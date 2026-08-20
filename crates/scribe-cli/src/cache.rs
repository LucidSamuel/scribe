//! D4 — fingerprint caching: unchanged circuits cost nothing.
//!
//! The fingerprint is SHA-256 over the canonical JSON of the `CircuitIR` with
//! `provenance.source_rev` cleared. It therefore covers the constraint set,
//! the variables, the definitions, the hypotheses — and the spec, so editing
//! a spec invalidates the cache even when the circuit is untouched.
//!
//! The cache lives in `target/scribe/` and is only an *index*: the evidence
//! is the committed kernel-checked Lean artifact the record points at, and a
//! hit requires that artifact to still hash exactly as recorded. A cache
//! record whose artifact drifted is ignored, never trusted.

use std::io;
use std::path::{Path, PathBuf};

use circuit_ir::CircuitIR;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// SHA-256 hex of the canonical IR JSON, excluding `provenance.source_rev`
/// and every `Constraint.origin`.
///
/// Origins are diagnostic metadata (which source line a constraint came
/// from), not circuit semantics: they never reach the emitted Lean, so the
/// theorem, the proof, and the evidence are identical with or without them.
/// Including them would invalidate every cached verdict whenever a comment
/// edit shifts line numbers in a gadget file — cache churn with no semantic
/// change. The spec and the constraint set itself remain fully covered.
pub fn fingerprint(ir: &CircuitIR) -> String {
    // The canonicalization lives in circuit-ir so every consumer (this
    // cache, corpus content fingerprints) agrees on it by construction.
    ir.semantic_fingerprint()
}

/// SHA-256 hex of a file's contents.
pub fn file_sha256(path: &Path) -> io::Result<String> {
    Ok(hex(&Sha256::digest(std::fs::read(path)?)))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Short display form of a fingerprint for terminal output.
pub fn short(fp: &str) -> &str {
    &fp[..fp.len().min(12)]
}

/// What the kernel established for a fingerprint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CachedVerdict {
    /// A kernel-accepted proof of the soundness spec exists.
    Sound,
    /// A kernel-checked counterexample to the soundness spec exists.
    Unsound,
}

/// What was actually audited when this record was created. Facts about runs
/// that happened, not scans of what might have.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditReport {
    /// `#audit_axioms` passed on the bound declaration in the binding probe
    /// (kernel-run at record time). Recording refuses to proceed without it,
    /// so this is `true` in every stored record — kept explicit so the
    /// rendering never has to assume.
    pub axioms_ok: bool,
    /// C1 (`#audit_uses`) outcome from its own probe; `None` when it was not
    /// run (refutation artifacts have no hypotheses to audit).
    pub uses_ok: Option<bool>,
    /// `#audit_*` commands the artifact itself executes — line-anchored scan
    /// of a file that lake-built green at record time, so these commands ran
    /// and passed during that build.
    pub artifact_audits: Vec<String>,
}

/// One cache entry: fingerprint → committed kernel-checked artifact.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheRecord {
    pub fingerprint: String,
    pub circuit_name: String,
    pub verdict: CachedVerdict,
    /// Path to the committed Lean artifact (proof or refutation).
    pub artifact: String,
    /// SHA-256 of the artifact at record time.
    pub artifact_sha256: String,
    /// Fingerprint of the proof environment (toolchain, manifest, Lean
    /// library sources) at record time. A kernel verdict is only as good as
    /// the environment that checked it.
    pub env_fingerprint: String,
    /// Probe prime, for refutation artifacts.
    pub prime: Option<u64>,
    /// What was audited at record time.
    pub audits: AuditReport,
    /// What created the record (`judge`, `check --record`).
    pub recorded_by: String,
}

/// Cache directory: `$SCRIBE_CACHE_DIR`, else `target/scribe/cache`.
pub fn default_dir() -> PathBuf {
    match std::env::var("SCRIBE_CACHE_DIR") {
        Ok(dir) => PathBuf::from(dir),
        Err(_) => Path::new("target").join("scribe").join("cache"),
    }
}

fn record_path(dir: &Path, fp: &str) -> PathBuf {
    dir.join(format!("{fp}.json"))
}

/// Persist a record under its fingerprint.
pub fn store(dir: &Path, record: &CacheRecord) -> io::Result<PathBuf> {
    std::fs::create_dir_all(dir)?;
    let path = record_path(dir, &record.fingerprint);
    let json = serde_json::to_string_pretty(record).expect("record serializes");
    std::fs::write(&path, json)?;
    Ok(path)
}

/// Read a record. Missing or corrupt files are simply misses.
pub fn lookup(dir: &Path, fp: &str) -> Option<CacheRecord> {
    let text = std::fs::read_to_string(record_path(dir, fp)).ok()?;
    serde_json::from_str(&text).ok()
}

/// Fingerprint of the proof environment: `lean-toolchain`,
/// `lake-manifest.json`, and every committed `.lean` source under the lake
/// project (excluding generated `Bench/` scratch files). A cached verdict is
/// invalid the moment any of these change — a different Mathlib revision or
/// an edited `Audit.lean` re-opens the question the kernel answered.
pub fn environment_fingerprint(lake_dir: &str) -> io::Result<String> {
    let lake = Path::new(lake_dir);
    let mut entries: Vec<(String, Vec<u8>)> = Vec::new();

    for meta in ["lean-toolchain", "lake-manifest.json"] {
        let p = lake.join(meta);
        if let Ok(bytes) = std::fs::read(&p) {
            entries.push((meta.to_string(), bytes));
        }
    }

    let mut lean_files: Vec<PathBuf> = Vec::new();
    collect_lean_sources(lake, &mut lean_files)?;
    for p in lean_files {
        let rel = p
            .strip_prefix(lake)
            .unwrap_or(&p)
            .to_string_lossy()
            .into_owned();
        let bytes = std::fs::read(&p)?;
        entries.push((rel, bytes));
    }

    entries.sort_by(|a, b| a.0.cmp(&b.0));
    let mut hasher = Sha256::new();
    for (name, bytes) in &entries {
        hasher.update(name.as_bytes());
        hasher.update([0u8]);
        hasher.update(bytes);
        hasher.update([0u8]);
    }
    Ok(hex(&hasher.finalize()))
}

fn collect_lean_sources(dir: &Path, out: &mut Vec<PathBuf>) -> io::Result<()> {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Ok(());
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if path.is_dir() {
            // Bench/ holds per-run generated scaffolds and probes; .lake and
            // lakefile caches are build products, not proof sources.
            if name == "Bench" || name.starts_with('.') {
                continue;
            }
            collect_lean_sources(&path, out)?;
        } else if path.extension().is_some_and(|e| e == "lean") {
            out.push(path);
        }
    }
    Ok(())
}

/// Full hit verification: the artifact must hash as recorded AND the proof
/// environment must match record time.
pub fn verify_hit(record: &CacheRecord, lake_dir: &str) -> Result<(), String> {
    verify_artifact(record)?;
    let env = environment_fingerprint(lake_dir)
        .map_err(|e| format!("cannot fingerprint the proof environment: {e}"))?;
    if env != record.env_fingerprint {
        return Err(
            "the proof environment (toolchain / Mathlib / Lean sources) changed since this \
             verdict was recorded — re-judge or re-record to refresh the evidence"
                .to_string(),
        );
    }
    Ok(())
}

/// A hit is only a hit while the evidence stands: the artifact must exist and
/// hash exactly as recorded.
pub fn verify_artifact(record: &CacheRecord) -> Result<(), String> {
    let actual = file_sha256(Path::new(&record.artifact)).map_err(|e| {
        format!(
            "artifact {} is unreadable ({e}) — the evidence is gone, ignoring the cache record",
            record.artifact
        )
    })?;
    if actual != record.artifact_sha256 {
        return Err(format!(
            "artifact {} changed since it was recorded — re-judge to refresh the evidence",
            record.artifact
        ));
    }
    Ok(())
}

/// Convenience: record a verdict for `ir`'s fingerprint, hashing the artifact
/// and the proof environment now. Callers must have bound the artifact to the
/// IR first (binding probe) — this function records evidence, it does not
/// create it.
#[allow(clippy::too_many_arguments)]
pub fn record_verdict(
    dir: &Path,
    ir: &CircuitIR,
    verdict: CachedVerdict,
    artifact: &str,
    recorded_by: &str,
    lake_dir: &str,
    prime: Option<u64>,
    audits: AuditReport,
) -> io::Result<PathBuf> {
    let record = CacheRecord {
        fingerprint: fingerprint(ir),
        circuit_name: ir.name.clone(),
        verdict,
        artifact: artifact.to_string(),
        artifact_sha256: file_sha256(Path::new(artifact))?,
        env_fingerprint: environment_fingerprint(lake_dir)?,
        prime,
        audits,
        recorded_by: recorded_by.to_string(),
    };
    store(dir, &record)
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit_ir::{Constraint, Provenance, Term, Variable};

    fn ir() -> CircuitIR {
        CircuitIR {
            name: "t".into(),
            modulus: "17".into(),
            provenance: Provenance {
                frontend: "toml".into(),
                frontend_version: "0.1.0".into(),
                source: "t.toml".into(),
                source_rev: Some("rev-a".into()),
            },
            private: vec![Variable {
                id: 0,
                name: "x".into(),
            }],
            constraints: vec![Constraint {
                label: "c".into(),
                terms: vec![Term {
                    coeff: "1".into(),
                    vars: vec![0],
                }],
                origin: None,
            }],
            soundness_spec: Some("x = 0".into()),
            ..Default::default()
        }
    }

    fn tmp() -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "scribe-cache-test-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn fingerprint_is_stable_and_excludes_source_rev() {
        let a = ir();
        let mut b = ir();
        assert_eq!(fingerprint(&a), fingerprint(&b));
        // source_rev must not participate — same circuit at another commit
        b.provenance.source_rev = Some("rev-b".into());
        assert_eq!(fingerprint(&a), fingerprint(&b));
        b.provenance.source_rev = None;
        assert_eq!(fingerprint(&a), fingerprint(&b));
    }

    #[test]
    fn spec_edit_invalidates() {
        let a = ir();
        let mut b = ir();
        b.soundness_spec = Some("x = 1".into());
        assert_ne!(
            fingerprint(&a),
            fingerprint(&b),
            "a spec edit with an unchanged circuit MUST invalidate the cache"
        );
    }

    #[test]
    fn constraint_edit_invalidates() {
        let a = ir();
        let mut b = ir();
        b.constraints[0].terms[0].coeff = "2".into();
        assert_ne!(fingerprint(&a), fingerprint(&b));
    }

    #[test]
    fn origin_spans_do_not_participate() {
        // Origins are diagnostics, not semantics: a comment edit shifting a
        // gadget's line numbers must not invalidate its cached verdict.
        let a = ir();
        let mut b = ir();
        b.constraints[0].origin = Some(circuit_ir::SourceSpan {
            file: "boolean.rs".into(),
            line: 61,
            label: None,
        });
        assert_eq!(fingerprint(&a), fingerprint(&b));
    }

    fn audits() -> AuditReport {
        AuditReport {
            axioms_ok: true,
            uses_ok: Some(true),
            artifact_audits: vec!["#audit_axioms".into()],
        }
    }

    /// A minimal fake lake project the environment fingerprint can hash.
    fn fake_lake(dir: &Path) -> PathBuf {
        let lake = dir.join("lake");
        std::fs::create_dir_all(lake.join("ZkGadgets")).unwrap();
        std::fs::create_dir_all(lake.join("ZkGadgets/Bench")).unwrap();
        std::fs::write(lake.join("lean-toolchain"), "leanprover/lean4:v4.x").unwrap();
        std::fs::write(lake.join("lake-manifest.json"), "{\"mathlib\": \"rev-a\"}").unwrap();
        std::fs::write(lake.join("ZkGadgets/Audit.lean"), "-- audit commands").unwrap();
        lake
    }

    #[test]
    fn store_lookup_roundtrip_and_artifact_verification() {
        let dir = tmp();
        let lake = fake_lake(&dir);
        let artifact = dir.join("Proof.lean");
        std::fs::write(&artifact, "theorem t : True := trivial").unwrap();

        let path = record_verdict(
            &dir,
            &ir(),
            CachedVerdict::Sound,
            artifact.to_str().unwrap(),
            "test",
            lake.to_str().unwrap(),
            None,
            audits(),
        )
        .unwrap();
        assert!(path.exists());

        let rec = lookup(&dir, &fingerprint(&ir())).expect("hit");
        assert_eq!(rec.circuit_name, "t");
        assert_eq!(rec.verdict, CachedVerdict::Sound);
        assert!(rec.audits.axioms_ok);
        assert!(verify_hit(&rec, lake.to_str().unwrap()).is_ok());

        // evidence drift is detected, not trusted
        std::fs::write(&artifact, "theorem t : True := sorry").unwrap();
        let err = verify_artifact(&rec).unwrap_err();
        assert!(err.contains("changed since it was recorded"));

        // evidence removal too
        std::fs::remove_file(&artifact).unwrap();
        assert!(verify_artifact(&rec).unwrap_err().contains("unreadable"));

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn environment_change_invalidates_a_hit() {
        let dir = tmp();
        let lake = fake_lake(&dir);
        let artifact = dir.join("Proof.lean");
        std::fs::write(&artifact, "theorem t : True := trivial").unwrap();

        record_verdict(
            &dir,
            &ir(),
            CachedVerdict::Sound,
            artifact.to_str().unwrap(),
            "test",
            lake.to_str().unwrap(),
            None,
            audits(),
        )
        .unwrap();
        let rec = lookup(&dir, &fingerprint(&ir())).unwrap();
        assert!(verify_hit(&rec, lake.to_str().unwrap()).is_ok());

        // editing a library source (e.g. the audit definitions!) re-opens the
        // question — the artifact hash alone would not catch this
        std::fs::write(lake.join("ZkGadgets/Audit.lean"), "-- tampered").unwrap();
        let err = verify_hit(&rec, lake.to_str().unwrap()).unwrap_err();
        assert!(err.contains("proof environment"));

        // toolchain bump too
        std::fs::write(lake.join("ZkGadgets/Audit.lean"), "-- audit commands").unwrap();
        assert!(verify_hit(&rec, lake.to_str().unwrap()).is_ok());
        std::fs::write(lake.join("lean-toolchain"), "leanprover/lean4:v4.y").unwrap();
        assert!(verify_hit(&rec, lake.to_str().unwrap()).is_err());

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn environment_fingerprint_ignores_generated_bench_files() {
        let dir = tmp();
        let lake = fake_lake(&dir);
        let before = environment_fingerprint(lake.to_str().unwrap()).unwrap();
        // per-run scaffolds and probes must not churn the environment
        std::fs::write(lake.join("ZkGadgets/Bench/JudgeFoo.lean"), "scratch").unwrap();
        let after = environment_fingerprint(lake.to_str().unwrap()).unwrap();
        assert_eq!(before, after);
        // but a real library file does
        std::fs::write(
            lake.join("ZkGadgets/New.lean"),
            "theorem n : True := trivial",
        )
        .unwrap();
        assert_ne!(
            before,
            environment_fingerprint(lake.to_str().unwrap()).unwrap()
        );
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn corrupt_records_are_misses() {
        let dir = tmp();
        let fp = fingerprint(&ir());
        std::fs::write(dir.join(format!("{fp}.json")), "not json").unwrap();
        assert!(lookup(&dir, &fp).is_none());
        std::fs::remove_dir_all(&dir).ok();
    }
}
