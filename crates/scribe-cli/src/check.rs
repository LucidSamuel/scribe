//! D3 — `scribe check`: the fast tier that never requires an API key.
//!
//! Nobody should wait twenty minutes and spend API budget to discover a typo.
//! `check` runs the free half of the pipeline — extraction, schema validation,
//! fingerprint cache, spec elaboration — and reports honestly what it did NOT
//! establish. Exit codes follow the `judge` convention exactly:
//!
//!   0 = SOUND        (a kernel-checked proof is on file for this fingerprint)
//!   1 = UNDETERMINED (static checks pass; no kernel evidence — run `judge`)
//!   2 = UNSOUND      (a kernel-checked counterexample is on file)
//!   3 = input / infrastructure error (including any failing static check)
//!
//! Note the honesty rule baked into the codes: static checks alone never earn
//! exit 0. An exit 0 from `check` always means kernel-checked evidence exists.

use std::path::{Path, PathBuf};
use std::process;

use circuit_ir::CircuitIR;
use scribe_frontend::Frontend;

use crate::cache;
use crate::check_cmd::CheckArgs;
use crate::verdict;

const EXIT_SOUND: i32 = 0;
const EXIT_UNDETERMINED: i32 = 1;
const EXIT_UNSOUND: i32 = 2;
const EXIT_INFRA: i32 = 3;

/// The committed v1 schema, embedded at build time so `check` works from any
/// working directory.
const SCHEMA_JSON: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../schema/circuit-ir-v1.json"
));

/// The audit commands a committed artifact can carry. `#audit_axioms` is the
/// proof-soundness gate; the others are the C1–C3 statement audits.
const AUDIT_COMMANDS: [&str; 5] = [
    "#audit_axioms",
    "#audit_uses",
    "#audit_requires",
    "#audit_falsifiable",
    "#audit_satisfiable",
];

pub fn run_check(args: CheckArgs) {
    let started = std::time::Instant::now();

    // ── 1. Extraction ────────────────────────────────────────────────────────
    let ir = match load_ir(&args.gadget) {
        Ok(ir) => ir,
        Err(e) => {
            step('✗', "extraction", &e);
            fail_static();
        }
    };
    step(
        '✓',
        "extraction",
        &format!(
            "{} — {} public + {} private variable(s), {} constraint(s), {} definition(s) \
             (frontend: {})",
            ir.name,
            ir.public.len(),
            ir.private.len(),
            ir.constraints.len(),
            ir.definitions.len(),
            if ir.provenance.frontend.is_empty() {
                "unknown"
            } else {
                &ir.provenance.frontend
            },
        ),
    );

    // ── 2. Schema ────────────────────────────────────────────────────────────
    let errors = schema_errors(&ir);
    if !errors.is_empty() {
        step(
            '✗',
            "schema",
            &format!("circuit-ir-v1: {} violation(s)", errors.len()),
        );
        for e in errors.iter().take(5) {
            eprintln!("      {e}");
        }
        fail_static();
    }
    step('✓', "schema", "valid against circuit-ir-v1");

    // ── 3. Fingerprint cache ─────────────────────────────────────────────────
    let fp = cache::fingerprint(&ir);
    let cache_dir = cache::default_dir();
    let lake_dir = crate::orchestrate::resolve_lake_dir(args.lake_dir.as_deref());

    // `--record`: kernel-check that a Lean artifact proves THIS circuit's
    // regenerated statement (binding probe + #audit_axioms + C1), then record
    // it as the SOUND evidence for this fingerprint. Free of models, not of
    // rigor.
    if let Some(ref artifact) = args.record {
        record_artifact(&args, &ir, &cache_dir, artifact);
        // fall through to the normal cache path, which will now hit
    }

    if !args.no_cache {
        if let Some(rec) = cache::lookup(&cache_dir, &fp) {
            match cache::verify_hit(&rec, &lake_dir) {
                Ok(()) => {
                    step(
                        '✓',
                        "proof cache",
                        &format!(
                            "HIT {} → {} (kernel-checked, recorded by {})",
                            cache::short(&fp),
                            rec.artifact,
                            rec.recorded_by
                        ),
                    );
                    render_recorded_audits(&rec.audits);
                    eprintln!(
                        "[scribe check] done in {:.2}s (no model, no elaboration needed)",
                        started.elapsed().as_secs_f64()
                    );
                    match rec.verdict {
                        cache::CachedVerdict::Sound => {
                            println!("SOUND: {}", rec.artifact);
                            println!(
                                "{}",
                                verdict::accept_line(&format!(
                                    "kernel-accepted proof at {} (cache hit {})",
                                    rec.artifact,
                                    cache::short(&fp)
                                ))
                            );
                            process::exit(EXIT_SOUND);
                        }
                        cache::CachedVerdict::Unsound => {
                            println!("UNSOUND: {}", rec.artifact);
                            println!(
                                "{}",
                                verdict::reject_line(&format!(
                                    "kernel-checked counterexample at {} (cache hit {})",
                                    rec.artifact,
                                    cache::short(&fp)
                                ))
                            );
                            process::exit(EXIT_UNSOUND);
                        }
                    }
                }
                Err(why) => {
                    step('–', "proof cache", &format!("record ignored: {why}"));
                }
            }
        } else {
            step(
                '–',
                "proof cache",
                &format!("MISS {} (no kernel evidence on file)", cache::short(&fp)),
            );
        }
    } else {
        step('–', "proof cache", "skipped (--no-cache)");
    }

    // ── 4. Spec elaboration ──────────────────────────────────────────────────
    if args.no_elab {
        step('–', "spec elaborates", "skipped (--no-elab)");
    } else {
        match elaborate_scaffold(&ir, &lake_dir) {
            Ok(()) => step(
                '✓',
                "spec elaborates",
                &format!(
                    "theorem statement is valid Lean ({})",
                    ir.soundness_spec.as_deref().unwrap_or("True")
                ),
            ),
            Err(e) => {
                step('✗', "spec elaborates", &e);
                fail_static();
            }
        }
    }

    // ── 5. Honest close: nothing kernel-checked happened here ────────────────
    step(
        '–',
        "audits C1–C3",
        "need a finished proof to audit — `scribe judge` (or `check --record`) \
         runs them and caches the outcome",
    );
    eprintln!(
        "[scribe check] done in {:.2}s (no API key used)",
        started.elapsed().as_secs_f64()
    );
    println!("UNDETERMINED: {}", args.gadget);
    println!(
        "{}",
        verdict::undetermined_line(&format!(
            "static checks pass; no kernel evidence for fingerprint {} — run `scribe judge`",
            cache::short(&fp)
        ))
    );
    process::exit(EXIT_UNDETERMINED);
}

fn step(mark: char, label: &str, detail: &str) {
    eprintln!("  {mark} {label:<16} {detail}");
}

fn fail_static() -> ! {
    eprintln!("[scribe check] FAILED — fix the input above; no API budget was spent finding this");
    process::exit(EXIT_INFRA);
}

/// Load a circuit: `.json` is the CircuitIR interchange format (ir_version
/// enforced at parse time), anything else is gadget TOML via the frontend.
///
/// `check` and `judge` MUST share this loader: the fingerprint covers
/// provenance (minus `source_rev`), so two commands that stamp provenance
/// differently would compute different fingerprints for the same circuit and
/// the cache would silently never hit across them.
pub(crate) fn load_ir(path: &str) -> Result<CircuitIR, String> {
    if Path::new(path).extension().is_some_and(|e| e == "json") {
        let text = std::fs::read_to_string(path).map_err(|e| format!("cannot read {path}: {e}"))?;
        // Validate the RAW document against the schema BEFORE serde touches
        // it. Serde normalizes as it deserializes — a missing ir_version
        // becomes "1" via the field default, and unknown or misspelled
        // properties are silently discarded — so validating a reserialized
        // value can never catch those. The raw document is what the schema's
        // `required` and `additionalProperties: false` exist to check.
        let raw: serde_json::Value =
            serde_json::from_str(&text).map_err(|e| format!("{path} is not JSON: {e}"))?;
        let errors: Vec<String> = schema_validator()
            .iter_errors(&raw)
            .map(|e| format!("{} (at {})", e, e.instance_path))
            .collect();
        if !errors.is_empty() {
            return Err(format!(
                "{path} fails circuit-ir-v1 schema validation:\n      {}",
                errors.join("\n      ")
            ));
        }
        CircuitIR::from_json(&text).map_err(|e| e.to_string())
    } else {
        // Canonicalize so `examples/x.toml` and `./examples/x.toml` stamp the
        // same provenance.source and therefore the same fingerprint. The
        // cache is per-checkout (target/), so an absolute path is fine.
        let p = PathBuf::from(path);
        let canon = p.canonicalize().unwrap_or(p);
        frontend_toml::TomlFrontend
            .extract(&canon)
            .map_err(|e| e.to_string())
    }
}

fn schema_validator() -> jsonschema::Validator {
    let schema: serde_json::Value =
        serde_json::from_str(SCHEMA_JSON).expect("embedded schema is valid JSON");
    jsonschema::validator_for(&schema).expect("embedded schema compiles")
}

/// Validate the IR's canonical JSON against the embedded v1 schema.
///
/// For `.json` inputs this is the second layer — the raw document was already
/// validated in `load_ir` before deserialization. For TOML inputs (which have
/// no raw JSON form) it is the only layer.
fn schema_errors(ir: &CircuitIR) -> Vec<String> {
    let value: serde_json::Value =
        serde_json::from_str(&ir.to_json().expect("CircuitIR serializes"))
            .expect("serialized IR is valid JSON");
    schema_validator()
        .iter_errors(&value)
        .map(|e| format!("{} (at {})", e, e.instance_path))
        .collect()
}

/// Write the sorry-scaffold (audit gate stripped) into the lake project and
/// elaborate it with `lake env lean`. A `sorry` warning is fine — an error in
/// the *statement* (bad spec syntax, unknown identifier, type mismatch) is
/// exactly the typo this tier exists to catch in seconds.
fn elaborate_scaffold(ir: &CircuitIR, lake_dir: &str) -> Result<(), String> {
    let scaffold = lean_emit::emit_lean(ir).map_err(|e| format!("cannot emit scaffold: {e}"))?;
    let probe = strip_audit_gates(&scaffold);
    run_probe(lake_dir, &format!("Check{}", sanitize(&ir.name)), &probe).map_err(|tail| {
        format!(
            "the theorem statement does not elaborate — this is a typo-tier failure \
             in the spec or IR, not a proof failure:\n      {tail}"
        )
    })
}

/// Render what was actually audited at record time. Facts about runs, not
/// scans: `axioms_ok`/`uses_ok` come from kernel-checked probes, and
/// `artifact_audits` lists the commands the artifact itself executed during
/// its green build.
fn render_recorded_audits(audits: &cache::AuditReport) {
    let mut ran: Vec<String> = Vec::new();
    if audits.axioms_ok {
        ran.push("#audit_axioms (binding probe)".to_string());
    }
    match audits.uses_ok {
        Some(true) => ran.push("#audit_uses (C1)".to_string()),
        Some(false) => ran.push("#audit_uses (C1) FAILED — decorative hypotheses".to_string()),
        None => {}
    }
    step(
        if audits.uses_ok == Some(false) {
            '–'
        } else {
            '✓'
        },
        "audits run",
        &format!("{} at record time", ran.join(", ")),
    );
    if audits.artifact_audits.is_empty() {
        step(
            '–',
            "artifact audits",
            "artifact declares no #audit_* commands of its own",
        );
    } else {
        step(
            '✓',
            "artifact audits",
            &format!(
                "{} executed during the artifact's green build",
                audits.artifact_audits.join(", ")
            ),
        );
    }
}

/// What an artifact is being bound to prove.
pub(crate) enum BindTarget {
    /// The soundness theorem regenerated from the IR.
    Soundness,
    /// The refutation theorem at `prime` regenerated from the IR.
    Refutation { prime: u64 },
}

/// Kernel-check that `artifact` proves EXACTLY the statement the current IR
/// regenerates, and audit it. This is the binding a cache record stands on —
/// "builds green and mentions #audit_axioms somewhere" is not evidence that
/// the artifact has anything to do with this circuit.
///
/// Three kernel-checked facts, or an error:
/// 1. the artifact lake-builds green (which also *runs* every `#audit_*`
///    command the artifact declares);
/// 2. a binding probe `example : <regenerated statement> := @<theorem>`
///    elaborates — the declaration exists and its type is definitionally the
///    regenerated statement;
/// 3. `#audit_axioms <theorem>` passes in the probe (trusted axioms only),
///    independent of whatever gates the artifact itself carries.
///
/// For soundness targets, C1 (`#audit_uses`) then runs in its own probe; its
/// outcome is reported, not gating (unused hypotheses are a smell, not
/// unsoundness).
pub(crate) fn bind_and_audit(
    ir: &CircuitIR,
    artifact: &str,
    lake_dir: &str,
    target: BindTarget,
) -> Result<cache::AuditReport, String> {
    let module = artifact_module(artifact, lake_dir)?;

    // 1. Build the artifact's MODULE green. This type-checks it with the
    //    kernel, executes every `#audit_*` command it declares, and produces
    //    the .olean the binding probe imports.
    let build = process::Command::new("lake")
        .args(["build", &module])
        .current_dir(lake_dir)
        .output()
        .map_err(|e| format!("cannot run `lake build {module}` in {lake_dir}: {e}"))?;
    if !build.status.success() {
        let stdout = String::from_utf8_lossy(&build.stdout);
        let stderr = String::from_utf8_lossy(&build.stderr);
        let tail: String = stdout
            .lines()
            .chain(stderr.lines())
            .filter(|l| !l.trim().is_empty())
            .take(6)
            .collect::<Vec<_>>()
            .join("\n      ");
        return Err(format!(
            "{artifact} does not build green — refusing to record it as evidence:\n      {tail}"
        ));
    }
    let (name, ty) = match target {
        BindTarget::Soundness => lean_emit::soundness_statement(ir).map_err(|e| e.to_string())?,
        BindTarget::Refutation { prime } => {
            lean_emit::refutation_statement(ir, prime).map_err(|e| e.to_string())?
        }
    };

    // 2 + 3. Binding + axiom audit in one kernel-checked probe.
    let bind_probe = format!(
        "import ZkGadgets.Audit\nimport {module}\n\n\
         /-- Binding probe: `{name}` in {module} must prove exactly the statement\n\
         regenerated from the current circuit IR — auto-generated, do not edit. -/\n\
         example :\n    {ty} := @{name}\n\n\
         #audit_axioms {name}\n"
    );
    run_probe(
        lake_dir,
        &format!("BindProbe{}", sanitize(&ir.name)),
        &bind_probe,
    )
    .map_err(|out| {
        format!(
            "{artifact} does NOT prove this circuit's statement (declaration `{name}` \
                 missing, wrong type, or axiom-tainted):\n      {out}"
        )
    })?;

    // C1: hypothesis liveness, reported but not gating.
    let uses_ok = match target {
        BindTarget::Soundness => {
            let uses_probe =
                format!("import ZkGadgets.Audit\nimport {module}\n\n#audit_uses {name}\n");
            Some(
                run_probe(
                    lake_dir,
                    &format!("UsesProbe{}", sanitize(&ir.name)),
                    &uses_probe,
                )
                .is_ok(),
            )
        }
        BindTarget::Refutation { .. } => None,
    };

    Ok(cache::AuditReport {
        axioms_ok: true, // the bind probe just gated on it
        uses_ok,
        artifact_audits: audit_gates_in(&std::fs::read_to_string(artifact).unwrap_or_default()),
    })
}

/// Write a probe file into the lake project's Bench scratch dir, elaborate it
/// with `lake env lean`, clean up, and return the output tail on failure.
fn run_probe(lake_dir: &str, stem: &str, contents: &str) -> Result<(), String> {
    let rel = format!("ZkGadgets/Bench/{stem}.lean");
    let abs = Path::new(lake_dir).join(&rel);
    if let Some(parent) = abs.parent() {
        std::fs::create_dir_all(parent).map_err(|e| format!("cannot create {parent:?}: {e}"))?;
    }
    std::fs::write(&abs, contents).map_err(|e| format!("cannot write probe {abs:?}: {e}"))?;
    let output = process::Command::new("lake")
        .args(["env", "lean", &rel])
        .current_dir(lake_dir)
        .output();
    let _ = std::fs::remove_file(&abs);
    let output = output.map_err(|e| format!("cannot run `lake env lean` in {lake_dir}: {e}"))?;
    if output.status.success() {
        Ok(())
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        Err(stdout
            .lines()
            .chain(stderr.lines())
            .filter(|l| !l.trim().is_empty())
            .take(8)
            .collect::<Vec<_>>()
            .join("\n      "))
    }
}

/// The Lean module name of an artifact inside the lake project
/// (`lean/ZkGadgets/RangeCheck.lean` → `ZkGadgets.RangeCheck`).
fn artifact_module(artifact: &str, lake_dir: &str) -> Result<String, String> {
    let art = Path::new(artifact)
        .canonicalize()
        .map_err(|e| format!("cannot resolve {artifact}: {e}"))?;
    let lake = Path::new(lake_dir)
        .canonicalize()
        .map_err(|e| format!("cannot resolve lake dir {lake_dir}: {e}"))?;
    let rel = art.strip_prefix(&lake).map_err(|_| {
        format!(
            "{artifact} is outside the lake project {lake_dir} — the binding probe must be \
             able to import it"
        )
    })?;
    let no_ext = rel.with_extension("");
    let module: Vec<String> = no_ext
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect();
    if module.is_empty() {
        return Err(format!("{artifact} has no module path inside {lake_dir}"));
    }
    Ok(module.join("."))
}

fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

/// Verify a Lean artifact against the CURRENT circuit (binding probe + axiom
/// audit + C1) and record it as SOUND evidence for this fingerprint.
fn record_artifact(args: &CheckArgs, ir: &CircuitIR, cache_dir: &Path, artifact: &str) {
    let lake_dir = crate::orchestrate::resolve_lake_dir(args.lake_dir.as_deref());
    let audits = match bind_and_audit(ir, artifact, &lake_dir, BindTarget::Soundness) {
        Ok(a) => a,
        Err(e) => {
            step('✗', "record", &e);
            fail_static();
        }
    };

    match cache::record_verdict(
        cache_dir,
        ir,
        cache::CachedVerdict::Sound,
        artifact,
        "check --record",
        &lake_dir,
        None,
        audits,
    ) {
        Ok(_) => step(
            '✓',
            "record",
            &format!(
                "{artifact} bound to this circuit (kernel-checked statement match, \
                 #audit_axioms clean) and recorded for {}",
                cache::short(&cache::fingerprint(ir))
            ),
        ),
        Err(e) => {
            step('✗', "record", &format!("could not write cache record: {e}"));
            fail_static();
        }
    }
}

/// Remove `#audit_axioms` gate lines from a scaffold so the probe elaborates
/// (with a `sorry` warning) instead of failing on the intentionally-red gate.
fn strip_audit_gates(lean: &str) -> String {
    lean.lines()
        .filter(|l| !l.trim_start().starts_with("#audit_axioms"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Which audit commands a Lean artifact executes: line-anchored, so a command
/// buried in prose or a line comment does not count. Callers only invoke this
/// on files that lake-built green, which is what makes "declares" mean "ran
/// and passed".
fn audit_gates_in(text: &str) -> Vec<String> {
    AUDIT_COMMANDS
        .into_iter()
        .filter(|cmd| text.lines().any(|l| l.trim_start().starts_with(cmd)))
        .map(str::to_string)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn examples_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("examples")
    }

    #[test]
    fn load_ir_reads_toml_and_stamps_frontend() {
        let ir = load_ir(
            examples_dir()
                .join("range-check/gadget.toml")
                .to_str()
                .unwrap(),
        )
        .unwrap();
        assert_eq!(ir.name, "range-check-8bit");
        assert_eq!(ir.provenance.frontend, "toml");
    }

    #[test]
    fn fingerprint_is_stable_across_path_spellings() {
        // `judge` and `check` share load_ir, and load_ir canonicalizes: the
        // same file reached via different spellings must fingerprint the same,
        // or the cache silently never hits.
        let dir = examples_dir().join("range-check");
        let plain = dir.join("gadget.toml");
        let dotted = dir.join(".").join("gadget.toml");
        let a = crate::cache::fingerprint(&load_ir(plain.to_str().unwrap()).unwrap());
        let b = crate::cache::fingerprint(&load_ir(dotted.to_str().unwrap()).unwrap());
        assert_eq!(a, b);
    }

    #[test]
    fn load_ir_reads_json_and_enforces_version() {
        let dir = std::env::temp_dir().join(format!("scribe-check-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();

        let ir = load_ir(
            examples_dir()
                .join("range-check/gadget.toml")
                .to_str()
                .unwrap(),
        )
        .unwrap();
        let good = dir.join("good.json");
        std::fs::write(&good, ir.to_json().unwrap()).unwrap();
        assert!(load_ir(good.to_str().unwrap()).is_ok());

        let mut bad_ir = ir.clone();
        bad_ir.ir_version = "2".into();
        let bad = dir.join("bad.json");
        std::fs::write(&bad, bad_ir.to_json().unwrap()).unwrap();
        let err = load_ir(bad.to_str().unwrap()).unwrap_err();
        // the raw schema layer rejects the unknown major before serde ever
        // runs; circuit-ir's own from_json gate backstops it (tested there)
        assert!(err.contains("ir_version"), "{err}");

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn schema_errors_empty_for_examples_and_real_for_broken_ir() {
        let ir = load_ir(
            examples_dir()
                .join("poseidon-sbox/gadget.toml")
                .to_str()
                .unwrap(),
        )
        .unwrap();
        assert!(schema_errors(&ir).is_empty());

        let mut broken = ir;
        broken.constraints[0].origin = Some(circuit_ir::SourceSpan {
            file: "x.rs".into(),
            line: 0, // schema minimum is 1
            label: None,
        });
        assert!(!schema_errors(&broken).is_empty());
    }

    #[test]
    fn strip_audit_gates_removes_only_gate_lines() {
        let ir = load_ir(
            examples_dir()
                .join("range-check/gadget.toml")
                .to_str()
                .unwrap(),
        )
        .unwrap();
        let scaffold = lean_emit::emit_lean(&ir).unwrap();
        assert!(scaffold.contains("#audit_axioms"));
        let probe = strip_audit_gates(&scaffold);
        assert!(!probe.contains("#audit_axioms"));
        // everything else survives
        assert!(probe.contains("theorem range_check_8bit_sound"));
        assert!(probe.contains("sorry"));
    }

    #[test]
    fn audit_gates_in_is_line_anchored() {
        let text = "theorem t : True := trivial\n#audit_axioms t\n  #audit_falsifiable t (p := 5)";
        assert_eq!(
            audit_gates_in(text),
            vec!["#audit_axioms", "#audit_falsifiable"]
        );
        assert!(audit_gates_in("no gates here").is_empty());
        // prose or comments mentioning a command are not a command
        assert!(audit_gates_in("-- remember to add #audit_axioms t").is_empty());
        assert!(audit_gates_in("/- #audit_uses would go here -/").is_empty());
    }

    #[test]
    fn raw_json_missing_ir_version_is_rejected() {
        // Serde would silently default ir_version to "1"; the raw-document
        // schema validation must catch the omission first.
        let dir = std::env::temp_dir().join(format!("scribe-check-raw-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let doc = serde_json::json!({
            "name": "t", "modulus": "17",
            "private": [{"id": 0, "name": "x"}],
            "constraints": [{"label": "c", "terms": [{"coeff": "1", "vars": [0]}]}],
        });
        let p = dir.join("no-version.json");
        std::fs::write(&p, serde_json::to_string(&doc).unwrap()).unwrap();
        let err = load_ir(p.to_str().unwrap()).unwrap_err();
        assert!(err.contains("ir_version"), "{err}");
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn raw_json_unknown_property_is_rejected() {
        // Serde silently discards unknown fields — a misspelled
        // `soundness_specc` would otherwise vanish and the circuit would be
        // checked WITHOUT its spec.
        let dir = std::env::temp_dir().join(format!("scribe-check-raw2-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let doc = serde_json::json!({
            "ir_version": "1", "name": "t", "modulus": "17",
            "soundness_specc": "x = 0",
            "private": [{"id": 0, "name": "x"}],
            "constraints": [{"label": "c", "terms": [{"coeff": "1", "vars": [0]}]}],
        });
        let p = dir.join("misspelled.json");
        std::fs::write(&p, serde_json::to_string(&doc).unwrap()).unwrap();
        let err = load_ir(p.to_str().unwrap()).unwrap_err();
        assert!(err.contains("soundness_specc"), "{err}");
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn artifact_module_maps_paths_and_rejects_outsiders() {
        let dir = std::env::temp_dir().join(format!("scribe-check-mod-{}", std::process::id()));
        let lake = dir.join("lean");
        std::fs::create_dir_all(lake.join("ZkGadgets/Bench")).unwrap();
        let inside = lake.join("ZkGadgets/RangeCheck.lean");
        std::fs::write(&inside, "-- proof").unwrap();
        assert_eq!(
            artifact_module(inside.to_str().unwrap(), lake.to_str().unwrap()).unwrap(),
            "ZkGadgets.RangeCheck"
        );
        let outside = dir.join("Elsewhere.lean");
        std::fs::write(&outside, "-- not importable").unwrap();
        let err = artifact_module(outside.to_str().unwrap(), lake.to_str().unwrap()).unwrap_err();
        assert!(err.contains("outside the lake project"));
        std::fs::remove_dir_all(&dir).ok();
    }
}
