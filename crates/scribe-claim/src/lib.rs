//! Portable claim metadata and local artifact integrity checks.
//! A seal attests to byte identity and structural validation, never theorem truth.
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Artifact {
    pub path: String,
    pub sha256: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Proposition {
    pub declaration: String,
    pub statement: String,
    pub artifact_id: String,
    /// Explicitly record the claimed trust boundary; sealing does not audit it.
    pub trust: Trust,
    pub axioms: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Trust {
    Kernel,
    NativeDecide,
    Unchecked,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Heuristic {
    pub id: String,
    pub scope: String,
    pub evidence: Vec<String>,
    pub limitations: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CostEntry {
    pub id: String,
    /// Decimal string: preserve exact integers/rationals without float rounding.
    pub quantity: String,
    pub unit: String,
    pub scope: String,
    pub evidence: Vec<String>,
    pub extrapolation: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClaimPackage {
    pub schema_version: u32,
    pub claim_id: String,
    pub source_revision: String,
    pub toolchain: String,
    pub parameters: BTreeMap<String, String>,
    /// Includes target profile, dependencies, proof sources, logs, and measurements.
    pub artifacts: BTreeMap<String, Artifact>,
    pub propositions: Vec<Proposition>,
    pub heuristics: Vec<Heuristic>,
    pub cost_ledger: Vec<CostEntry>,
}

/// Cannot be deserialized or constructed by callers without validation.
#[derive(Debug, Serialize)]
pub struct SealedPackage {
    package: ClaimPackage,
    package_sha256: String,
}

pub fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn required(value: &str, label: &str) -> Result<(), String> {
    if value.trim().is_empty() {
        Err(format!("{label} must not be empty"))
    } else {
        Ok(())
    }
}

fn evidence(ids: &[String], artifacts: &BTreeMap<String, Artifact>) -> Result<(), String> {
    if ids.is_empty() {
        return Err("evidence must not be empty".into());
    }
    for id in ids {
        if !artifacts.contains_key(id) {
            return Err(format!("unknown evidence artifact: {id}"));
        }
    }
    Ok(())
}

fn exact_quantity(s: &str) -> bool {
    let parts: Vec<_> = s.split('/').collect();
    (parts.len() == 1 || parts.len() == 2)
        && parts
            .iter()
            .all(|p| !p.is_empty() && p.bytes().all(|b| b.is_ascii_digit()))
        && (parts.len() == 1 || parts[1].bytes().any(|b| b != b'0'))
}

impl ClaimPackage {
    /// Validate metadata and re-hash every artifact beneath root, rejecting escapes.
    /// This does not run Lean, execute candidates, or establish a cost bound.
    pub fn seal(self, root: &Path) -> Result<SealedPackage, String> {
        if self.schema_version != 1 {
            return Err("unsupported schema_version".into());
        }
        required(&self.claim_id, "claim_id")?;
        if !matches!(self.source_revision.len(), 40 | 64)
            || !self.source_revision.bytes().all(|b| b.is_ascii_hexdigit())
        {
            return Err("source_revision must be a full Git object ID".into());
        }
        required(&self.toolchain, "toolchain")?;
        for (key, value) in &self.parameters {
            required(key, "parameter name")?;
            required(value, "parameter value")?;
        }
        if self.propositions.is_empty() {
            return Err("at least one proposition is required".into());
        }
        let root = fs::canonicalize(root).map_err(|e| e.to_string())?;
        for (id, artifact) in &self.artifacts {
            required(id, "artifact ID")?;
            let path = Path::new(&artifact.path);
            if artifact.path.is_empty()
                || !path.components().all(|c| matches!(c, Component::Normal(_)))
            {
                return Err(format!(
                    "artifact {id}: expected a relative path without traversal"
                ));
            }
            let resolved =
                fs::canonicalize(root.join(path)).map_err(|e| format!("artifact {id}: {e}"))?;
            if !resolved.starts_with(&root) {
                return Err(format!("artifact {id} escapes package root"));
            }
            let bytes = fs::read(&resolved).map_err(|e| format!("artifact {id}: {e}"))?;
            if sha256(&bytes) != artifact.sha256 {
                return Err(format!("artifact {id}: SHA-256 mismatch"));
            }
        }
        let mut declarations = BTreeSet::new();
        for p in &self.propositions {
            required(&p.declaration, "declaration")?;
            required(&p.statement, "statement")?;
            if !declarations.insert(&p.declaration) {
                return Err("duplicate declaration".into());
            }
            evidence(std::slice::from_ref(&p.artifact_id), &self.artifacts)?;
            for axiom in &p.axioms {
                required(axiom, "axiom")?;
            }
        }
        let mut ids = BTreeSet::new();
        for h in &self.heuristics {
            required(&h.id, "heuristic ID")?;
            if !ids.insert(&h.id) {
                return Err("duplicate heuristic ID".into());
            }
            required(&h.scope, "heuristic scope")?;
            required(&h.limitations, "heuristic limitations")?;
            evidence(&h.evidence, &self.artifacts)?;
        }
        let mut ids = BTreeSet::new();
        for c in &self.cost_ledger {
            required(&c.id, "cost ID")?;
            if !ids.insert(&c.id) {
                return Err("duplicate cost ID".into());
            }
            if !exact_quantity(&c.quantity) {
                return Err(format!(
                    "cost {}: expected unsigned integer or rational with nonzero denominator",
                    c.id
                ));
            }
            required(&c.unit, "cost unit")?;
            required(&c.scope, "cost scope")?;
            evidence(&c.evidence, &self.artifacts)?;
            if let Some(rule) = &c.extrapolation {
                required(rule, "extrapolation")?;
            }
        }
        let bytes = serde_json::to_vec(&self).map_err(|e| e.to_string())?;
        Ok(SealedPackage {
            package_sha256: sha256(&bytes),
            package: self,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct Fixture(std::path::PathBuf);
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    fn fixture() -> (Fixture, ClaimPackage) {
        let root = std::env::temp_dir().join(format!(
            "scribe-claim-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        fs::write(root.join("proof.lean"), b"example : True := by trivial\n").unwrap();
        let package = ClaimPackage {
            schema_version: 1,
            claim_id: "test".into(),
            source_revision: "a".repeat(40),
            toolchain: "lean test fixture".into(),
            parameters: BTreeMap::new(),
            artifacts: BTreeMap::from([(
                "proof".into(),
                Artifact {
                    path: "proof.lean".into(),
                    sha256: sha256(b"example : True := by trivial\n"),
                },
            )]),
            propositions: vec![Proposition {
                declaration: "fixture".into(),
                statement: "True".into(),
                artifact_id: "proof".into(),
                trust: Trust::Unchecked,
                axioms: vec![],
            }],
            heuristics: vec![Heuristic {
                id: "H1".into(),
                scope: "test only".into(),
                evidence: vec!["proof".into()],
                limitations: "not attack evidence".into(),
            }],
            cost_ledger: vec![CostEntry {
                id: "C1".into(),
                quantity: "1/2".into(),
                unit: "test operations".into(),
                scope: "fixture".into(),
                evidence: vec!["proof".into()],
                extrapolation: None,
            }],
        };
        (Fixture(root), package)
    }
    #[test]
    fn deterministic_roundtrip_and_metadata_binding() {
        let (root, p) = fixture();
        let roundtrip =
            serde_json::from_slice::<ClaimPackage>(&serde_json::to_vec(&p).unwrap()).unwrap();
        let a = p.clone().seal(&root.0).unwrap();
        let b = roundtrip.seal(&root.0).unwrap();
        assert_eq!(a.package_sha256, b.package_sha256);
        let mut changed = p;
        changed.propositions[0].statement = "False".into();
        assert_ne!(
            a.package_sha256,
            changed.seal(&root.0).unwrap().package_sha256
        );
    }
    #[test]
    fn rejects_artifact_tampering() {
        let (root, p) = fixture();
        fs::write(root.0.join("proof.lean"), "changed").unwrap();
        assert!(p.seal(&root.0).unwrap_err().contains("SHA-256 mismatch"));
    }
    #[test]
    fn rejects_bad_metadata_and_dangling_evidence() {
        let (root, p) = fixture();
        for mutate in [
            (|p: &mut ClaimPackage| p.heuristics.push(p.heuristics[0].clone()))
                as fn(&mut ClaimPackage),
            |p| p.heuristics[0].evidence = vec!["missing".into()],
            |p| p.heuristics[0].limitations.clear(),
            |p| p.cost_ledger[0].quantity = "1/0".into(),
            |p| p.cost_ledger[0].quantity = "NaN".into(),
            |p| p.cost_ledger[0].evidence.clear(),
            |p| p.schema_version = 2,
            |p| p.source_revision = "main".into(),
            |p| p.propositions.clear(),
        ] {
            let mut bad = p.clone();
            mutate(&mut bad);
            assert!(bad.seal(&root.0).is_err());
        }
    }
    #[test]
    fn rejects_unknown_json_fields() {
        let (_, p) = fixture();
        let mut value = serde_json::to_value(p).unwrap();
        value["verified"] = true.into();
        assert!(serde_json::from_value::<ClaimPackage>(value).is_err());
    }
    #[test]
    fn rejects_traversal_and_absolute_paths() {
        let (root, p) = fixture();
        for path in ["../proof.lean", "/tmp/proof.lean", ""] {
            let mut bad = p.clone();
            bad.artifacts.get_mut("proof").unwrap().path = path.into();
            assert!(bad.seal(&root.0).is_err());
        }
    }
    #[cfg(unix)]
    #[test]
    fn rejects_symlink_escape() {
        let (root, mut p) = fixture();
        let (other, _) = fixture();
        std::os::unix::fs::symlink(other.0.join("proof.lean"), root.0.join("escape.lean")).unwrap();
        p.artifacts.get_mut("proof").unwrap().path = "escape.lean".into();
        assert!(p.seal(&root.0).unwrap_err().contains("escapes"));
    }
}
