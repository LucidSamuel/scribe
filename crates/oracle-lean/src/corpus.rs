//! The circuit corpus: the evidence behind every verdict the Lean oracle
//! issues (locked decision 5).
//!
//! A corpus is not test fixtures. It is versioned, it grows monotonically,
//! and it carries *positives as well as negatives* — an oracle that rejects
//! everything has perfect negative discrimination and is useless. The on-disk
//! form lives in `corpus/circuits/`: a `corpus.toml` manifest plus one IR
//! file (gadget TOML or CircuitIR JSON) per instance.
//!
//! The five negatives are `benchmark/suite.toml`'s `kind = "negative"`
//! gadgets, promoted to first-class corpus entries with stable ids so escapes
//! are reportable. The gadget names inside the IR files stay neutral on
//! purpose: the name becomes the theorem name the model sees, and a
//! `neg-...` name would leak the expected answer. Only the manifest (which
//! the model never sees) marks an instance negative.

use std::fs;
use std::path::{Path, PathBuf};

use circuit_ir::CircuitIR;
use scribe_core::{Corpus, DiscriminationReport, Instance};
use serde::{Deserialize, Serialize};

use crate::CircuitClaim;

/// One manifest row.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ManifestEntry {
    /// Stable corpus id (this is what a `DiscriminationReport` escape names).
    pub id: String,
    /// `"negative"` (the oracle MUST reject) or `"positive"` (MUST accept).
    pub kind: String,
    /// IR file, relative to the corpus directory. `.toml` loads as gadget
    /// TOML, `.json` as versioned CircuitIR JSON.
    pub file: String,
    /// Where this instance came from (provenance, human-readable).
    #[serde(default)]
    pub origin: Option<String>,
    /// Why this instance is in the corpus.
    #[serde(default)]
    pub note: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Manifest {
    version: String,
    #[serde(rename = "instances")]
    entries: Vec<ManifestEntry>,
}

/// A loaded, in-memory circuit corpus.
#[derive(Debug)]
pub struct CircuitCorpus {
    version: String,
    entries: Vec<(ManifestEntry, CircuitIR)>,
}

#[derive(Debug)]
pub enum CorpusError {
    Io {
        path: PathBuf,
        message: String,
    },
    Parse {
        path: PathBuf,
        message: String,
    },
    /// Bad manifest content (unknown kind, duplicate id, missing spec, …).
    Invalid(String),
}

impl std::fmt::Display for CorpusError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CorpusError::Io { path, message } => {
                write!(f, "cannot read {}: {}", path.display(), message)
            }
            CorpusError::Parse { path, message } => {
                write!(f, "cannot parse {}: {}", path.display(), message)
            }
            CorpusError::Invalid(message) => write!(f, "invalid corpus: {message}"),
        }
    }
}

impl std::error::Error for CorpusError {}

impl CircuitCorpus {
    /// Load `corpus.toml` and every IR it references from `dir`.
    pub fn load(dir: &Path) -> Result<Self, CorpusError> {
        let manifest_path = dir.join("corpus.toml");
        let raw = fs::read_to_string(&manifest_path).map_err(|e| CorpusError::Io {
            path: manifest_path.clone(),
            message: e.to_string(),
        })?;
        let manifest: Manifest = toml::from_str(&raw).map_err(|e| CorpusError::Parse {
            path: manifest_path,
            message: e.to_string(),
        })?;

        let mut entries = Vec::with_capacity(manifest.entries.len());
        let mut seen = std::collections::HashSet::new();
        for entry in manifest.entries {
            if !seen.insert(entry.id.clone()) {
                return Err(CorpusError::Invalid(format!("duplicate id {:?}", entry.id)));
            }
            if entry.kind != "negative" && entry.kind != "positive" {
                return Err(CorpusError::Invalid(format!(
                    "instance {:?} has unknown kind {:?} (expected \"negative\" or \"positive\")",
                    entry.id, entry.kind
                )));
            }
            let path = dir.join(&entry.file);
            let ir = load_ir(&path)?;
            if ir.soundness_spec.is_none() {
                return Err(CorpusError::Invalid(format!(
                    "instance {:?} has no soundness_spec — there is no claim to adjudicate",
                    entry.id
                )));
            }
            entries.push((entry, ir));
        }
        Ok(CircuitCorpus {
            version: manifest.version,
            entries,
        })
    }

    pub fn entries(&self) -> &[(ManifestEntry, CircuitIR)] {
        &self.entries
    }

    fn of_kind(&self, kind: &str) -> Vec<Instance<CircuitClaim>> {
        self.entries
            .iter()
            .filter(|(entry, _)| entry.kind == kind)
            .map(|(entry, ir)| Instance {
                id: entry.id.as_str().into(),
                claim: CircuitClaim::new(&entry.id),
                subject: ir.clone(),
            })
            .collect()
    }
}

fn load_ir(path: &Path) -> Result<CircuitIR, CorpusError> {
    if path.extension().and_then(|e| e.to_str()) == Some("json") {
        let raw = fs::read_to_string(path).map_err(|e| CorpusError::Io {
            path: path.to_path_buf(),
            message: e.to_string(),
        })?;
        CircuitIR::from_json(&raw).map_err(|e| CorpusError::Parse {
            path: path.to_path_buf(),
            message: e.to_string(),
        })
    } else {
        circuit_ir::load_toml_file(path).map_err(|e| CorpusError::Parse {
            path: path.to_path_buf(),
            message: e.to_string(),
        })
    }
}

impl Corpus<CircuitClaim> for CircuitCorpus {
    fn negatives(&self) -> Vec<Instance<CircuitClaim>> {
        self.of_kind("negative")
    }

    fn positives(&self) -> Vec<Instance<CircuitClaim>> {
        self.of_kind("positive")
    }

    fn version(&self) -> &str {
        &self.version
    }
}

/// A committed validation run: the [`DiscriminationReport`] plus enough
/// context to reproduce it. Stored at
/// `corpus/circuits/discrimination-report.json`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommittedValidation {
    /// ISO date of the run.
    pub generated: String,
    /// Oracle description (backend + budgets).
    pub oracle: String,
    pub prove_iters: u32,
    pub refute_iters: u32,
    pub report: DiscriminationReport,
}

impl CommittedValidation {
    pub fn load(path: &Path) -> Result<Self, CorpusError> {
        let raw = fs::read_to_string(path).map_err(|e| CorpusError::Io {
            path: path.to_path_buf(),
            message: e.to_string(),
        })?;
        serde_json::from_str(&raw).map_err(|e| CorpusError::Parse {
            path: path.to_path_buf(),
            message: e.to_string(),
        })
    }

    pub fn save(&self, path: &Path) -> std::io::Result<()> {
        let json = serde_json::to_string_pretty(self).expect("report serializes");
        fs::write(path, format!("{json}\n"))
    }
}
