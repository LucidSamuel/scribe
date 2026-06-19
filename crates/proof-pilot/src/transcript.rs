//! P5 — Transcript capture: serialize a `SessionJournal` to versioned JSON
//! and reload it for deterministic replay.
//!
//! JSON shape:
//! ```json
//! {
//!   "version": 1,
//!   "toolchain": "leanprover/lean4:v4.30.0-rc2",
//!   "mathlib_rev": "53f8a93a7739dd4eb33926f645811ebb6cee21bf",
//!   "journal": { ... }
//! }
//! ```
//!
//! `toolchain` comes from `journal.toolchain`.
//! `mathlib_rev` is parsed from `<lake_dir>/lake-manifest.json`.

use std::io;
use std::path::Path;

use crate::journal::SessionJournal;

/// Current serialization version.  Increment when the schema breaks.
const TRANSCRIPT_VERSION: u32 = 1;

/// The versioned wrapper written to disk.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq)]
pub struct Transcript {
    /// Schema version (currently 1).
    pub version: u32,
    /// Contents of `lean-toolchain` in the lake directory.
    pub toolchain: String,
    /// Mathlib git revision from `lake-manifest.json`, if found.
    pub mathlib_rev: Option<String>,
    /// The full session journal.
    pub journal: SessionJournal,
}

// ─── Write / Read ─────────────────────────────────────────────────────────────

/// Serialize `journal` to versioned JSON and write it to `path`.
///
/// `mathlib_rev` should come from `read_mathlib_rev(lake_dir)`.
pub fn save(journal: &SessionJournal, path: &str, mathlib_rev: Option<String>) -> io::Result<()> {
    let transcript = Transcript {
        version: TRANSCRIPT_VERSION,
        toolchain: journal.toolchain.clone(),
        mathlib_rev,
        journal: journal.clone(),
    };

    let json = serde_json::to_string_pretty(&transcript)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

    std::fs::write(path, json)
}

/// Deserialize a `Transcript` from a JSON file at `path`.
pub fn load(path: &str) -> io::Result<Transcript> {
    let json = std::fs::read_to_string(path)?;
    serde_json::from_str(&json).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
}

// ─── Mathlib revision helper ─────────────────────────────────────────────────

/// Parse `<lake_dir>/lake-manifest.json` and return the `rev` field for the
/// package named `"mathlib"`.
///
/// Returns `None` if the file is absent, unreadable, or the mathlib package
/// cannot be found.
pub fn read_mathlib_rev(lake_dir: &str) -> Option<String> {
    let manifest_path = Path::new(lake_dir).join("lake-manifest.json");
    let content = std::fs::read_to_string(&manifest_path).ok()?;

    let value: serde_json::Value = serde_json::from_str(&content).ok()?;

    // lake-manifest.json schema:
    // { "packages": [ { "name": "mathlib", "rev": "abcdef..." }, ... ] }
    value
        .get("packages")?
        .as_array()?
        .iter()
        .find(|pkg| pkg.get("name").and_then(|n| n.as_str()) == Some("mathlib"))
        .and_then(|pkg| pkg.get("rev"))
        .and_then(|r| r.as_str())
        .map(|s| s.to_string())
}

// ─── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::journal::{IterationRecord, SessionJournal};

    fn sample_journal() -> SessionJournal {
        SessionJournal {
            theorem_statement: "lean/ZkGadgets/Test.lean".to_string(),
            lean_file: "lean/ZkGadgets/Test.lean".to_string(),
            backend: "claude-cli (test)".to_string(),
            toolchain: "leanprover/lean4:v4.30.0-rc2".to_string(),
            outcome: "exhausted".to_string(),
            iterations: vec![
                IterationRecord {
                    index: 1,
                    source_before: "theorem foo : True := by\n  sorry\n".to_string(),
                    source_after: "theorem foo : True := by\n  trivial\n".to_string(),
                    prompt: "Replace the proof body...".to_string(),
                    llm_response: "```lean\n  trivial\n```".to_string(),
                    build_errors: "Test.lean:2:2: error: unsolved goals".to_string(),
                    goal_states: vec!["⊢ True".to_string()],
                    suggestions: vec!["try trivial".to_string()],
                    patch_applied: true,
                },
                IterationRecord {
                    index: 2,
                    source_before: "theorem foo : True := by\n  trivial\n".to_string(),
                    source_after: "theorem foo : True := by\n  trivial\n".to_string(),
                    prompt: "Replace the proof body...".to_string(),
                    llm_response: "```lean\n  trivial\n```".to_string(),
                    build_errors: String::new(),
                    goal_states: vec![],
                    suggestions: vec![],
                    patch_applied: false,
                },
            ],
        }
    }

    #[test]
    fn round_trip_save_load() {
        let journal = sample_journal();
        let mathlib_rev = Some("53f8a93a7739dd4eb33926f645811ebb6cee21bf".to_string());

        let tmp = tempfile_path("transcript_round_trip");
        save(&journal, &tmp, mathlib_rev.clone()).expect("save failed");

        let loaded = load(&tmp).expect("load failed");

        assert_eq!(loaded.version, TRANSCRIPT_VERSION);
        assert_eq!(loaded.toolchain, journal.toolchain);
        assert_eq!(loaded.mathlib_rev, mathlib_rev);
        assert_eq!(loaded.journal.lean_file, journal.lean_file);
        assert_eq!(loaded.journal.outcome, journal.outcome);
        assert_eq!(loaded.journal.iterations.len(), 2);

        let rec0 = &loaded.journal.iterations[0];
        assert_eq!(rec0.index, 1);
        assert_eq!(rec0.source_after, "theorem foo : True := by\n  trivial\n");
        assert!(rec0.patch_applied);
        assert_eq!(rec0.goal_states, vec!["⊢ True"]);
        assert_eq!(rec0.suggestions, vec!["try trivial"]);

        // Clean up
        let _ = std::fs::remove_file(&tmp);
    }

    #[test]
    fn load_missing_file_is_io_error() {
        let result = load("/tmp/does_not_exist_scribe_test.json");
        assert!(result.is_err());
    }

    #[test]
    fn read_mathlib_rev_from_real_manifest() {
        // Use the actual lake-manifest.json from the project.
        // This test is intentionally not hermetic — it confirms the helper works
        // end-to-end against the real project manifest.
        let rev = read_mathlib_rev("lean");
        // If the manifest is present, rev should be a 40-char hex string.
        if let Some(r) = rev {
            assert_eq!(r.len(), 40, "mathlib rev should be a 40-char git hash");
            assert!(r.chars().all(|c| c.is_ascii_hexdigit()), "should be hex");
        }
        // If the manifest is absent (CI with no lean dir), that's also acceptable.
    }

    #[test]
    fn read_mathlib_rev_missing_dir_returns_none() {
        let rev = read_mathlib_rev("/tmp/does_not_exist_scribe_lake");
        assert!(rev.is_none());
    }

    #[test]
    fn save_produces_valid_json() {
        let journal = sample_journal();
        let tmp = tempfile_path("transcript_json_check");
        save(&journal, &tmp, None).expect("save failed");

        let content = std::fs::read_to_string(&tmp).expect("read failed");
        let value: serde_json::Value = serde_json::from_str(&content).expect("not valid JSON");

        assert_eq!(value["version"].as_u64(), Some(1));
        assert!(value["journal"].is_object());
        assert!(value["journal"]["iterations"].is_array());

        let _ = std::fs::remove_file(&tmp);
    }

    /// Generate a unique temp file path for a test.
    fn tempfile_path(name: &str) -> String {
        format!("/tmp/scribe_test_{name}_{}.json", std::process::id())
    }
}
