//! Session journal — structured record of a proof completion session.
//!
//! `SessionJournal` accumulates one `IterationRecord` per loop iteration and is
//! returned alongside the `SessionResult` by `session::run`. Downstream phases
//! (P4 NOTES.md, P5 transcript replay) consume this type; it must remain
//! serde-stable.

/// A single LLM iteration within a proof session.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct IterationRecord {
    /// 1-based iteration index.
    pub index: u32,
    /// Lean source before the patch was applied.
    pub source_before: String,
    /// Lean source after the patch was applied (same as before if patch was rejected).
    pub source_after: String,
    /// Full prompt sent to the LLM.
    pub prompt: String,
    /// Raw text response from the LLM.
    pub llm_response: String,
    /// Build / LSP error text shown to the LLM for this iteration.
    pub build_errors: String,
    /// Goal states extracted from the LSP (empty in lake-build mode).
    pub goal_states: Vec<String>,
    /// Heuristic suggestions surfaced by the LSP enricher (empty in lake-build mode).
    pub suggestions: Vec<String>,
    /// `true` if the patch was successfully applied; `false` if it was rejected.
    pub patch_applied: bool,
}

/// Complete record of one proof completion session.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SessionJournal {
    /// The theorem statement (lean file path used as identifier).
    pub theorem_statement: String,
    /// Absolute or relative path to the Lean file.
    pub lean_file: String,
    /// Human-readable name of the backend used (e.g. `"claude-cli (claude-sonnet-5)"`).
    pub backend: String,
    /// Contents of `lean-toolchain` in the lake directory, or empty string if absent.
    pub toolchain: String,
    /// Human-readable final outcome (`"proven"`, `"exhausted"`, `"failed"`).
    pub outcome: String,
    /// Per-iteration records, in order.
    pub iterations: Vec<IterationRecord>,
}

impl SessionJournal {
    /// Create a new, empty journal for a session.
    pub fn new(lean_file: String, backend: String, toolchain: String) -> Self {
        SessionJournal {
            theorem_statement: lean_file.clone(),
            lean_file,
            backend,
            toolchain,
            outcome: String::new(),
            iterations: Vec::new(),
        }
    }

    /// Append one iteration record to the journal.
    pub fn push(&mut self, record: IterationRecord) {
        self.iterations.push(record);
    }
}
