//! Session journal — structured record of a proof completion session.
//!
//! `SessionJournal` accumulates one `IterationRecord` per loop iteration and is
//! returned alongside the `SessionResult` by `session::run`. Downstream phases
//! (P4 NOTES.md, P5 transcript replay) consume this type; it must remain
//! serde-stable.

/// One sampled candidate within a best-of-n iteration.
///
/// Recorded for every sample when `samples_per_iter > 1` so the transcript is a
/// complete, deterministic record: `--replay` applies `source_after` states and
/// never re-derives from responses, but an auditor must be able to see every
/// candidate the kernel filtered and which one was accepted.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct CandidateRecord {
    /// 0-based index in sampling order (the order responses were requested).
    pub sample_index: u32,
    /// Raw LLM response for this sample.
    pub llm_response: String,
    /// What happened to this candidate: `"accepted"`, `"build_failed"`,
    /// `"patch_rejected"`, `"duplicate"` (identical patched source as an earlier
    /// sample), `"not_tried"` (an earlier candidate was accepted first), or
    /// `"request_failed"` (the backend call itself failed — `llm_response` is
    /// empty and the error is in `build_output`).
    pub status: String,
    /// Build output for candidates that were built; empty otherwise.
    pub build_output: String,
}

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
    /// Raw text response from the LLM. Under best-of-n this is the response
    /// whose patch ended the iteration (the accepted candidate, or the last
    /// candidate tried when all failed) — consistent with `source_after`.
    pub llm_response: String,
    /// Build / LSP error text shown to the LLM for this iteration.
    pub build_errors: String,
    /// Goal states extracted from the LSP (empty in lake-build mode).
    pub goal_states: Vec<String>,
    /// Heuristic suggestions surfaced by the LSP enricher (empty in lake-build mode).
    pub suggestions: Vec<String>,
    /// `true` if the patch was successfully applied; `false` if it was rejected.
    pub patch_applied: bool,
    /// All sampled candidates, in sampling order. Empty when `samples_per_iter`
    /// is 1 (the single response is already `llm_response`). `#[serde(default)]`
    /// keeps pre-best-of-n transcripts loadable unchanged.
    #[serde(default)]
    pub candidates: Vec<CandidateRecord>,
    /// `sample_index` of the accepted candidate, when one was accepted under
    /// best-of-n sampling.
    #[serde(default)]
    pub accepted_sample: Option<u32>,
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
