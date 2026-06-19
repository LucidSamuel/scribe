//! P5 — Deterministic replay: apply recorded `source_after` states from a
//! `Transcript` to the target Lean file without calling the LLM.
//!
//! Toolchain / Mathlib-rev pinning is checked before replay starts.
//! Pass `allow_toolchain_mismatch = true` to skip the hard error (warn only).

use std::io;
use std::path::Path;

use crate::lean_runner::run_lake_build_for_file;
use crate::transcript::{self, Transcript};

/// Outcome of one replayed step.
#[derive(Debug, Clone)]
pub struct StepResult {
    /// 1-based iteration index from the transcript.
    pub index: u32,
    /// Whether the `lake build` passed for this step (`None` when `verify = false`).
    pub build_passed: Option<bool>,
    /// Combined build output when `verify = true`, empty string otherwise.
    pub build_output: String,
}

/// Outcome of the full replay.
#[derive(Debug)]
pub struct ReplayResult {
    /// Per-step outcomes, in transcript order.
    pub steps: Vec<StepResult>,
    /// `true` if the final step's build passed (only meaningful when `verify = true`).
    pub final_build_passed: bool,
    /// Number of steps replayed.
    pub steps_applied: usize,
}

/// Error returned by `replay`.
#[derive(Debug)]
pub enum ReplayError {
    /// The transcript could not be loaded.
    LoadFailed(io::Error),
    /// Toolchain or Mathlib rev mismatch and `allow_toolchain_mismatch = false`.
    ToolchainMismatch(String),
    /// The target Lean file could not be written.
    WriteError(io::Error),
    /// `lake build` could not be invoked (I/O-level, not a build failure).
    BuildError(io::Error),
}

impl std::fmt::Display for ReplayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplayError::LoadFailed(e) => write!(f, "failed to load transcript: {e}"),
            ReplayError::ToolchainMismatch(msg) => write!(f, "toolchain mismatch: {msg}"),
            ReplayError::WriteError(e) => write!(f, "failed to write lean file: {e}"),
            ReplayError::BuildError(e) => write!(f, "lake build invocation failed: {e}"),
        }
    }
}

impl std::error::Error for ReplayError {}

/// Replay a recorded transcript onto `lean_file`.
///
/// For each `IterationRecord` in order, write `source_after` to `lean_file`.
/// If `verify` is true, run `lake build` after each step and record the result.
/// Toolchain / Mathlib-rev mismatch causes an error unless
/// `allow_toolchain_mismatch` is true (in which case a warning is printed).
pub fn replay(
    transcript_path: &str,
    lean_file: &str,
    lake_dir: &str,
    verify: bool,
    allow_toolchain_mismatch: bool,
) -> Result<ReplayResult, ReplayError> {
    let transcript = transcript::load(transcript_path).map_err(ReplayError::LoadFailed)?;

    // ── Toolchain / Mathlib-rev check ────────────────────────────────────────
    check_pinning(&transcript, lake_dir, allow_toolchain_mismatch)?;

    // ── Apply steps ──────────────────────────────────────────────────────────
    let lean_path = Path::new(lean_file);
    let lake_path = Path::new(lake_dir);

    let mut steps: Vec<StepResult> = Vec::new();

    for record in &transcript.journal.iterations {
        eprintln!("[replay] applying iteration {}", record.index);

        std::fs::write(lean_path, &record.source_after).map_err(ReplayError::WriteError)?;

        if verify {
            let build = run_lake_build_for_file(lake_path, lean_path)
                .map_err(ReplayError::BuildError)?;
            let passed = build.success;
            if passed {
                eprintln!("[replay] iteration {} — build PASSED", record.index);
            } else {
                eprintln!("[replay] iteration {} — build FAILED", record.index);
            }
            steps.push(StepResult {
                index: record.index,
                build_passed: Some(passed),
                build_output: build.combined,
            });
        } else {
            steps.push(StepResult {
                index: record.index,
                build_passed: None,
                build_output: String::new(),
            });
        }
    }

    let final_build_passed = steps
        .last()
        .and_then(|s| s.build_passed)
        .unwrap_or(false);

    Ok(ReplayResult {
        steps_applied: steps.len(),
        final_build_passed,
        steps,
    })
}

// ─── Toolchain / Mathlib-rev pinning check ───────────────────────────────────

fn check_pinning(
    transcript: &Transcript,
    lake_dir: &str,
    allow_mismatch: bool,
) -> Result<(), ReplayError> {
    let mut mismatches: Vec<String> = Vec::new();

    // Compare toolchain
    let current_toolchain = read_current_toolchain(lake_dir);
    if !transcript.toolchain.is_empty()
        && !current_toolchain.is_empty()
        && transcript.toolchain != current_toolchain
    {
        mismatches.push(format!(
            "lean toolchain: transcript has `{}`, current is `{}`",
            transcript.toolchain, current_toolchain
        ));
    }

    // Compare Mathlib rev
    if let Some(recorded_rev) = &transcript.mathlib_rev {
        let current_rev = transcript::read_mathlib_rev(lake_dir);
        if let Some(cur_rev) = &current_rev {
            if recorded_rev != cur_rev {
                mismatches.push(format!(
                    "mathlib rev: transcript has `{recorded_rev}`, current is `{cur_rev}`"
                ));
            }
        }
    }

    if mismatches.is_empty() {
        return Ok(());
    }

    let message = mismatches.join("; ");

    if allow_mismatch {
        eprintln!("[replay] WARNING — toolchain mismatch (--allow-toolchain-mismatch): {message}");
        Ok(())
    } else {
        Err(ReplayError::ToolchainMismatch(format!(
            "{message} — pass --allow-toolchain-mismatch to override"
        )))
    }
}

fn read_current_toolchain(lake_dir: &str) -> String {
    let path = Path::new(lake_dir).join("lean-toolchain");
    std::fs::read_to_string(&path)
        .unwrap_or_default()
        .trim()
        .to_string()
}

// ─── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::journal::{IterationRecord, SessionJournal};
    use crate::transcript;

    fn sample_journal(toolchain: &str) -> SessionJournal {
        SessionJournal {
            theorem_statement: "lean/ZkGadgets/Test.lean".to_string(),
            lean_file: "lean/ZkGadgets/Test.lean".to_string(),
            backend: "claude-cli (test)".to_string(),
            toolchain: toolchain.to_string(),
            outcome: "proven".to_string(),
            iterations: vec![
                IterationRecord {
                    index: 1,
                    source_before: "-- original\ntheorem foo : True := by\n  sorry\n".to_string(),
                    source_after: "-- step1\ntheorem foo : True := by\n  trivial\n".to_string(),
                    prompt: "test".to_string(),
                    llm_response: "```lean\n  trivial\n```".to_string(),
                    build_errors: String::new(),
                    goal_states: vec![],
                    suggestions: vec![],
                    patch_applied: true,
                },
                IterationRecord {
                    index: 2,
                    source_before: "-- step1\ntheorem foo : True := by\n  trivial\n".to_string(),
                    source_after: "-- step2\ntheorem foo : True := by\n  exact True.intro\n"
                        .to_string(),
                    prompt: "test".to_string(),
                    llm_response: "```lean\n  exact True.intro\n```".to_string(),
                    build_errors: String::new(),
                    goal_states: vec![],
                    suggestions: vec![],
                    patch_applied: true,
                },
            ],
        }
    }

    /// Helper to create a temp path unique to this test run.
    fn tmp(name: &str) -> String {
        format!("/tmp/scribe_replay_test_{name}_{}", std::process::id())
    }

    #[test]
    fn replay_applies_source_after_states() {
        // Write a transcript to a temp JSON file.
        let journal = sample_journal("leanprover/lean4:v4.30.0-rc2");
        let transcript_path = tmp("transcript.json");
        transcript::save(&journal, &transcript_path, None).expect("save failed");

        // Target lean file starts empty.
        let lean_file = tmp("Target.lean");
        std::fs::write(&lean_file, "-- initial\n").expect("write initial lean file");

        // Replay without verification (no lake build needed).
        let result = replay(
            &transcript_path,
            &lean_file,
            "lean",           // lake_dir — only used for toolchain check
            false,            // verify = false
            true,             // allow_toolchain_mismatch = true
        )
        .expect("replay failed");

        assert_eq!(result.steps_applied, 2);

        // After replay, the file should contain the last source_after.
        let final_content = std::fs::read_to_string(&lean_file).expect("read lean file");
        assert!(
            final_content.contains("exact True.intro"),
            "file should contain the last source_after state, got: {final_content}"
        );

        // Clean up
        let _ = std::fs::remove_file(&transcript_path);
        let _ = std::fs::remove_file(&lean_file);
    }

    #[test]
    fn replay_toolchain_mismatch_errors_without_flag() {
        // Write a fake lake dir with a toolchain file whose content does NOT
        // match the transcript's recorded toolchain.  We own this directory
        // so we don't rely on the real `lean/lean-toolchain` being findable.
        let fake_lake = tmp("fake_lake_mismatch");
        std::fs::create_dir_all(&fake_lake).expect("create fake lake dir");
        let toolchain_file = format!("{fake_lake}/lean-toolchain");
        std::fs::write(&toolchain_file, "leanprover/lean4:v4.30.0-rc2\n")
            .expect("write fake toolchain");

        // Transcript records a DIFFERENT toolchain → mismatch expected.
        let journal = sample_journal("leanprover/lean4:v1.0.0-mismatch");
        let transcript_path = tmp("mismatch_transcript.json");
        transcript::save(&journal, &transcript_path, None).expect("save failed");

        let lean_file = tmp("MismatchTarget.lean");
        std::fs::write(&lean_file, "-- initial\n").expect("write lean file");

        let result = replay(
            &transcript_path,
            &lean_file,
            &fake_lake,
            false,
            false, // allow_toolchain_mismatch = false  → should error
        );

        match result {
            Err(ReplayError::ToolchainMismatch(_)) => { /* expected */ }
            other => panic!("expected ToolchainMismatch, got: {other:?}"),
        }

        // Clean up
        let _ = std::fs::remove_file(&transcript_path);
        let _ = std::fs::remove_file(&lean_file);
        let _ = std::fs::remove_dir_all(&fake_lake);
    }

    #[test]
    fn replay_toolchain_mismatch_allowed_with_flag() {
        // Same setup — mismatched toolchain — but allow_toolchain_mismatch=true.
        let fake_lake = tmp("fake_lake_allowed");
        std::fs::create_dir_all(&fake_lake).expect("create fake lake dir");
        let toolchain_file = format!("{fake_lake}/lean-toolchain");
        std::fs::write(&toolchain_file, "leanprover/lean4:v4.30.0-rc2\n")
            .expect("write fake toolchain");

        let journal = sample_journal("leanprover/lean4:v1.0.0-mismatch");
        let transcript_path = tmp("allowed_mismatch.json");
        transcript::save(&journal, &transcript_path, None).expect("save failed");

        let lean_file = tmp("AllowedMismatch.lean");
        std::fs::write(&lean_file, "-- initial\n").expect("write lean file");

        // Should succeed (just warn) when allow_toolchain_mismatch = true.
        let result = replay(
            &transcript_path,
            &lean_file,
            &fake_lake,
            false,
            true, // allow_toolchain_mismatch = true
        );

        assert!(result.is_ok(), "should succeed with allow_toolchain_mismatch=true: {result:?}");

        // Clean up
        let _ = std::fs::remove_file(&transcript_path);
        let _ = std::fs::remove_file(&lean_file);
        let _ = std::fs::remove_dir_all(&fake_lake);
    }

    #[test]
    fn replay_missing_transcript_is_load_error() {
        let result = replay(
            "/tmp/does_not_exist_scribe_replay.json",
            "/tmp/dummy.lean",
            "lean",
            false,
            true,
        );

        assert!(matches!(result, Err(ReplayError::LoadFailed(_))));
    }

    #[test]
    fn replay_step_count_matches_journal_iterations() {
        let journal = sample_journal("leanprover/lean4:v4.30.0-rc2");
        let transcript_path = tmp("step_count.json");
        transcript::save(&journal, &transcript_path, None).expect("save failed");

        let lean_file = tmp("StepCount.lean");
        std::fs::write(&lean_file, "-- start\n").expect("write lean file");

        let result = replay(&transcript_path, &lean_file, "lean", false, true)
            .expect("replay failed");

        assert_eq!(
            result.steps_applied,
            journal.iterations.len(),
            "step count must match journal iteration count"
        );
        assert_eq!(result.steps[0].index, 1);
        assert_eq!(result.steps[1].index, 2);
        // Without verify, build_passed is None
        assert!(result.steps.iter().all(|s| s.build_passed.is_none()));

        // Clean up
        let _ = std::fs::remove_file(&transcript_path);
        let _ = std::fs::remove_file(&lean_file);
    }
}
