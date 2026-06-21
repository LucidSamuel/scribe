use std::fs;
use std::io::Write;
use std::path::Path;

use crate::backend::Backend;
use crate::journal::{IterationRecord, SessionJournal};
use crate::lean_runner::{has_forbidden_tactics, run_lake_build_for_file};
use crate::lsp_feedback::{
    error_suggestions, feedback_as_build_output, format_lsp_feedback, format_probe_results,
    format_search_results, format_suggestions, goal_to_search_query, has_forbidden_in_feedback,
    LspBridge, LspFeedback, ProbeResult, SearchResult,
};
use crate::patcher::apply_patch_with_diagnostics;

/// Configuration for a proof completion session.
pub struct SessionConfig {
    /// Path to the Lean file to prove.
    pub lean_file: String,
    /// Working directory containing the Lake project.
    pub lake_dir: String,
    /// Maximum number of iterations before giving up.
    pub max_iterations: u32,
    /// System prompt text (read from file by caller).
    pub system_prompt: Option<String>,
    /// Optional path for transcript log. If set, every iteration is logged.
    pub transcript: Option<String>,
    /// Use Lean LSP for structured feedback instead of lake build text parsing.
    pub use_lsp: bool,
}

/// Outcome of a proof session.
#[derive(Debug)]
pub enum SessionResult {
    /// Proof accepted by the Lean kernel (lake build returns 0, no sorry).
    Proven { iterations: u32 },
    /// Budget exhausted without a valid proof.
    Exhausted { iterations: u32, last_error: String },
    /// Session failed for an unexpected reason.
    Failed(String),
}

impl SessionResult {
    fn outcome_str(&self) -> &'static str {
        match self {
            SessionResult::Proven { .. } => "proven",
            SessionResult::Exhausted { .. } => "exhausted",
            SessionResult::Failed(_) => "failed",
        }
    }
}

/// Read the toolchain string from `<lake_dir>/lean-toolchain`, or return empty string.
fn read_toolchain(lake_dir: &Path) -> String {
    let toolchain_path = lake_dir.join("lean-toolchain");
    fs::read_to_string(&toolchain_path)
        .unwrap_or_default()
        .trim()
        .to_string()
}

/// Run a proof completion session.
///
/// Loop: read lean file → get feedback (LSP or lake build) → send to backend →
/// get patch → apply → verify → repeat until green or budget exhausted.
///
/// Returns the session result and a `SessionJournal` recording every iteration.
pub fn run(config: &SessionConfig, backend: &dyn Backend) -> (SessionResult, SessionJournal) {
    let lake_dir = Path::new(&config.lake_dir);
    let toolchain = read_toolchain(lake_dir);
    let mut journal = SessionJournal::new(
        config.lean_file.clone(),
        backend.name().to_string(),
        toolchain,
    );

    let result = if config.use_lsp {
        run_with_lsp(config, backend, &mut journal)
    } else {
        run_with_lake_build(config, backend, &mut journal)
    };

    journal.outcome = result.outcome_str().to_string();
    (result, journal)
}

// ─── LSP-based feedback loop ────────────────────────────────────────────────

fn run_with_lsp(
    config: &SessionConfig,
    backend: &dyn Backend,
    journal: &mut SessionJournal,
) -> SessionResult {
    let lean_path = Path::new(&config.lean_file);
    let lake_dir = Path::new(&config.lake_dir);

    let mut log = open_log(config);
    log_line(
        &mut log,
        &format!(
            "=== proof-pilot session (LSP mode) ===\nfile: {}\nbackend: {}\nmax_iters: {}\n",
            config.lean_file,
            backend.name(),
            config.max_iterations
        ),
    );

    // Compute relative path from lake_dir to the lean file for LSP queries.
    let rel_path = match relative_lean_path(lean_path, lake_dir) {
        Some(p) => p,
        None => {
            return SessionResult::Failed(format!(
                "cannot compute relative path: {} not under {}",
                config.lean_file, config.lake_dir
            ));
        }
    };

    // Start LSP bridge
    eprintln!("[proof-pilot] starting LSP bridge...");
    let mut lsp = match LspBridge::new(lake_dir) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("[proof-pilot] LSP bridge failed: {e}, falling back to lake build");
            return run_with_lake_build(config, backend, journal);
        }
    };

    // Initial feedback
    let initial_feedback = match lsp.feedback(&rel_path) {
        Ok(fb) => fb,
        Err(e) => return SessionResult::Failed(format!("initial LSP feedback: {e}")),
    };

    let mut last_feedback;
    if initial_feedback.success && !has_forbidden_in_feedback(&initial_feedback) {
        log_line(
            &mut log,
            "initial LSP check: CLEAN; verifying with lake build\n",
        );
        match run_lake_build_for_file(lake_dir, lean_path) {
            Ok(r) if r.success && !has_forbidden_tactics(&r.combined, Some(&config.lean_file)) => {
                log_line(&mut log, "initial lake build: CLEAN (already proven)\n");
                return SessionResult::Proven { iterations: 0 };
            }
            Ok(r) => {
                eprintln!("[proof-pilot] LSP said OK but lake build disagrees, continuing...");
                log_line(
                    &mut log,
                    &format!("initial lake build: FAIL\n{}\n", r.combined),
                );
                last_feedback = FeedbackSource::BuildOutput(r.combined);
            }
            Err(e) => return SessionResult::Failed(format!("lake build verify: {e}")),
        }
    } else {
        log_line(
            &mut log,
            &format!(
                "initial check: FAIL\n{}\n",
                format_lsp_feedback(&initial_feedback)
            ),
        );
        last_feedback = enrich_feedback(&mut lsp, initial_feedback, &rel_path, &mut log);
    }

    for iteration in 1..=config.max_iterations {
        eprintln!(
            "[proof-pilot] iteration {}/{} (LSP)",
            iteration, config.max_iterations
        );
        log_line(
            &mut log,
            &format!(
                "--- iteration {}/{} ---\n",
                iteration, config.max_iterations
            ),
        );

        let source_before = match fs::read_to_string(lean_path) {
            Ok(s) => s,
            Err(e) => return SessionResult::Failed(format!("read {}: {e}", config.lean_file)),
        };

        // Build prompt with structured LSP feedback
        let prompt = build_lsp_prompt(&config.lean_file, &source_before, &last_feedback, iteration);
        log_line(&mut log, &format!("[prompt]\n{}\n", prompt));

        let llm_response = match backend.complete(&prompt, config.system_prompt.as_deref()) {
            Ok(r) => r,
            Err(e) => return SessionResult::Failed(format!("backend: {e}")),
        };
        log_line(&mut log, &format!("[llm response]\n{}\n", llm_response));

        // Apply patch — use synthetic build output for the patcher's diagnostic targeting
        let build_output = last_feedback.build_output_for_patcher(&config.lean_file);
        let (patched, patch_applied) = match apply_patch_with_diagnostics(
            &source_before,
            &llm_response,
            &build_output,
            Some(&config.lean_file),
        ) {
            Ok(p) => (p, true),
            Err(e) => {
                eprintln!("[proof-pilot] patch rejected: {e}");
                log_line(&mut log, &format!("[patch] REJECTED: {e}\n"));

                // Record failed patch iteration
                journal.push(IterationRecord {
                    index: iteration,
                    source_before: source_before.clone(),
                    source_after: source_before.clone(),
                    prompt: prompt.clone(),
                    llm_response: llm_response.clone(),
                    build_errors: build_output.clone(),
                    goal_states: last_feedback.goal_states(),
                    suggestions: last_feedback.suggestions(),
                    patch_applied: false,
                });

                continue;
            }
        };
        log_line(&mut log, &format!("[patched file]\n{}\n", patched));

        // Write patched file to disk
        if let Err(e) = fs::write(lean_path, &patched) {
            return SessionResult::Failed(format!("write {}: {e}", config.lean_file));
        }

        // Get fresh LSP feedback (close + reopen to pick up disk changes)
        let new_build_errors;
        let iteration_result = match lsp.feedback_after_update(&rel_path) {
            Ok(fb) => {
                if fb.success && !has_forbidden_in_feedback(&fb) {
                    eprintln!("[proof-pilot] proof accepted at iteration {iteration} (LSP)");
                    log_line(
                        &mut log,
                        &format!("[build] SUCCESS at iteration {iteration}\n"),
                    );

                    // Final verification with the exact target file.
                    match run_lake_build_for_file(lake_dir, lean_path) {
                        Ok(r)
                            if r.success
                                && !has_forbidden_tactics(&r.combined, Some(&config.lean_file)) =>
                        {
                            new_build_errors = String::new();
                            Some(SessionResult::Proven {
                                iterations: iteration,
                            })
                        }
                        Ok(r) => {
                            eprintln!(
                                "[proof-pilot] LSP said OK but lake build disagrees, continuing..."
                            );
                            log_line(
                                &mut log,
                                &format!("[build] LSP/lake mismatch\n{}\n", r.combined),
                            );
                            new_build_errors = r.combined.clone();
                            last_feedback = FeedbackSource::BuildOutput(r.combined);
                            None
                        }
                        Err(e) => return SessionResult::Failed(format!("lake build verify: {e}")),
                    }
                } else {
                    eprintln!("[proof-pilot] build failed (LSP), retrying...");
                    log_line(
                        &mut log,
                        &format!("[build] FAIL\n{}\n", format_lsp_feedback(&fb)),
                    );
                    new_build_errors = format_lsp_feedback(&fb);
                    last_feedback = enrich_feedback(&mut lsp, fb, &rel_path, &mut log);
                    None
                }
            }
            Err(e) => {
                eprintln!("[proof-pilot] LSP feedback error: {e}, using lake build fallback");
                // Fall back to target-specific Lean verification for this iteration.
                match run_lake_build_for_file(lake_dir, lean_path) {
                    Ok(r)
                        if r.success
                            && !has_forbidden_tactics(&r.combined, Some(&config.lean_file)) =>
                    {
                        new_build_errors = String::new();
                        Some(SessionResult::Proven {
                            iterations: iteration,
                        })
                    }
                    Ok(r) => {
                        log_line(
                            &mut log,
                            &format!("[build] FAIL (fallback)\n{}\n", r.combined),
                        );
                        new_build_errors = r.combined.clone();
                        last_feedback = FeedbackSource::BuildOutput(r.combined);
                        None
                    }
                    Err(e) => return SessionResult::Failed(format!("lake build: {e}")),
                }
            }
        };

        journal.push(IterationRecord {
            index: iteration,
            source_before,
            source_after: patched,
            prompt,
            llm_response,
            build_errors: new_build_errors,
            goal_states: last_feedback.goal_states(),
            suggestions: last_feedback.suggestions(),
            patch_applied,
        });

        if let Some(result) = iteration_result {
            return result;
        }
    }

    log_line(
        &mut log,
        &format!(
            "[result] EXHAUSTED after {} iterations\n",
            config.max_iterations
        ),
    );

    SessionResult::Exhausted {
        iterations: config.max_iterations,
        last_error: last_feedback.last_error(),
    }
}

enum FeedbackSource {
    Lsp {
        feedback: LspFeedback,
        suggestions: Vec<String>,
        search_results: Vec<SearchResult>,
        probe_results: Vec<ProbeResult>,
    },
    BuildOutput(String),
}

impl FeedbackSource {
    fn prompt_section(&self) -> String {
        match self {
            FeedbackSource::Lsp {
                feedback,
                suggestions,
                search_results,
                probe_results,
            } => {
                let mut out = format_lsp_feedback(feedback);
                out.push_str(&format_suggestions(suggestions));
                out.push_str(&format_search_results(search_results));
                out.push_str(&format_probe_results(probe_results));
                out
            }
            FeedbackSource::BuildOutput(output) => {
                format!("--- build errors (lake fallback) ---\n{output}")
            }
        }
    }

    fn build_output_for_patcher(&self, target_file: &str) -> String {
        match self {
            FeedbackSource::Lsp { feedback, .. } => feedback_as_build_output(feedback, target_file),
            FeedbackSource::BuildOutput(output) => output.clone(),
        }
    }

    fn last_error(&self) -> String {
        match self {
            FeedbackSource::Lsp { feedback, .. } => format_lsp_feedback(feedback),
            FeedbackSource::BuildOutput(output) => output.clone(),
        }
    }

    /// Extract goal state strings for the journal (LSP mode only).
    fn goal_states(&self) -> Vec<String> {
        match self {
            FeedbackSource::Lsp { feedback, .. } => feedback
                .goals
                .iter()
                .flat_map(|g| g.goals.iter().cloned())
                .collect(),
            FeedbackSource::BuildOutput(_) => Vec::new(),
        }
    }

    /// Extract suggestion strings for the journal (LSP mode only).
    fn suggestions(&self) -> Vec<String> {
        match self {
            FeedbackSource::Lsp { suggestions, .. } => suggestions.clone(),
            FeedbackSource::BuildOutput(_) => Vec::new(),
        }
    }
}

/// Candidate tactics to probe at sorry/error positions.
const PROBE_TACTICS: &[&str] = &[
    "ring",
    "simp",
    "field_simp",
    "norm_num",
    "trivial",
    "exact?",
    "apply?",
];

/// Enrich raw LSP feedback with search results, tactic probes, and heuristic suggestions.
fn enrich_feedback(
    lsp: &mut LspBridge,
    feedback: LspFeedback,
    rel_path: &str,
    log: &mut Option<std::fs::File>,
) -> FeedbackSource {
    let suggestions = error_suggestions(&feedback);

    // Search loogle for relevant lemmas based on goal state
    let mut search_results = Vec::new();
    for g in &feedback.goals {
        for goal_text in &g.goals {
            if let Some(query) = goal_to_search_query(goal_text) {
                match lsp.search(&query, 3) {
                    Ok(results) if !results.is_empty() => {
                        log_line(
                            log,
                            &format!("[search] query={query:?} → {} result(s)\n", results.len()),
                        );
                        search_results.extend(results);
                    }
                    Err(e) => {
                        log_line(log, &format!("[search] failed: {e}\n"));
                    }
                    _ => {}
                }
                // Only search for the first goal to keep tokens down
                break;
            }
        }
        if !search_results.is_empty() {
            break;
        }
    }

    // Probe candidate tactics at each sorry/error position
    let mut probe_results = Vec::new();
    // Only probe at the first error position to avoid excessive LSP calls
    if let Some(g) = feedback.goals.first() {
        match lsp.probe(rel_path, g.line, g.col, PROBE_TACTICS) {
            Ok(results) => {
                let useful: Vec<_> = results
                    .iter()
                    .filter(|r| r.status == "solved" || r.status == "progress")
                    .collect();
                if !useful.is_empty() {
                    log_line(
                        log,
                        &format!(
                            "[probe] {} tactic(s) made progress at line {}\n",
                            useful.len(),
                            g.line + 1
                        ),
                    );
                }
                probe_results = results;
            }
            Err(e) => {
                log_line(log, &format!("[probe] failed: {e}\n"));
            }
        }
    }

    FeedbackSource::Lsp {
        feedback,
        suggestions,
        search_results,
        probe_results,
    }
}

// ─── Original lake-build feedback loop (unchanged logic) ────────────────────

fn run_with_lake_build(
    config: &SessionConfig,
    backend: &dyn Backend,
    journal: &mut SessionJournal,
) -> SessionResult {
    let lean_path = Path::new(&config.lean_file);
    let lake_dir = Path::new(&config.lake_dir);

    let mut log = open_log(config);
    log_line(
        &mut log,
        &format!(
            "=== proof-pilot session ===\nfile: {}\nbackend: {}\nmax_iters: {}\n",
            config.lean_file,
            backend.name(),
            config.max_iterations
        ),
    );

    // Initial build to get starting errors
    let mut last_stderr = match run_lake_build_for_file(lake_dir, lean_path) {
        Ok(r) if r.success && !has_forbidden_tactics(&r.combined, Some(&config.lean_file)) => {
            log_line(&mut log, "initial build: CLEAN (already proven)\n");
            return SessionResult::Proven { iterations: 0 };
        }
        Ok(r) => {
            log_line(&mut log, &format!("initial build: FAIL\n{}\n", r.combined));
            r.combined
        }
        Err(e) => return SessionResult::Failed(format!("lake build failed: {}", e)),
    };

    for iteration in 1..=config.max_iterations {
        eprintln!(
            "[proof-pilot] iteration {}/{}",
            iteration, config.max_iterations
        );
        log_line(
            &mut log,
            &format!(
                "--- iteration {}/{} ---\n",
                iteration, config.max_iterations
            ),
        );

        // Read current source
        let source_before = match fs::read_to_string(lean_path) {
            Ok(s) => s,
            Err(e) => return SessionResult::Failed(format!("read {}: {}", config.lean_file, e)),
        };

        // Build prompt for Claude
        let prompt = build_prompt(&config.lean_file, &source_before, &last_stderr, iteration);

        log_line(&mut log, &format!("[prompt]\n{}\n", prompt));

        let llm_response = match backend.complete(&prompt, config.system_prompt.as_deref()) {
            Ok(r) => r,
            Err(e) => return SessionResult::Failed(format!("backend: {e}")),
        };

        log_line(&mut log, &format!("[llm response]\n{}\n", llm_response));

        // Apply patch
        let (patched, patch_applied, build_errors_after) = match apply_patch_with_diagnostics(
            &source_before,
            &llm_response,
            &last_stderr,
            Some(&config.lean_file),
        ) {
            Ok(p) => (p, true, last_stderr.clone()),
            Err(e) => {
                eprintln!("[proof-pilot] patch rejected: {}", e);
                log_line(&mut log, &format!("[patch] REJECTED: {}\n", e));
                let combined_error = format!("(patch error: {})\n{}", e, last_stderr);

                journal.push(IterationRecord {
                    index: iteration,
                    source_before: source_before.clone(),
                    source_after: source_before.clone(),
                    prompt: prompt.clone(),
                    llm_response: llm_response.clone(),
                    build_errors: last_stderr.clone(),
                    goal_states: Vec::new(),
                    suggestions: Vec::new(),
                    patch_applied: false,
                });

                last_stderr = combined_error;
                continue;
            }
        };

        log_line(&mut log, &format!("[patched file]\n{}\n", patched));

        // Write patched file
        if let Err(e) = fs::write(lean_path, &patched) {
            return SessionResult::Failed(format!("write {}: {}", config.lean_file, e));
        }

        // Rebuild
        let (build_result, new_stderr) = match run_lake_build_for_file(lake_dir, lean_path) {
            Ok(r) if r.success && !has_forbidden_tactics(&r.combined, Some(&config.lean_file)) => {
                eprintln!("[proof-pilot] proof accepted at iteration {}", iteration);
                log_line(
                    &mut log,
                    &format!("[build] SUCCESS at iteration {}\n", iteration),
                );

                journal.push(IterationRecord {
                    index: iteration,
                    source_before,
                    source_after: patched,
                    prompt,
                    llm_response,
                    build_errors: build_errors_after,
                    goal_states: Vec::new(),
                    suggestions: Vec::new(),
                    patch_applied,
                });

                return SessionResult::Proven {
                    iterations: iteration,
                };
            }
            Ok(r) => {
                eprintln!("[proof-pilot] build failed, retrying...");
                log_line(&mut log, &format!("[build] FAIL\n{}\n", r.combined));
                let stderr = r.combined.clone();
                (r.combined, stderr)
            }
            Err(e) => return SessionResult::Failed(format!("lake build: {}", e)),
        };

        journal.push(IterationRecord {
            index: iteration,
            source_before,
            source_after: patched,
            prompt,
            llm_response,
            build_errors: build_result,
            goal_states: Vec::new(),
            suggestions: Vec::new(),
            patch_applied,
        });

        last_stderr = new_stderr;
    }

    log_line(
        &mut log,
        &format!(
            "[result] EXHAUSTED after {} iterations\n",
            config.max_iterations
        ),
    );

    SessionResult::Exhausted {
        iterations: config.max_iterations,
        last_error: last_stderr,
    }
}

// ─── Prompt builders ────────────────────────────────────────────────────────

/// Build prompt with structured LSP feedback (goals + hypotheses).
fn build_lsp_prompt(
    lean_file: &str,
    source: &str,
    feedback: &FeedbackSource,
    iteration: u32,
) -> String {
    let mut prompt = String::new();

    prompt.push_str(
        "Replace the proof body (everything after `:= by`) so that the Lean kernel accepts it \
         with zero errors and zero `sorry`. Do NOT change the theorem statement. \
         You may add `import` lines at the top of the code block if needed.\n\n",
    );

    if iteration > 1 {
        prompt.push_str(&format!(
            "This is attempt #{}. Previous attempts failed. \
             Study the feedback carefully. When Lean LSP goals are available, they show exactly \
             what needs to be proved and what is available. Try a DIFFERENT approach.\n\n",
            iteration
        ));
    }

    prompt.push_str("Reply with a single fenced code block containing the proof body ");
    prompt.push_str("(optionally preceded by import lines). No explanation needed.\n\n");

    prompt.push_str(&format!("--- file: {} ---\n{}\n\n", lean_file, source));

    prompt.push_str(&feedback.prompt_section());

    prompt
}

/// Build prompt with flat build errors (original mode).
fn build_prompt(lean_file: &str, source: &str, build_errors: &str, iteration: u32) -> String {
    let mut prompt = String::new();

    prompt.push_str(
        "Replace the proof body (everything after `:= by`) so that `lake build` passes \
         with zero errors and zero `sorry`. Do NOT change the theorem statement. \
         You may add `import` lines at the top of the code block if needed.\n\n",
    );

    if iteration > 1 {
        prompt.push_str(&format!(
            "This is attempt #{}. Previous attempts failed. \
             Carefully analyze the build errors and try a DIFFERENT approach.\n\n",
            iteration
        ));
    }

    prompt.push_str("Reply with a single fenced code block containing the proof body ");
    prompt.push_str("(optionally preceded by import lines). No explanation needed.\n\n");

    prompt.push_str(&format!("--- file: {} ---\n{}\n\n", lean_file, source));
    prompt.push_str(&format!("--- build errors ---\n{}", build_errors));

    prompt
}

// ─── Helpers ────────────────────────────────────────────────────────────────

fn open_log(config: &SessionConfig) -> Option<fs::File> {
    config.transcript.as_ref().and_then(|p| {
        fs::File::create(p)
            .map_err(|e| eprintln!("[proof-pilot] warning: could not create transcript: {e}"))
            .ok()
    })
}

fn log_line(log: &mut Option<fs::File>, msg: &str) {
    if let Some(f) = log.as_mut() {
        let _ = f.write_all(msg.as_bytes());
        let _ = f.flush();
    }
}

/// Compute relative path of `lean_file` from `lake_dir`.
///
/// e.g. lean_file = "lean/ZkGadgets/Foo.lean", lake_dir = "lean"
///    → "ZkGadgets/Foo.lean"
fn relative_lean_path(lean_file: &Path, lake_dir: &Path) -> Option<String> {
    // Try to strip lake_dir prefix
    if let Ok(rel) = lean_file.strip_prefix(lake_dir) {
        return Some(rel.to_string_lossy().into_owned());
    }
    // Try canonical paths
    let abs_file = lean_file.canonicalize().ok()?;
    let abs_lake = lake_dir.canonicalize().ok()?;
    abs_file
        .strip_prefix(&abs_lake)
        .ok()
        .map(|r| r.to_string_lossy().into_owned())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lsp_feedback::{Diagnostic, GoalState};

    #[test]
    fn lsp_prompt_preserves_lake_fallback_output() {
        let feedback =
            FeedbackSource::BuildOutput("Foo.lean:12:2: error: unsolved goals".to_string());

        let prompt = build_lsp_prompt(
            "Foo.lean",
            "theorem foo : True := by\n  sorry",
            &feedback,
            2,
        );

        assert!(prompt.contains("--- build errors (lake fallback) ---"));
        assert!(prompt.contains("Foo.lean:12:2: error: unsolved goals"));
        assert_eq!(
            feedback.build_output_for_patcher("Foo.lean"),
            "Foo.lean:12:2: error: unsolved goals"
        );
    }

    #[test]
    fn lsp_prompt_includes_enrichment() {
        let feedback = FeedbackSource::Lsp {
            feedback: LspFeedback {
                success: false,
                diagnostics: vec![Diagnostic {
                    line: 10,
                    col: 2,
                    severity: 1,
                    message: "linarith failed to find a contradiction".to_string(),
                }],
                goals: vec![GoalState {
                    line: 10,
                    col: 2,
                    goals: vec!["x : ZMod p\n⊢ q = x * x".to_string()],
                }],
            },
            suggestions: vec![
                "linarith does not work on ZMod p. Use `linear_combination` instead.".to_string(),
            ],
            search_results: vec![SearchResult {
                name: "sub_eq_zero".to_string(),
                type_sig: "a - b = 0 ↔ a = b".to_string(),
                module: "Mathlib.Algebra.Group.Basic".to_string(),
            }],
            probe_results: vec![ProbeResult {
                tactic: "ring".to_string(),
                status: "progress".to_string(),
                remaining_goals: vec!["⊢ False".to_string()],
                error: None,
            }],
        };

        let prompt = build_lsp_prompt(
            "Foo.lean",
            "theorem foo : True := by\n  sorry",
            &feedback,
            2,
        );

        assert!(prompt.contains("--- hints ---"));
        assert!(prompt.contains("linear_combination"));
        assert!(prompt.contains("--- relevant Mathlib lemmas (loogle) ---"));
        assert!(prompt.contains("sub_eq_zero"));
        assert!(prompt.contains("--- tactic probe results ---"));
        assert!(prompt.contains("`ring` — makes progress"));
    }

    #[test]
    fn feedback_source_goal_states_lsp() {
        let feedback = FeedbackSource::Lsp {
            feedback: LspFeedback {
                success: false,
                diagnostics: vec![],
                goals: vec![GoalState {
                    line: 5,
                    col: 2,
                    goals: vec!["⊢ True".to_string(), "⊢ False".to_string()],
                }],
            },
            suggestions: vec!["try trivial".to_string()],
            search_results: vec![],
            probe_results: vec![],
        };
        let states = feedback.goal_states();
        assert_eq!(states, vec!["⊢ True", "⊢ False"]);
        let sugs = feedback.suggestions();
        assert_eq!(sugs, vec!["try trivial"]);
    }

    #[test]
    fn feedback_source_goal_states_build_output() {
        let feedback = FeedbackSource::BuildOutput("error: unsolved goals".to_string());
        assert!(feedback.goal_states().is_empty());
        assert!(feedback.suggestions().is_empty());
    }
}
