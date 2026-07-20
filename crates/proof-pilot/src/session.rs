use std::fs;
use std::io::Write;
use std::path::Path;

use crate::backend::Backend;
use crate::journal::{CandidateRecord, IterationRecord, SessionJournal};
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
    /// Best-of-n: sampled proof attempts per iteration (default 1). The kernel
    /// filters — candidates are deduplicated, tried shortest-first, and the
    /// first to build wins. Soundness-free parallelism: a wrong candidate costs
    /// a build, never a false acceptance. Lake-build mode only; LSP mode warns
    /// and samples once.
    pub samples_per_iter: u32,
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

    if config.samples_per_iter > 1 {
        eprintln!(
            "[proof-pilot] warning: --samples-per-iter applies to lake-build mode; \
             LSP mode samples once per iteration"
        );
    }

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
                    candidates: Vec::new(),
                    accepted_sample: None,
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
            candidates: Vec::new(),
            accepted_sample: None,
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

// ─── Best-of-n sampling ─────────────────────────────────────────────────────

/// Everything the build phase needs for one best-of-n iteration, planned
/// deterministically before any file is written.
struct SamplePlan {
    /// One record per sample, in sampling order. `patch_rejected` / `duplicate`
    /// are final; the rest start as `"not_tried"` and are updated by the build
    /// phase.
    records: Vec<CandidateRecord>,
    /// `(sample_index, patched_source)` in build order: shortest patched source
    /// first (ties broken by sampling order, so the plan is deterministic given
    /// the responses).
    try_order: Vec<(u32, String)>,
}

/// Request `k` completions. For `k > 1` the calls run concurrently on scoped
/// threads (the kernel filters, so parallel sampling is soundness-free); the
/// returned vector is in sampling order regardless of completion order.
fn sample_responses(
    backend: &dyn Backend,
    prompt: &str,
    system_prompt: Option<&str>,
    k: u32,
) -> Vec<Result<String, crate::backend::BackendError>> {
    if k <= 1 {
        return vec![backend.complete(prompt, system_prompt)];
    }
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..k)
            .map(|_| scope.spawn(|| backend.complete(prompt, system_prompt)))
            .collect();
        handles
            .into_iter()
            .map(|h| {
                h.join().unwrap_or_else(|_| {
                    Err(crate::backend::BackendError::RequestFailed(
                        "sampling thread panicked".to_string(),
                    ))
                })
            })
            .collect()
    })
}

/// Plan the build phase from the raw sampling results: request failures are
/// recorded in place (so `sample_index` always refers to the original K
/// requested samples and the journal genuinely records every candidate), then
/// each successful response is patched (pure — no file is touched), rejects
/// recorded, identical patched sources hash-deduped (samples at low temperature
/// frequently collapse to the same proof, and builds dominate cost), and the
/// survivors ordered shortest-first.
fn plan_candidates(
    source_before: &str,
    samples: &[Result<String, crate::backend::BackendError>],
    build_output: &str,
    target_file: &str,
) -> SamplePlan {
    let mut records: Vec<CandidateRecord> = Vec::with_capacity(samples.len());
    let mut planned: Vec<(u32, String)> = Vec::new();
    let mut seen: std::collections::HashSet<u64> = std::collections::HashSet::new();

    for (i, sample) in samples.iter().enumerate() {
        let sample_index = i as u32;
        let response = match sample {
            Ok(r) => r,
            Err(e) => {
                records.push(CandidateRecord {
                    sample_index,
                    llm_response: String::new(),
                    status: "request_failed".to_string(),
                    build_output: format!("backend: {e}"),
                });
                continue;
            }
        };
        match apply_patch_with_diagnostics(source_before, response, build_output, Some(target_file))
        {
            Ok(patched) => {
                use std::hash::{Hash, Hasher};
                let mut hasher = std::collections::hash_map::DefaultHasher::new();
                patched.hash(&mut hasher);
                if seen.insert(hasher.finish()) {
                    planned.push((sample_index, patched));
                    records.push(CandidateRecord {
                        sample_index,
                        llm_response: response.clone(),
                        status: "not_tried".to_string(),
                        build_output: String::new(),
                    });
                } else {
                    records.push(CandidateRecord {
                        sample_index,
                        llm_response: response.clone(),
                        status: "duplicate".to_string(),
                        build_output: String::new(),
                    });
                }
            }
            Err(e) => {
                records.push(CandidateRecord {
                    sample_index,
                    llm_response: response.clone(),
                    status: "patch_rejected".to_string(),
                    build_output: format!("patch error: {e}"),
                });
            }
        }
    }

    // Shortest candidate first; sampling order breaks ties deterministically.
    planned.sort_by(|a, b| a.1.len().cmp(&b.1.len()).then(a.0.cmp(&b.0)));

    SamplePlan {
        records,
        try_order: planned,
    }
}

fn set_candidate_status(
    records: &mut [CandidateRecord],
    sample_index: u32,
    status: &str,
    build_output: String,
) {
    if let Some(r) = records.iter_mut().find(|r| r.sample_index == sample_index) {
        r.status = status.to_string();
        r.build_output = build_output;
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

        // Sample k candidates (concurrently when k > 1); the kernel filters.
        let k = config.samples_per_iter.max(1);
        let sampled = sample_responses(backend, &prompt, config.system_prompt.as_deref(), k);
        let ok_count = sampled.iter().filter(|r| r.is_ok()).count();
        if ok_count == 0 {
            let e = sampled
                .into_iter()
                .find_map(|r| r.err())
                .expect("no responses implies at least one error");
            return SessionResult::Failed(format!("backend: {e}"));
        }
        if ok_count < k as usize {
            eprintln!(
                "[proof-pilot] warning: {}/{} sample(s) failed; continuing with the rest",
                k as usize - ok_count,
                k
            );
        }
        let first_ok_response = sampled
            .iter()
            .find_map(|r| r.as_ref().ok())
            .cloned()
            .expect("ok_count > 0");
        for (i, r) in sampled.iter().enumerate() {
            match r {
                Ok(text) => log_line(&mut log, &format!("[llm response, sample {i}]\n{text}\n")),
                Err(e) => log_line(
                    &mut log,
                    &format!("[llm response, sample {i}] FAILED: {e}\n"),
                ),
            }
        }

        // Plan: patch each candidate (pure), dedupe, shortest-first. The plan's
        // records cover ALL k requested samples — including request failures —
        // with sample_index referring to the original sampling order.
        let mut plan = plan_candidates(&source_before, &sampled, &last_stderr, &config.lean_file);

        // Journal candidate records only under genuine best-of-n; with k = 1 the
        // single response is already `llm_response` (schema-stable with old runs).
        let record_candidates = k > 1;

        if plan.try_order.is_empty() {
            // Every successful sample was rejected by the patcher.
            let first_reason = plan
                .records
                .iter()
                .find(|r| r.status == "patch_rejected")
                .map(|r| r.build_output.clone())
                .unwrap_or_else(|| "patch error: no candidates".to_string());
            eprintln!("[proof-pilot] patch rejected: {first_reason}");
            log_line(&mut log, &format!("[patch] REJECTED: {first_reason}\n"));
            let combined_error = format!("({})\n{}", first_reason, last_stderr);

            journal.push(IterationRecord {
                index: iteration,
                source_before: source_before.clone(),
                source_after: source_before.clone(),
                prompt: prompt.clone(),
                llm_response: first_ok_response.clone(),
                build_errors: last_stderr.clone(),
                goal_states: Vec::new(),
                suggestions: Vec::new(),
                patch_applied: false,
                candidates: if record_candidates {
                    plan.records
                } else {
                    Vec::new()
                },
                accepted_sample: None,
            });

            last_stderr = combined_error;
            continue;
        }

        // Build phase: sequential with early exit — success costs one build.
        let mut accepted: Option<(u32, String)> = None;
        let mut last_failed: Option<(u32, String, String)> = None;
        let try_order = std::mem::take(&mut plan.try_order);
        for (sample_index, patched) in &try_order {
            log_line(
                &mut log,
                &format!("[patched file, sample {sample_index}]\n{patched}\n"),
            );
            if let Err(e) = fs::write(lean_path, patched) {
                return SessionResult::Failed(format!("write {}: {}", config.lean_file, e));
            }
            match run_lake_build_for_file(lake_dir, lean_path) {
                Ok(r)
                    if r.success
                        && !has_forbidden_tactics(&r.combined, Some(&config.lean_file)) =>
                {
                    set_candidate_status(&mut plan.records, *sample_index, "accepted", r.combined);
                    accepted = Some((*sample_index, patched.clone()));
                    break;
                }
                Ok(r) => {
                    log_line(
                        &mut log,
                        &format!("[build] FAIL (sample {sample_index})\n{}\n", r.combined),
                    );
                    set_candidate_status(
                        &mut plan.records,
                        *sample_index,
                        "build_failed",
                        r.combined.clone(),
                    );
                    last_failed = Some((*sample_index, patched.clone(), r.combined));
                }
                Err(e) => return SessionResult::Failed(format!("lake build: {}", e)),
            }
        }

        let response_for = |sample_index: u32| -> String {
            plan.records
                .iter()
                .find(|r| r.sample_index == sample_index)
                .map(|r| r.llm_response.clone())
                .unwrap_or_default()
        };

        if let Some((sample_index, patched)) = accepted {
            eprintln!("[proof-pilot] proof accepted at iteration {}", iteration);
            log_line(
                &mut log,
                &format!("[build] SUCCESS at iteration {iteration} (sample {sample_index})\n"),
            );

            journal.push(IterationRecord {
                index: iteration,
                source_before,
                source_after: patched,
                prompt,
                llm_response: response_for(sample_index),
                build_errors: last_stderr.clone(),
                goal_states: Vec::new(),
                suggestions: Vec::new(),
                patch_applied: true,
                candidates: if record_candidates {
                    plan.records
                } else {
                    Vec::new()
                },
                accepted_sample: if record_candidates {
                    Some(sample_index)
                } else {
                    None
                },
            });

            return SessionResult::Proven {
                iterations: iteration,
            };
        }

        // All candidates failed to build. The file on disk holds the LAST tried
        // candidate, so record and feed back exactly that state.
        let (sample_index, patched, build_output) =
            last_failed.expect("non-empty try_order with no acceptance has a last failure");
        eprintln!("[proof-pilot] build failed, retrying...");

        journal.push(IterationRecord {
            index: iteration,
            source_before,
            source_after: patched,
            prompt,
            llm_response: response_for(sample_index),
            build_errors: build_output.clone(),
            goal_states: Vec::new(),
            suggestions: Vec::new(),
            patch_applied: true,
            candidates: if record_candidates {
                plan.records
            } else {
                Vec::new()
            },
            accepted_sample: None,
        });

        last_stderr = build_output;
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

    const SORRY_SOURCE: &str = "theorem foo : True := by\n  sorry\n";

    fn fenced(body: &str) -> String {
        format!("```lean\n{body}\n```")
    }

    #[test]
    fn plan_dedupes_orders_shortest_first_and_records_rejects() {
        let responses = vec![
            Ok(fenced("exact True.intro")),  // sample 0: longer proof
            Ok(fenced("trivial")),           // sample 1: shorter proof
            Ok(fenced("trivial")),           // sample 2: duplicate of 1
            Ok("no code block".to_string()), // sample 3: patcher must reject
        ];
        let plan = plan_candidates(SORRY_SOURCE, &responses, "", "Foo.lean");

        // Build order: shortest patched source first, then the longer one.
        assert_eq!(plan.try_order.len(), 2);
        assert_eq!(plan.try_order[0].0, 1);
        assert_eq!(plan.try_order[1].0, 0);
        assert!(plan.try_order[0].1.len() < plan.try_order[1].1.len());
        assert!(plan.try_order[0].1.contains("trivial"));

        // Records cover every sample, in sampling order, with final statuses for
        // duplicates and rejects.
        let statuses: Vec<&str> = plan.records.iter().map(|r| r.status.as_str()).collect();
        assert_eq!(
            statuses,
            vec!["not_tried", "not_tried", "duplicate", "patch_rejected"]
        );
        assert!(plan.records[3].build_output.starts_with("patch error:"));
    }

    #[test]
    fn plan_length_ties_break_by_sampling_order() {
        // Same length, different content — deterministic order must follow
        // sampling order, not hash order.
        let responses = vec![Ok(fenced("simp_a")), Ok(fenced("simp_b"))];
        let plan = plan_candidates(SORRY_SOURCE, &responses, "", "Foo.lean");
        assert_eq!(plan.try_order.len(), 2);
        assert_eq!(plan.try_order[0].0, 0);
        assert_eq!(plan.try_order[1].0, 1);
    }

    #[test]
    fn plan_records_request_failures_at_original_indexes() {
        // A failed concurrent sample must appear in the records at its original
        // sample_index — "the journal records every candidate" includes partial
        // sampling failures, and accepted_sample must keep referring to the
        // originally requested K samples.
        let responses = vec![
            Err(crate::backend::BackendError::RequestFailed(
                "boom".to_string(),
            )),
            Ok(fenced("trivial")),
            Ok(fenced("exact True.intro")),
        ];
        let plan = plan_candidates(SORRY_SOURCE, &responses, "", "Foo.lean");

        assert_eq!(plan.records.len(), 3);
        assert_eq!(plan.records[0].status, "request_failed");
        assert_eq!(plan.records[0].sample_index, 0);
        assert!(plan.records[0].llm_response.is_empty());
        assert!(plan.records[0].build_output.contains("boom"));
        // Surviving candidates keep their ORIGINAL indexes (1 and 2), shortest
        // first.
        assert_eq!(plan.try_order.len(), 2);
        assert_eq!(plan.try_order[0].0, 1);
        assert_eq!(plan.try_order[1].0, 2);
    }

    #[test]
    fn plan_all_rejected_yields_empty_try_order() {
        let responses = vec![Ok("nope".to_string()), Ok("also nope".to_string())];
        let plan = plan_candidates(SORRY_SOURCE, &responses, "", "Foo.lean");
        assert!(plan.try_order.is_empty());
        assert!(plan.records.iter().all(|r| r.status == "patch_rejected"));
    }

    #[test]
    fn set_candidate_status_targets_by_sample_index() {
        let responses = vec![Ok(fenced("trivial")), Ok(fenced("exact True.intro"))];
        let mut plan = plan_candidates(SORRY_SOURCE, &responses, "", "Foo.lean");
        set_candidate_status(&mut plan.records, 1, "accepted", "ok".to_string());
        assert_eq!(plan.records[1].status, "accepted");
        assert_eq!(plan.records[1].build_output, "ok");
        assert_eq!(plan.records[0].status, "not_tried");
    }

    #[test]
    fn pre_best_of_n_journal_json_still_loads() {
        // An IterationRecord serialized before the candidates/accepted_sample
        // fields existed must deserialize with defaults — the replay
        // determinism contract includes old transcripts.
        let old = r#"{
            "index": 1,
            "source_before": "a",
            "source_after": "b",
            "prompt": "p",
            "llm_response": "r",
            "build_errors": "",
            "goal_states": [],
            "suggestions": [],
            "patch_applied": true
        }"#;
        let rec: IterationRecord = serde_json::from_str(old).expect("old journal must load");
        assert!(rec.candidates.is_empty());
        assert_eq!(rec.accepted_sample, None);
    }

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
