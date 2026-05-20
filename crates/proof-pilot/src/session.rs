use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::Command;

use crate::lean_runner::{has_forbidden_tactics, run_lake_build};
use crate::lsp_feedback::{
    feedback_as_build_output, format_lsp_feedback, has_forbidden_in_feedback, LspBridge,
    LspFeedback,
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
    /// Model to use (e.g. "claude-sonnet-4-20250514").
    pub model: String,
    /// System prompt text for Claude (read from file by caller).
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

/// Run a proof completion session.
///
/// Loop: read lean file → get feedback (LSP or lake build) → send to Claude →
/// get patch → apply → verify → repeat until green or budget exhausted.
pub fn run(config: &SessionConfig) -> SessionResult {
    if config.use_lsp {
        run_with_lsp(config)
    } else {
        run_with_lake_build(config)
    }
}

// ─── LSP-based feedback loop ────────────────────────────────────────────────

fn run_with_lsp(config: &SessionConfig) -> SessionResult {
    let lean_path = Path::new(&config.lean_file);
    let lake_dir = Path::new(&config.lake_dir);

    let mut log = open_log(config);
    log_line(
        &mut log,
        &format!(
            "=== proof-pilot session (LSP mode) ===\nfile: {}\nmodel: {}\nmax_iters: {}\n",
            config.lean_file, config.model, config.max_iterations
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
            return run_with_lake_build(config);
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
        match run_lake_build(lake_dir) {
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
        last_feedback = FeedbackSource::Lsp(initial_feedback);
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

        let source = match fs::read_to_string(lean_path) {
            Ok(s) => s,
            Err(e) => return SessionResult::Failed(format!("read {}: {e}", config.lean_file)),
        };

        // Build prompt with structured LSP feedback
        let prompt = build_lsp_prompt(&config.lean_file, &source, &last_feedback, iteration);
        log_line(&mut log, &format!("[prompt]\n{}\n", prompt));

        let llm_response =
            match call_claude(&prompt, &config.model, config.system_prompt.as_deref()) {
                Ok(r) => r,
                Err(e) => return SessionResult::Failed(format!("claude cli: {e}")),
            };
        log_line(&mut log, &format!("[llm response]\n{}\n", llm_response));

        // Apply patch — use synthetic build output for the patcher's diagnostic targeting
        let build_output = last_feedback.build_output_for_patcher(&config.lean_file);
        let patched = match apply_patch_with_diagnostics(
            &source,
            &llm_response,
            &build_output,
            Some(&config.lean_file),
        ) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("[proof-pilot] patch rejected: {e}");
                log_line(&mut log, &format!("[patch] REJECTED: {e}\n"));
                continue;
            }
        };
        log_line(&mut log, &format!("[patched file]\n{}\n", patched));

        // Write patched file to disk
        if let Err(e) = fs::write(lean_path, &patched) {
            return SessionResult::Failed(format!("write {}: {e}", config.lean_file));
        }

        // Get fresh LSP feedback (close + reopen to pick up disk changes)
        match lsp.feedback_after_update(&rel_path) {
            Ok(fb) => {
                if fb.success && !has_forbidden_in_feedback(&fb) {
                    eprintln!("[proof-pilot] proof accepted at iteration {iteration} (LSP)");
                    log_line(
                        &mut log,
                        &format!("[build] SUCCESS at iteration {iteration}\n"),
                    );

                    // Final verification with lake build (belt + suspenders)
                    match run_lake_build(lake_dir) {
                        Ok(r)
                            if r.success
                                && !has_forbidden_tactics(&r.combined, Some(&config.lean_file)) =>
                        {
                            return SessionResult::Proven {
                                iterations: iteration,
                            };
                        }
                        Ok(r) => {
                            eprintln!(
                                "[proof-pilot] LSP said OK but lake build disagrees, continuing..."
                            );
                            log_line(
                                &mut log,
                                &format!("[build] LSP/lake mismatch\n{}\n", r.combined),
                            );
                            last_feedback = FeedbackSource::BuildOutput(r.combined);
                        }
                        Err(e) => return SessionResult::Failed(format!("lake build verify: {e}")),
                    }
                } else {
                    eprintln!("[proof-pilot] build failed (LSP), retrying...");
                    log_line(
                        &mut log,
                        &format!("[build] FAIL\n{}\n", format_lsp_feedback(&fb)),
                    );
                    last_feedback = FeedbackSource::Lsp(fb);
                }
            }
            Err(e) => {
                eprintln!("[proof-pilot] LSP feedback error: {e}, using lake build fallback");
                // Fall back to lake build for this iteration
                match run_lake_build(lake_dir) {
                    Ok(r)
                        if r.success
                            && !has_forbidden_tactics(&r.combined, Some(&config.lean_file)) =>
                    {
                        return SessionResult::Proven {
                            iterations: iteration,
                        };
                    }
                    Ok(r) => {
                        log_line(
                            &mut log,
                            &format!("[build] FAIL (fallback)\n{}\n", r.combined),
                        );
                        last_feedback = FeedbackSource::BuildOutput(r.combined);
                    }
                    Err(e) => return SessionResult::Failed(format!("lake build: {e}")),
                }
            }
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
    Lsp(LspFeedback),
    BuildOutput(String),
}

impl FeedbackSource {
    fn prompt_section(&self) -> String {
        match self {
            FeedbackSource::Lsp(feedback) => format_lsp_feedback(feedback),
            FeedbackSource::BuildOutput(output) => {
                format!("--- build errors (lake fallback) ---\n{output}")
            }
        }
    }

    fn build_output_for_patcher(&self, target_file: &str) -> String {
        match self {
            FeedbackSource::Lsp(feedback) => feedback_as_build_output(feedback, target_file),
            FeedbackSource::BuildOutput(output) => output.clone(),
        }
    }

    fn last_error(&self) -> String {
        match self {
            FeedbackSource::Lsp(feedback) => format_lsp_feedback(feedback),
            FeedbackSource::BuildOutput(output) => output.clone(),
        }
    }
}

// ─── Original lake-build feedback loop (unchanged) ──────────────────────────

fn run_with_lake_build(config: &SessionConfig) -> SessionResult {
    let lean_path = Path::new(&config.lean_file);
    let lake_dir = Path::new(&config.lake_dir);

    let mut log = open_log(config);
    log_line(
        &mut log,
        &format!(
            "=== proof-pilot session ===\nfile: {}\nmodel: {}\nmax_iters: {}\n",
            config.lean_file, config.model, config.max_iterations
        ),
    );

    // Initial build to get starting errors
    let mut last_stderr = match run_lake_build(lake_dir) {
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
        let source = match fs::read_to_string(lean_path) {
            Ok(s) => s,
            Err(e) => return SessionResult::Failed(format!("read {}: {}", config.lean_file, e)),
        };

        // Build prompt for Claude
        let prompt = build_prompt(&config.lean_file, &source, &last_stderr, iteration);

        log_line(&mut log, &format!("[prompt]\n{}\n", prompt));

        // Call Claude CLI
        let llm_response =
            match call_claude(&prompt, &config.model, config.system_prompt.as_deref()) {
                Ok(r) => r,
                Err(e) => return SessionResult::Failed(format!("claude cli: {}", e)),
            };

        log_line(&mut log, &format!("[llm response]\n{}\n", llm_response));

        // Apply patch
        let patched = match apply_patch_with_diagnostics(
            &source,
            &llm_response,
            &last_stderr,
            Some(&config.lean_file),
        ) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("[proof-pilot] patch rejected: {}", e);
                log_line(&mut log, &format!("[patch] REJECTED: {}\n", e));
                last_stderr = format!("(patch error: {})\n{}", e, last_stderr);
                continue;
            }
        };

        log_line(&mut log, &format!("[patched file]\n{}\n", patched));

        // Write patched file
        if let Err(e) = fs::write(lean_path, &patched) {
            return SessionResult::Failed(format!("write {}: {}", config.lean_file, e));
        }

        // Rebuild
        match run_lake_build(lake_dir) {
            Ok(r) if r.success && !has_forbidden_tactics(&r.combined, Some(&config.lean_file)) => {
                eprintln!("[proof-pilot] proof accepted at iteration {}", iteration);
                log_line(
                    &mut log,
                    &format!("[build] SUCCESS at iteration {}\n", iteration),
                );
                return SessionResult::Proven {
                    iterations: iteration,
                };
            }
            Ok(r) => {
                eprintln!("[proof-pilot] build failed, retrying...");
                log_line(&mut log, &format!("[build] FAIL\n{}\n", r.combined));
                last_stderr = r.combined;
            }
            Err(e) => return SessionResult::Failed(format!("lake build: {}", e)),
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

/// Shell out to `claude` CLI and return stdout.
fn call_claude(
    prompt: &str,
    model: &str,
    system_prompt: Option<&str>,
) -> Result<String, std::io::Error> {
    let mut cmd = Command::new("claude");
    cmd.env_remove("CLAUDECODE")
        .arg("-p")
        .arg(prompt)
        .arg("--model")
        .arg(model);

    if let Some(sp) = system_prompt {
        cmd.arg("--system-prompt").arg(sp);
    }

    let output = cmd.output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(std::io::Error::other(format!(
            "claude exited {}: {}",
            output.status, stderr
        )));
    }

    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
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
}
