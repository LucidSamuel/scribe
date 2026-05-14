use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::Command;

use crate::lean_runner::{has_forbidden_tactics, run_lake_build};
use crate::patcher::apply_patch;

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
    /// Path to the system prompt file for Claude.
    pub system_prompt: Option<String>,
    /// Optional path for transcript log. If set, every iteration is logged.
    pub transcript: Option<String>,
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
/// Loop: read lean file → send to Claude CLI with build errors →
/// get patch → apply → rebuild → repeat until green or budget exhausted.
pub fn run(config: &SessionConfig) -> SessionResult {
    let lean_path = Path::new(&config.lean_file);
    let lake_dir = Path::new(&config.lake_dir);

    let mut log = config.transcript.as_ref().and_then(|p| {
        fs::File::create(p)
            .map_err(|e| eprintln!("[proof-pilot] warning: could not create transcript: {}", e))
            .ok()
    });

    log_line(&mut log, &format!("=== proof-pilot session ===\nfile: {}\nmodel: {}\nmax_iters: {}\n",
        config.lean_file, config.model, config.max_iterations));

    // Initial build to get starting errors
    let mut last_stderr = match run_lake_build(lake_dir) {
        Ok(r) if r.success && !has_forbidden_tactics(&r.combined) => {
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
        eprintln!("[proof-pilot] iteration {}/{}", iteration, config.max_iterations);
        log_line(&mut log, &format!("--- iteration {}/{} ---\n", iteration, config.max_iterations));

        // Read current source
        let source = match fs::read_to_string(lean_path) {
            Ok(s) => s,
            Err(e) => return SessionResult::Failed(format!("read {}: {}", config.lean_file, e)),
        };

        // Build prompt for Claude
        let prompt = format!(
            "The following Lean 4 file fails to build. \
             Replace the proof body (everything after `:= by`) so that `lake build` passes \
             with zero errors and zero `sorry`. Do NOT change the theorem statement. \
             You may add `import` lines at the top of the code block if needed. \
             Reply with a single fenced code block containing only the proof body \
             (optionally preceded by import lines).\n\n\
             --- file: {} ---\n{}\n\n--- build errors ---\n{}",
            config.lean_file, source, last_stderr
        );

        log_line(&mut log, &format!("[prompt]\n{}\n", prompt));

        // Call Claude CLI
        let llm_response = match call_claude(&prompt, &config.model, config.system_prompt.as_deref()) {
            Ok(r) => r,
            Err(e) => return SessionResult::Failed(format!("claude cli: {}", e)),
        };

        log_line(&mut log, &format!("[llm response]\n{}\n", llm_response));

        // Apply patch
        let patched = match apply_patch(&source, &llm_response) {
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
            Ok(r) if r.success && !has_forbidden_tactics(&r.combined) => {
                eprintln!("[proof-pilot] proof accepted at iteration {}", iteration);
                log_line(&mut log, &format!("[build] SUCCESS at iteration {}\n", iteration));
                return SessionResult::Proven { iterations: iteration };
            }
            Ok(r) => {
                eprintln!("[proof-pilot] build failed, retrying...");
                log_line(&mut log, &format!("[build] FAIL\n{}\n", r.combined));
                last_stderr = r.combined;
            }
            Err(e) => return SessionResult::Failed(format!("lake build: {}", e)),
        }
    }

    log_line(&mut log, &format!("[result] EXHAUSTED after {} iterations\n", config.max_iterations));

    SessionResult::Exhausted {
        iterations: config.max_iterations,
        last_error: last_stderr,
    }
}

fn log_line(log: &mut Option<fs::File>, msg: &str) {
    if let Some(f) = log.as_mut() {
        let _ = f.write_all(msg.as_bytes());
        let _ = f.flush();
    }
}

/// Shell out to `claude` CLI and return stdout.
fn call_claude(prompt: &str, model: &str, system_prompt: Option<&str>) -> Result<String, std::io::Error> {
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
        return Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("claude exited {}: {}", output.status, stderr),
        ));
    }

    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}
