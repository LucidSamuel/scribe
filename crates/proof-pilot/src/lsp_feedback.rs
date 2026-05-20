//! LSP-based feedback for the proof loop.
//!
//! Spawns a long-running Python bridge (`scripts/lsp-server.py`) that wraps
//! `leanclient` to provide structured diagnostics and goal states from the
//! Lean language server — replacing flat `lake build` text parsing.

use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Child, Command, Stdio};

use serde_json::Value;

/// A diagnostic from the Lean LSP.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// 0-based line number.
    pub line: usize,
    /// 0-based column.
    pub col: usize,
    /// 1 = error, 2 = warning, 3 = info, 4 = hint.
    pub severity: u8,
    pub message: String,
}

/// Proof goal state at a specific cursor position.
#[derive(Debug, Clone)]
pub struct GoalState {
    /// 0-based line number.
    pub line: usize,
    /// 0-based column.
    pub col: usize,
    /// Each string is one goal (hypotheses + turnstile + target).
    pub goals: Vec<String>,
}

/// Structured LSP feedback for a Lean file.
#[derive(Debug)]
pub struct LspFeedback {
    /// True when the file compiles without errors and without forbidden tactics.
    pub success: bool,
    pub diagnostics: Vec<Diagnostic>,
    pub goals: Vec<GoalState>,
}

/// Persistent connection to the LSP bridge process.
pub struct LspBridge {
    child: Child,
    stdin: std::process::ChildStdin,
    reader: BufReader<std::process::ChildStdout>,
}

impl LspBridge {
    /// Start the bridge, pointing it at the Lean project directory.
    pub fn new(lean_project: &Path) -> Result<Self, String> {
        let script = find_script()?;
        let project = lean_project.to_str().ok_or("non-UTF-8 project path")?;

        let mut child = Command::new("python3")
            .arg(&script)
            .arg(project)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|e| format!("spawn lsp-server.py: {e}"))?;

        let stdin = child.stdin.take().ok_or("no stdin on child")?;
        let stdout = child.stdout.take().ok_or("no stdout on child")?;
        let mut reader = BufReader::new(stdout);

        // Wait for "ready" then "initialized" signals.
        for expected in ["ready", "initialized"] {
            let mut buf = String::new();
            reader
                .read_line(&mut buf)
                .map_err(|e| format!("reading {expected}: {e}"))?;
            let val: Value =
                serde_json::from_str(buf.trim()).map_err(|e| format!("parsing {expected}: {e}"))?;
            if val.get("error").and_then(|e| e.as_str()).is_some() {
                return Err(format!(
                    "LSP bridge error: {}",
                    val["error"].as_str().unwrap()
                ));
            }
            if val.get("status").and_then(|s| s.as_str()) != Some(expected) {
                return Err(format!("expected status={expected}, got: {buf}"));
            }
            eprintln!("[proof-pilot] LSP bridge: {expected}");
        }

        Ok(Self {
            child,
            stdin,
            reader,
        })
    }

    /// Get feedback for a file that was just written to disk.
    ///
    /// Closes and re-opens the file in the LSP so it reads the new content.
    pub fn feedback_after_update(&mut self, file: &str) -> Result<LspFeedback, String> {
        self.call(&serde_json::json!({"cmd": "update", "file": file}))
    }

    /// Get feedback for a file (auto-opens if needed).
    pub fn feedback(&mut self, file: &str) -> Result<LspFeedback, String> {
        self.call(&serde_json::json!({"cmd": "feedback", "file": file}))
    }

    fn call(&mut self, cmd: &Value) -> Result<LspFeedback, String> {
        let line = serde_json::to_string(cmd).map_err(|e| format!("serialize: {e}"))?;
        writeln!(self.stdin, "{line}").map_err(|e| format!("write: {e}"))?;
        self.stdin.flush().map_err(|e| format!("flush: {e}"))?;

        let mut buf = String::new();
        self.reader
            .read_line(&mut buf)
            .map_err(|e| format!("read response: {e}"))?;

        parse_feedback(buf.trim())
    }
}

impl Drop for LspBridge {
    fn drop(&mut self) {
        let _ = writeln!(self.stdin, r#"{{"cmd":"quit"}}"#);
        let _ = self.stdin.flush();
        let _ = self.child.wait();
    }
}

fn find_script() -> Result<String, String> {
    let candidates = [
        "scripts/lsp-server.py",
        "../scripts/lsp-server.py",
        "../../scripts/lsp-server.py",
    ];
    for c in &candidates {
        if Path::new(c).exists() {
            return Ok(c.to_string());
        }
    }
    Err("could not find scripts/lsp-server.py — run from the repo root".to_string())
}

fn parse_feedback(json_str: &str) -> Result<LspFeedback, String> {
    let val: Value =
        serde_json::from_str(json_str).map_err(|e| format!("parse feedback JSON: {e}"))?;

    if let Some(err) = val.get("error").and_then(|e| e.as_str()) {
        return Err(format!("LSP: {err}"));
    }

    let success = val["success"].as_bool().unwrap_or(false);

    let diagnostics = val["diagnostics"]
        .as_array()
        .map(|arr| {
            arr.iter()
                .map(|d| Diagnostic {
                    line: d["line"].as_u64().unwrap_or(0) as usize,
                    col: d["col"].as_u64().unwrap_or(0) as usize,
                    severity: d["severity"].as_u64().unwrap_or(1) as u8,
                    message: d["message"].as_str().unwrap_or("").to_string(),
                })
                .collect()
        })
        .unwrap_or_default();

    let goals = val["goals"]
        .as_array()
        .map(|arr| {
            arr.iter()
                .map(|g| {
                    let goal_strings = g["goals"]
                        .as_array()
                        .map(|gs| {
                            gs.iter()
                                .filter_map(|s| s.as_str().map(String::from))
                                .collect()
                        })
                        .unwrap_or_default();
                    GoalState {
                        line: g["line"].as_u64().unwrap_or(0) as usize,
                        col: g["col"].as_u64().unwrap_or(0) as usize,
                        goals: goal_strings,
                    }
                })
                .collect()
        })
        .unwrap_or_default();

    Ok(LspFeedback {
        success,
        diagnostics,
        goals,
    })
}

/// Format LSP feedback into a prompt section for Claude.
///
/// Replaces the old flat "--- build errors ---" section with structured
/// diagnostics and proof state.
pub fn format_lsp_feedback(feedback: &LspFeedback) -> String {
    let mut out = String::new();

    if feedback.diagnostics.is_empty() && feedback.goals.is_empty() {
        out.push_str("No diagnostics or goals reported.\n");
        return out;
    }

    // Diagnostics — only errors and forbidden-tactic warnings (skip noise)
    let relevant: Vec<_> = feedback
        .diagnostics
        .iter()
        .filter(|d| d.severity == 1 || (d.severity == 2 && message_mentions_forbidden(&d.message)))
        .collect();

    if !relevant.is_empty() {
        out.push_str("--- diagnostics ---\n");
        for d in &relevant {
            let tag = if d.severity == 1 { "ERROR" } else { "WARNING" };
            // Display as 1-based lines for readability
            out.push_str(&format!(
                "[{tag}] line {}:{}: {}\n",
                d.line + 1,
                d.col,
                d.message.lines().next().unwrap_or("")
            ));
        }
        out.push('\n');
    }

    // Goal states — the high-value signal
    if !feedback.goals.is_empty() {
        out.push_str("--- proof state (Lean LSP) ---\n");
        for g in &feedback.goals {
            out.push_str(&format!("At line {}:\n", g.line + 1));
            for goal in &g.goals {
                out.push_str(goal);
                out.push('\n');
            }
            out.push('\n');
        }
    }

    out
}

/// Convert LSP feedback to a flat string compatible with the old build-error format.
///
/// Used by the patcher to find diagnostic line numbers.
pub fn feedback_as_build_output(feedback: &LspFeedback, target_file: &str) -> String {
    let basename = Path::new(target_file)
        .file_name()
        .and_then(|f| f.to_str())
        .unwrap_or(target_file);

    feedback
        .diagnostics
        .iter()
        .filter(|d| d.severity <= 2)
        .map(|d| {
            format!(
                "{}:{}:{}: {}",
                basename,
                d.line + 1,
                d.col,
                d.message.lines().next().unwrap_or("")
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Check if any diagnostic mentions forbidden tactics for a specific file.
pub fn has_forbidden_in_feedback(feedback: &LspFeedback) -> bool {
    feedback
        .diagnostics
        .iter()
        .any(|d| d.severity == 2 && message_mentions_forbidden(&d.message))
}

fn message_mentions_forbidden(message: &str) -> bool {
    const FORBIDDEN: &[&str] = &["sorry", "axiom", "native_decide"];
    let lower = message.to_lowercase();
    FORBIDDEN.iter().any(|kw| lower.contains(kw))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_forbidden_warnings_beyond_sorry() {
        let feedback = LspFeedback {
            success: false,
            diagnostics: vec![
                Diagnostic {
                    line: 4,
                    col: 2,
                    severity: 2,
                    message: "declaration uses `axiom`".to_string(),
                },
                Diagnostic {
                    line: 5,
                    col: 2,
                    severity: 2,
                    message: "declaration uses `native_decide`".to_string(),
                },
            ],
            goals: vec![],
        };

        let rendered = format_lsp_feedback(&feedback);
        assert!(rendered.contains("axiom"));
        assert!(rendered.contains("native_decide"));
        assert!(has_forbidden_in_feedback(&feedback));
    }
}
