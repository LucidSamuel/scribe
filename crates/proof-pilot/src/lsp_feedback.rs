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

/// A search result from loogle.
#[derive(Debug, Clone)]
pub struct SearchResult {
    pub name: String,
    pub type_sig: String,
    pub module: String,
}

/// Result of probing a single tactic at a position.
#[derive(Debug, Clone)]
pub struct ProbeResult {
    pub tactic: String,
    /// "solved", "progress", "failed", or "error"
    pub status: String,
    /// Remaining goals after the tactic (if progress or solved).
    pub remaining_goals: Vec<String>,
    /// Error message (if failed).
    pub error: Option<String>,
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

    /// Search Mathlib via loogle for lemmas matching a query.
    pub fn search(&mut self, query: &str, num_results: usize) -> Result<Vec<SearchResult>, String> {
        let cmd = serde_json::json!({
            "cmd": "search",
            "query": query,
            "num_results": num_results,
        });
        let line = serde_json::to_string(&cmd).map_err(|e| format!("serialize: {e}"))?;
        writeln!(self.stdin, "{line}").map_err(|e| format!("write: {e}"))?;
        self.stdin.flush().map_err(|e| format!("flush: {e}"))?;

        let mut buf = String::new();
        self.reader
            .read_line(&mut buf)
            .map_err(|e| format!("read: {e}"))?;

        parse_search_response(buf.trim())
    }

    /// Try multiple tactics at a position and report which ones make progress.
    pub fn probe(
        &mut self,
        file: &str,
        line: usize,
        col: usize,
        tactics: &[&str],
    ) -> Result<Vec<ProbeResult>, String> {
        let cmd = serde_json::json!({
            "cmd": "probe",
            "file": file,
            "line": line,
            "col": col,
            "tactics": tactics,
        });
        let json_line = serde_json::to_string(&cmd).map_err(|e| format!("serialize: {e}"))?;
        writeln!(self.stdin, "{json_line}").map_err(|e| format!("write: {e}"))?;
        self.stdin.flush().map_err(|e| format!("flush: {e}"))?;

        let mut buf = String::new();
        self.reader
            .read_line(&mut buf)
            .map_err(|e| format!("read: {e}"))?;

        let val: Value =
            serde_json::from_str(buf.trim()).map_err(|e| format!("parse probe: {e}"))?;

        if let Some(err) = val.get("error").and_then(|e| e.as_str()) {
            return Err(format!("probe: {err}"));
        }

        val["results"]
            .as_array()
            .map(|arr| {
                arr.iter()
                    .map(|r| ProbeResult {
                        tactic: r["tactic"].as_str().unwrap_or("").to_string(),
                        status: r["status"].as_str().unwrap_or("error").to_string(),
                        remaining_goals: r["remaining_goals"]
                            .as_array()
                            .map(|gs| {
                                gs.iter()
                                    .filter_map(|s| s.as_str().map(String::from))
                                    .collect()
                            })
                            .unwrap_or_default(),
                        error: r["error"].as_str().map(String::from),
                    })
                    .collect()
            })
            .ok_or_else(|| "no results array in probe response".to_string())
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

/// The Python LSP bridge, embedded so the published crate is self-contained.
/// (The canonical copy lives in the crate at scripts/lsp-server.py; the scribe
/// repo also keeps one at the repo root for direct use.)
const LSP_SERVER_SOURCE: &str = include_str!("../scripts/lsp-server.py");

fn find_script() -> Result<String, String> {
    // Explicit override, then repo-local copies (development), then the
    // embedded source materialized into a stable per-user temp path.
    if let Ok(path) = std::env::var("PROOF_PILOT_LSP_SERVER") {
        if Path::new(&path).exists() {
            return Ok(path);
        }
        return Err(format!(
            "PROOF_PILOT_LSP_SERVER points at a missing file: {path}"
        ));
    }
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
    let dir = std::env::temp_dir().join("proof-pilot");
    std::fs::create_dir_all(&dir).map_err(|e| format!("create {}: {e}", dir.display()))?;
    let path = dir.join("lsp-server.py");
    std::fs::write(&path, LSP_SERVER_SOURCE)
        .map_err(|e| format!("write embedded lsp-server.py: {e}"))?;
    Ok(path.to_string_lossy().into_owned())
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

fn parse_search_response(json_str: &str) -> Result<Vec<SearchResult>, String> {
    let val: Value = serde_json::from_str(json_str).map_err(|e| format!("parse search: {e}"))?;

    if let Some(err) = val.get("error").and_then(|e| e.as_str()) {
        if !err.is_empty() {
            return Err(format!("loogle: {err}"));
        }
    }

    val["results"]
        .as_array()
        .map(|arr| {
            arr.iter()
                .map(|r| SearchResult {
                    name: r["name"].as_str().unwrap_or("").to_string(),
                    type_sig: r["type"].as_str().unwrap_or("").to_string(),
                    module: r["module"].as_str().unwrap_or("").to_string(),
                })
                .collect()
        })
        .ok_or_else(|| "no results array in search response".to_string())
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

// ─── Error-to-suggestion heuristics ─────────────────────────────────────────

/// Analyze diagnostics and generate actionable suggestions for the LLM.
///
/// Pattern-matches on common Lean error messages and provides concrete
/// fix suggestions. This compensates for models that keep reaching for
/// tactics that don't work on ZMod p.
pub fn error_suggestions(feedback: &LspFeedback) -> Vec<String> {
    let mut suggestions = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();

    for d in &feedback.diagnostics {
        if d.severity != 1 {
            continue;
        }
        let msg = &d.message;

        // linarith on ZMod p
        if msg.contains("linarith failed") {
            let s = "linarith does not work on ZMod p (not linearly ordered). \
                     Use `linear_combination` instead. For `h : a - b = 0`, \
                     try `linear_combination h` to get `a = b`."
                .to_string();
            if seen.insert(s.clone()) {
                suggestions.push(s);
            }
        }

        // unknown tactic — usually a missing import
        if msg.contains("unknown tactic") {
            if let Some(tactic_name) = extract_quoted(msg) {
                let s = format!(
                    "`{tactic_name}` is not available. Check imports: {}",
                    suggest_import(&tactic_name)
                );
                if seen.insert(s.clone()) {
                    suggestions.push(s);
                }
            }
        }

        // omega on ZMod p
        if msg.contains("omega") && msg.contains("failed") {
            let s = "omega only works on Nat/Int, not ZMod p. \
                     Use `ring`, `linear_combination`, or `field_simp` instead."
                .to_string();
            if seen.insert(s.clone()) {
                suggestions.push(s);
            }
        }

        // type mismatch with ZMod
        if msg.contains("type mismatch") && msg.contains("ZMod") {
            let s = "Type mismatch in ZMod p context. Ensure numeric literals are \
                     cast: `(42 : ZMod p)`. Check that all terms have matching types."
                .to_string();
            if seen.insert(s.clone()) {
                suggestions.push(s);
            }
        }

        // ring failed — usually the goal isn't a pure polynomial identity
        if msg.contains("ring_nf") && msg.contains("failed") || msg.contains("Try this: ring_nf") {
            let s = "ring/ring_nf failed — the goal is not a pure polynomial identity. \
                     You may need to `rw` hypotheses into the goal first, or use \
                     `linear_combination` with appropriate hypothesis coefficients."
                .to_string();
            if seen.insert(s.clone()) {
                suggestions.push(s);
            }
        }
    }

    suggestions
}

/// Build a loogle search query from the goal state.
///
/// Extracts the goal target (after ⊢) and hypothesis types to form a
/// query that helps find relevant Mathlib lemmas.
pub fn goal_to_search_query(goal_state: &str) -> Option<String> {
    // Find the turnstile and extract the goal target
    let target = goal_state
        .lines()
        .find(|l| l.trim_start().starts_with('⊢'))
        .map(|l| l.trim_start().trim_start_matches('⊢').trim())?;

    // Simplify for loogle: keep the core structure
    let query = target.to_string();
    if query.is_empty() {
        return None;
    }
    Some(query)
}

fn extract_quoted(msg: &str) -> Option<String> {
    // Match `backtick` or 'single-quoted' identifiers
    let start = msg.find('`').or_else(|| msg.find('\''))?;
    let delim = msg.as_bytes()[start] as char;
    let rest = &msg[start + 1..];
    let end = rest.find(delim)?;
    Some(rest[..end].to_string())
}

fn suggest_import(tactic: &str) -> &'static str {
    match tactic {
        "linarith" => "add `import Mathlib.Tactic.Linarith`",
        "linear_combination" => "add `import Mathlib.Tactic.LinearCombination`",
        "ring" | "ring_nf" => "add `import Mathlib.Tactic.Ring`",
        "field_simp" => "add `import Mathlib.Tactic.FieldSimp`",
        "simp" | "simp_all" => "add `import Mathlib.Tactic.Simp`",
        "omega" => "add `import Mathlib.Tactic.Omega`",
        "norm_num" => "add `import Mathlib.Tactic.NormNum`",
        "positivity" => "add `import Mathlib.Tactic.Positivity`",
        "polyrith" => "add `import Mathlib.Tactic.Polyrith`",
        "decide" => "this tactic may not be suitable for ZMod p",
        _ => "check that the required Mathlib module is imported",
    }
}

/// Format search results for inclusion in a prompt.
pub fn format_search_results(results: &[SearchResult]) -> String {
    if results.is_empty() {
        return String::new();
    }
    let mut out = String::from("--- relevant Mathlib lemmas (loogle) ---\n");
    for r in results {
        out.push_str(&format!("{} : {}\n", r.name, r.type_sig));
    }
    out.push('\n');
    out
}

/// Format probe results for inclusion in a prompt.
pub fn format_probe_results(results: &[ProbeResult]) -> String {
    if results.is_empty() {
        return String::new();
    }

    let any_progress = results
        .iter()
        .any(|r| r.status == "solved" || r.status == "progress");
    if !any_progress {
        return String::new();
    }

    let mut out = String::from("--- tactic probe results ---\n");
    for r in results {
        match r.status.as_str() {
            "solved" => {
                out.push_str(&format!("  `{}` — CLOSES THE GOAL\n", r.tactic));
            }
            "progress" => {
                out.push_str(&format!("  `{}` — makes progress", r.tactic));
                if !r.remaining_goals.is_empty() {
                    out.push_str(&format!(" ({} goal(s) remaining)", r.remaining_goals.len()));
                }
                out.push('\n');
            }
            _ => {}
        }
    }
    out.push('\n');
    out
}

/// Format error suggestions for inclusion in a prompt.
pub fn format_suggestions(suggestions: &[String]) -> String {
    if suggestions.is_empty() {
        return String::new();
    }
    let mut out = String::from("--- hints ---\n");
    for s in suggestions {
        out.push_str(&format!("- {s}\n"));
    }
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linarith_heuristic_fires() {
        let feedback = LspFeedback {
            success: false,
            diagnostics: vec![Diagnostic {
                line: 5,
                col: 4,
                severity: 1,
                message: "linarith failed to find a contradiction\ncase ...\n".to_string(),
            }],
            goals: vec![],
        };
        let suggestions = error_suggestions(&feedback);
        assert!(suggestions.iter().any(|s| s.contains("linear_combination")));
    }

    #[test]
    fn unknown_tactic_suggests_import() {
        let feedback = LspFeedback {
            success: false,
            diagnostics: vec![Diagnostic {
                line: 5,
                col: 4,
                severity: 1,
                message: "unknown tactic `linarith`".to_string(),
            }],
            goals: vec![],
        };
        let suggestions = error_suggestions(&feedback);
        assert!(suggestions
            .iter()
            .any(|s| s.contains("Mathlib.Tactic.Linarith")));
    }

    #[test]
    fn unknown_tactic_suggestions_deduplicate_owned_strings() {
        let feedback = LspFeedback {
            success: false,
            diagnostics: vec![
                Diagnostic {
                    line: 5,
                    col: 4,
                    severity: 1,
                    message: "unknown tactic `linarith`".to_string(),
                },
                Diagnostic {
                    line: 6,
                    col: 4,
                    severity: 1,
                    message: "unknown tactic `linarith`".to_string(),
                },
            ],
            goals: vec![],
        };

        let suggestions = error_suggestions(&feedback);
        assert_eq!(suggestions.len(), 1);
    }

    #[test]
    fn search_response_error_wins_over_empty_results() {
        let err = parse_search_response(r#"{"results":[],"error":"loogle unavailable"}"#)
            .expect_err("search errors must not be treated as empty results");

        assert!(err.contains("loogle unavailable"));
    }

    #[test]
    fn goal_to_search_query_extracts_target() {
        let state = "x : ZMod p\nh : x * x - x = 0\n⊢ x = 0 ∨ x = 1";
        let query = goal_to_search_query(state).unwrap();
        assert_eq!(query, "x = 0 ∨ x = 1");
    }

    #[test]
    fn probe_results_format_shows_progress() {
        let results = vec![
            ProbeResult {
                tactic: "ring".to_string(),
                status: "failed".to_string(),
                remaining_goals: vec![],
                error: Some("ring failed".to_string()),
            },
            ProbeResult {
                tactic: "simp".to_string(),
                status: "progress".to_string(),
                remaining_goals: vec!["⊢ True".to_string()],
                error: None,
            },
        ];
        let formatted = format_probe_results(&results);
        assert!(formatted.contains("`simp` — makes progress"));
        assert!(!formatted.contains("ring")); // failed tactics excluded
    }

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
