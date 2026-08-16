//! `scribe golf` — zkGolf competition mode (Phase 1: prove-only pipeline).
//!
//! Drives proof-pilot against an EXTERNAL lake project (the zk-golf-challenges
//! checkout) instead of scribe's own `lean/` tree. A zkGolf solution is a set
//! of five pinned theorems (`configs/<Instance>.json` → `theorem_names`); each
//! obligation lives in its own file so the proof loop can close them one at a
//! time (proof-pilot's success criterion is per-file).
//!
//! Subcommands:
//!   init   <slug>  — resolve the challenge, record state under golf/<slug>/
//!   status <slug>  — render the obligation board from source + attempt journals
//!   prove  <slug>  — run the proof loop over pending obligations
//!   check  <slug>  — submission gate: guards + green build + axiom audit + score
//!   list           — enumerate challenges and local progress

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use proof_pilot::backend::make_backend;
use proof_pilot::journal::SessionJournal;
use proof_pilot::lean_runner::forbidden_source_token;
use proof_pilot::session::{self, SessionConfig, SessionResult};
use proof_pilot::transcript;

// ── CLI args ─────────────────────────────────────────────────────────────────

#[derive(clap::Args)]
pub struct GolfArgs {
    #[command(subcommand)]
    pub command: GolfCommand,
}

#[derive(clap::Subcommand)]
pub enum GolfCommand {
    /// Resolve a challenge and record its state under golf/<slug>/.
    Init {
        /// Challenge slug (e.g. assert-bytes, gf2-k12-compress-canonical).
        slug: String,
        /// Path to the zk-golf-challenges lake project (a warm checkout).
        /// Default: $SCRIBE_GOLF_PROJECT, then corpus/zk-golf-challenges.
        #[arg(long, value_name = "DIR")]
        project: Option<String>,
    },
    /// Render the obligation board for a challenge.
    Status { slug: String },
    /// Run the LLM proof loop over pending obligations (those whose proof
    /// still contains `sorry`), one at a time in config order.
    Prove {
        slug: String,
        /// Only attempt this obligation (short name, e.g. soundness).
        #[arg(long, value_name = "NAME")]
        obligation: Option<String>,
        /// Per-obligation iteration budget.
        #[arg(long, default_value_t = 8)]
        max_iterations: u32,
        /// Backend: claude | anthropic | openai | leanstral | openai-compat.
        #[arg(long, default_value = "claude")]
        backend: String,
        /// Model override for the chosen backend.
        #[arg(long)]
        model: Option<String>,
        /// Use the Lean LSP bridge for structured feedback.
        #[arg(long)]
        lsp: bool,
        /// Best-of-n samples per iteration (lake-build mode only).
        #[arg(long, default_value_t = 1)]
        samples: u32,
    },
    /// Submission gate: forbidden tokens, heartbeat cap, toolchain diff,
    /// green build with no sorry warnings, axiom audit, score extraction.
    Check {
        slug: String,
        /// Maximum permitted `set_option maxHeartbeats` value.
        #[arg(long, default_value_t = 4_000_000)]
        max_heartbeats: u64,
    },
    /// List challenges in the project and local progress.
    List {
        #[arg(long, value_name = "DIR")]
        project: Option<String>,
    },
}

pub fn run(args: GolfArgs) {
    ensure_lake_on_path();
    let code = match args.command {
        GolfCommand::Init { slug, project } => cmd_init(&slug, project.as_deref()),
        GolfCommand::Status { slug } => cmd_status(&slug),
        GolfCommand::Prove {
            slug,
            obligation,
            max_iterations,
            backend,
            model,
            lsp,
            samples,
        } => cmd_prove(
            &slug,
            obligation.as_deref(),
            max_iterations,
            &backend,
            model,
            lsp,
            samples,
        ),
        GolfCommand::Check {
            slug,
            max_heartbeats,
        } => cmd_check(&slug, max_heartbeats),
        GolfCommand::List { project } => cmd_list(project.as_deref()),
    };
    std::process::exit(code);
}

// ── State ────────────────────────────────────────────────────────────────────

#[derive(serde::Serialize, serde::Deserialize, Clone)]
struct GolfState {
    slug: String,
    instance: String,
    project: String,
    namespace: String,
    solution_module: String,
    /// Fully-qualified theorem names, in config order.
    theorems: Vec<String>,
    permitted_axioms: Vec<String>,
}

impl GolfState {
    fn obligations(&self) -> Vec<String> {
        self.theorems
            .iter()
            .map(|t| t.rsplit('.').next().unwrap_or(t).to_string())
            .collect()
    }

    fn solution_dir(&self) -> PathBuf {
        Path::new(&self.project).join("Solution").join(&self.instance)
    }

    fn instance_dir(&self) -> PathBuf {
        Path::new(&self.project)
            .join("Challenge/Instances")
            .join(&self.instance)
    }
}

fn state_dir(slug: &str) -> PathBuf {
    Path::new("golf").join(slug)
}

fn load_state(slug: &str) -> Result<GolfState, String> {
    let path = state_dir(slug).join("state.json");
    let text = fs::read_to_string(&path)
        .map_err(|e| format!("no state for '{slug}' ({}): run `scribe golf init {slug}` first", e))?;
    serde_json::from_str(&text).map_err(|e| format!("corrupt {}: {e}", path.display()))
}

fn resolve_project(explicit: Option<&str>) -> String {
    explicit
        .map(str::to_string)
        .or_else(|| std::env::var("SCRIBE_GOLF_PROJECT").ok())
        .unwrap_or_else(|| "corpus/zk-golf-challenges".to_string())
}

/// proof-pilot invokes bare `lake`; make sure it resolves even when the shell
/// PATH misses ~/.elan/bin. Detection scans PATH entries rather than running
/// `lake` — executing the elan shim outside a lake project can trigger a
/// toolchain download.
fn ensure_lake_on_path() {
    let path = std::env::var("PATH").unwrap_or_default();
    let on_path = std::env::split_paths(&path).any(|d| d.join("lake").is_file());
    if on_path {
        return;
    }
    if let Some(home) = std::env::var_os("HOME") {
        let elan = Path::new(&home).join(".elan/bin");
        if elan.join("lake").is_file() {
            std::env::set_var("PATH", format!("{}:{path}", elan.display()));
        }
    }
}

// ── init ─────────────────────────────────────────────────────────────────────

fn cmd_init(slug: &str, project: Option<&str>) -> i32 {
    let project = resolve_project(project);
    let project_path = Path::new(&project);
    if !project_path.join("lakefile.lean").exists() {
        eprintln!("[scribe golf] not a lake project: {project}");
        return 2;
    }

    let instance = match slug_to_instance(project_path, slug) {
        Ok(i) => i,
        Err(e) => {
            eprintln!("[scribe golf] {e}");
            return 2;
        }
    };
    let config_path = project_path.join("configs").join(format!("{instance}.json"));
    let config: serde_json::Value = match fs::read_to_string(&config_path)
        .map_err(|e| e.to_string())
        .and_then(|t| serde_json::from_str(&t).map_err(|e| e.to_string()))
    {
        Ok(v) => v,
        Err(e) => {
            eprintln!("[scribe golf] cannot read {}: {e}", config_path.display());
            return 2;
        }
    };

    let str_list = |key: &str| -> Vec<String> {
        config[key]
            .as_array()
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_str().map(str::to_string))
                    .collect()
            })
            .unwrap_or_default()
    };
    let theorems = str_list("theorem_names");
    if theorems.is_empty() {
        eprintln!("[scribe golf] {} has no theorem_names", config_path.display());
        return 2;
    }
    let namespace = theorems[0]
        .rsplit_once('.')
        .map(|(ns, _)| ns.to_string())
        .unwrap_or_default();
    let state = GolfState {
        slug: slug.to_string(),
        instance: instance.clone(),
        project: project.clone(),
        namespace,
        solution_module: config["solution_module"]
            .as_str()
            .unwrap_or_default()
            .to_string(),
        theorems,
        permitted_axioms: str_list("permitted_axioms"),
    };

    let dir = state_dir(slug);
    if let Err(e) = fs::create_dir_all(dir.join("attempts")) {
        eprintln!("[scribe golf] cannot create {}: {e}", dir.display());
        return 2;
    }
    let json = serde_json::to_string_pretty(&state).expect("state serializes");
    if let Err(e) = fs::write(dir.join("state.json"), json) {
        eprintln!("[scribe golf] cannot write state: {e}");
        return 2;
    }

    eprintln!(
        "[scribe golf] {slug} → instance {} in {} ({} obligations, axioms: {})",
        state.instance,
        state.project,
        state.theorems.len(),
        state.permitted_axioms.join(", "),
    );
    render_board(&state, None);
    println!("INIT: {}", dir.join("state.json").display());
    0
}

/// Minimal line-oriented parse of instances.yml: `slug:` blocks with an
/// `  instance: X` field. Avoids a YAML dependency.
fn slug_to_instance(project: &Path, slug: &str) -> Result<String, String> {
    let text = fs::read_to_string(project.join("instances.yml"))
        .map_err(|e| format!("cannot read instances.yml: {e}"))?;
    let mut current: Option<&str> = None;
    for line in text.lines() {
        if !line.starts_with([' ', '\t', '#']) && line.ends_with(':') {
            current = Some(line.trim_end_matches(':'));
        } else if current == Some(slug) {
            if let Some(rest) = line.trim_start().strip_prefix("instance:") {
                return Ok(rest.trim().to_string());
            }
        }
    }
    Err(format!("slug '{slug}' not found in instances.yml"))
}

// ── obligation scanning ──────────────────────────────────────────────────────

#[derive(Clone)]
struct Obligation {
    /// Short name, e.g. `soundness`.
    name: String,
    /// File in Solution/<Instance>/ declaring `theorem <name>`.
    file: Option<PathBuf>,
    /// The declaration's proof still contains `sorry`.
    pending: bool,
}

fn scan_obligations(state: &GolfState) -> Vec<Obligation> {
    let sources = solution_sources(state);
    state
        .obligations()
        .into_iter()
        .map(|name| {
            let mut file = None;
            let mut pending = false;
            for (path, text) in &sources {
                if let Some(body) = decl_body(text, &name) {
                    file = Some(path.clone());
                    pending = body.contains("sorry");
                    break;
                }
            }
            Obligation { name, file, pending }
        })
        .collect()
}

fn solution_sources(state: &GolfState) -> Vec<(PathBuf, String)> {
    let mut out = Vec::new();
    if let Ok(entries) = fs::read_dir(state.solution_dir()) {
        let mut paths: Vec<_> = entries
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|x| x == "lean"))
            .collect();
        paths.sort();
        for p in paths {
            if let Ok(text) = fs::read_to_string(&p) {
                out.push((p, text));
            }
        }
    }
    out
}

/// Extract the source region of `theorem <name>` (or `def <name>`): from its
/// declaration line to the next flush-left declaration keyword.
fn decl_body(text: &str, name: &str) -> Option<String> {
    let lines: Vec<&str> = text.lines().collect();
    let is_decl = |l: &str| {
        let t = l.trim_start();
        for kw in ["theorem ", "def ", "private theorem ", "protected theorem "] {
            if let Some(rest) = t.strip_prefix(kw) {
                let ident: String = rest
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '.')
                    .collect();
                return ident == name || ident.ends_with(&format!(".{name}"));
            }
        }
        false
    };
    let start = lines.iter().position(|l| is_decl(l))?;
    let mut end = lines.len();
    for (i, l) in lines.iter().enumerate().skip(start + 1) {
        if !l.starts_with([' ', '\t']) && !l.is_empty() {
            let first = l.split_whitespace().next().unwrap_or("");
            if matches!(
                first,
                "theorem" | "def" | "instance" | "lemma" | "end" | "section" | "namespace"
                    | "private" | "protected" | "attribute" | "set_option" | "open" | "import"
                    | "@[reducible]" | "structure" | "abbrev"
            ) {
                end = i;
                break;
            }
        }
    }
    Some(lines[start..end].join("\n"))
}

// ── board rendering ──────────────────────────────────────────────────────────

const GREEN: &str = "\x1b[32m";
const RED: &str = "\x1b[31m";
const YELLOW: &str = "\x1b[33m";
const DIM: &str = "\x1b[2m";
const BOLD: &str = "\x1b[1m";
const RESET: &str = "\x1b[0m";

/// Render the obligation board to stderr. `live` marks one obligation as
/// currently being attempted.
fn render_board(state: &GolfState, live: Option<(&str, &str)>) {
    let obligations = scan_obligations(state);
    let attempts = latest_attempts(&state.slug);
    let (alloc, cons) = extract_cost(state);
    eprintln!(
        "\n{BOLD}◆ {}{RESET} {DIM}({}){RESET}  claimed cost: {}",
        state.slug,
        state.instance,
        match (alloc, cons) {
            (Some(a), Some(c)) => format!("{a}a + {c}c = {}", a + c),
            _ => "unknown".to_string(),
        }
    );
    for ob in &obligations {
        let attempt = attempts.get(&ob.name);
        let (mark, detail) = if let Some((name, note)) = live {
            if name == ob.name {
                (format!("{YELLOW}⟳{RESET}"), note.to_string())
            } else {
                board_row(ob, attempt)
            }
        } else {
            board_row(ob, attempt)
        };
        let file = ob
            .file
            .as_ref()
            .and_then(|f| f.file_name().map(|n| n.to_string_lossy().to_string()))
            .unwrap_or_else(|| format!("{RED}missing{RESET}"));
        eprintln!("  {mark} {:<22} {DIM}{:<24}{RESET} {detail}", ob.name, file);
    }
    eprintln!();
}

fn board_row(ob: &Obligation, attempt: Option<&AttemptSummary>) -> (String, String) {
    if ob.file.is_none() {
        return (
            format!("{RED}✗{RESET}"),
            "theorem not found in solution".to_string(),
        );
    }
    if ob.pending {
        let detail = match attempt {
            Some(a) => format!(
                "{DIM}last attempt: {} after {} iter{RESET}",
                a.outcome, a.iterations
            ),
            None => format!("{DIM}pending{RESET}"),
        };
        (format!("{YELLOW}·{RESET}"), detail)
    } else {
        let detail = match attempt {
            Some(a) if a.outcome == "proven" => {
                format!("{DIM}proven in {} iter{RESET}", a.iterations)
            }
            _ => format!("{DIM}proven{RESET}"),
        };
        (format!("{GREEN}✓{RESET}"), detail)
    }
}

struct AttemptSummary {
    outcome: String,
    iterations: usize,
}

/// Latest attempt journal per obligation, from golf/<slug>/attempts/*.json.
fn latest_attempts(slug: &str) -> BTreeMap<String, AttemptSummary> {
    let mut out = BTreeMap::new();
    let dir = state_dir(slug).join("attempts");
    let Ok(entries) = fs::read_dir(&dir) else {
        return out;
    };
    let mut files: Vec<_> = entries
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    files.sort(); // timestamped names → chronological; later overwrite earlier
    for path in files {
        let Some(stem) = path.file_stem().and_then(|s| s.to_str()) else {
            continue;
        };
        // `<obligation>-<epoch>.json`
        let Some((name, _)) = stem.rsplit_once('-') else {
            continue;
        };
        if let Ok(t) = transcript::load(&path.to_string_lossy()) {
            out.insert(
                name.to_string(),
                AttemptSummary {
                    outcome: t.journal.outcome.clone(),
                    iterations: t.journal.iterations.len(),
                },
            );
        }
    }
    out
}

fn extract_cost(state: &GolfState) -> (Option<u64>, Option<u64>) {
    let mut alloc = None;
    let mut cons = None;
    for (_, text) in solution_sources(state) {
        for line in text.lines() {
            let l = line.trim();
            if let Some(rest) = l.strip_prefix("@[reducible] def allocations : Nat :=") {
                alloc = rest.trim().parse().ok();
            }
            if let Some(rest) = l.strip_prefix("@[reducible] def constraints : Nat :=") {
                cons = rest.trim().parse().ok();
            }
        }
    }
    (alloc, cons)
}

// ── status / list ────────────────────────────────────────────────────────────

fn cmd_status(slug: &str) -> i32 {
    let state = match load_state(slug) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[scribe golf] {e}");
            return 2;
        }
    };
    render_board(&state, None);
    let pending = scan_obligations(&state).iter().filter(|o| o.pending).count();
    if pending == 0 {
        println!("STATUS: {slug} all-proven");
    } else {
        println!("STATUS: {slug} {pending} pending");
    }
    0
}

fn cmd_list(project: Option<&str>) -> i32 {
    let project = resolve_project(project);
    let text = match fs::read_to_string(Path::new(&project).join("instances.yml")) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("[scribe golf] cannot read instances.yml in {project}: {e}");
            return 2;
        }
    };
    eprintln!("{BOLD}zkGolf challenges{RESET} in {project}:");
    for line in text.lines() {
        if !line.starts_with([' ', '\t', '#']) && line.ends_with(':') {
            let slug = line.trim_end_matches(':');
            let inited = state_dir(slug).join("state.json").exists();
            let marker = if inited {
                format!("{GREEN}●{RESET}")
            } else {
                format!("{DIM}○{RESET}")
            };
            eprintln!("  {marker} {slug}");
        }
    }
    0
}

// ── prove ────────────────────────────────────────────────────────────────────

#[allow(clippy::too_many_arguments)]
fn cmd_prove(
    slug: &str,
    only: Option<&str>,
    max_iterations: u32,
    backend_name: &str,
    model: Option<String>,
    use_lsp: bool,
    samples: u32,
) -> i32 {
    let state = match load_state(slug) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[scribe golf] {e}");
            return 2;
        }
    };

    let obligations = scan_obligations(&state);
    let targets: Vec<&Obligation> = obligations
        .iter()
        .filter(|o| o.pending && only.is_none_or(|n| n == o.name))
        .collect();
    if targets.is_empty() {
        eprintln!("[scribe golf] nothing to prove for {slug}");
        render_board(&state, None);
        println!("PROVEN: {slug}");
        return 0;
    }

    // Imports of each obligation file (Defs, gadget files) must have oleans
    // before `lake env lean <file>` can elaborate it.
    eprintln!(
        "[scribe golf] pre-building {} (imports for obligation files)…",
        state.solution_module
    );
    let pre = lake_build_module(&state.project, &state.solution_module);
    if let Err(e) = pre {
        eprintln!("[scribe golf] pre-build failed: {e}");
        return 2;
    }

    let backend = match make_backend(backend_name, model, None, None) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("[scribe golf] backend error: {e}");
            return 2;
        }
    };

    let mut failed = Vec::new();
    for ob in &targets {
        let Some(file) = &ob.file else {
            eprintln!("[scribe golf] {}: theorem not found in any solution file", ob.name);
            failed.push(ob.name.clone());
            continue;
        };
        render_board(&state, Some((&ob.name, "proving…")));

        let system_prompt = build_golf_prompt(&state, &ob.name);
        let ts = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        let attempt_base = state_dir(slug)
            .join("attempts")
            .join(format!("{}-{ts}", ob.name));
        let config = SessionConfig {
            lean_file: file.to_string_lossy().to_string(),
            lake_dir: state.project.clone(),
            max_iterations,
            system_prompt: Some(system_prompt),
            transcript: Some(format!("{}.log", attempt_base.display())),
            use_lsp,
            samples_per_iter: samples,
        };
        eprintln!(
            "[scribe golf] {} → {} (budget {} iter, backend {}, follow: tail -f {}.log)",
            ob.name,
            file.display(),
            max_iterations,
            backend.name(),
            attempt_base.display(),
        );

        let started = Instant::now();
        let (result, journal) = session::run(&config, backend.as_ref());
        let elapsed = started.elapsed().as_secs();
        save_attempt(&attempt_base, &journal, &state.project);

        match result {
            SessionResult::Proven { iterations } => {
                eprintln!(
                    "[scribe golf] {GREEN}✓ {} proven{RESET} ({iterations} iter, {elapsed}s)",
                    ob.name
                );
            }
            SessionResult::Exhausted { iterations, last_error } => {
                let snippet: String = last_error.lines().take(4).collect::<Vec<_>>().join(" | ");
                eprintln!(
                    "[scribe golf] {RED}✗ {} exhausted{RESET} ({iterations} iter, {elapsed}s): {snippet}",
                    ob.name
                );
                failed.push(ob.name.clone());
            }
            SessionResult::Failed(e) => {
                eprintln!("[scribe golf] {RED}✗ {} failed{RESET}: {e}", ob.name);
                failed.push(ob.name.clone());
            }
        }
    }

    render_board(&state, None);
    if failed.is_empty() {
        println!("PROVEN: {slug}");
        0
    } else {
        println!("EXHAUSTED: {slug} ({})", failed.join(", "));
        1
    }
}

fn save_attempt(base: &Path, journal: &SessionJournal, project: &str) {
    let json_path = format!("{}.json", base.display());
    let rev = transcript::read_mathlib_rev(project);
    if let Err(e) = transcript::save(journal, &json_path, rev) {
        eprintln!("[scribe golf] warning: could not save attempt journal: {e}");
    }
}

/// System prompt: golf-specific base prompt + challenge interface + the
/// obligation statement + the matching playbook section.
fn build_golf_prompt(state: &GolfState, obligation: &str) -> String {
    let mut prompt = read_or_empty(&golf_prompt_path());
    if prompt.is_empty() {
        prompt = read_or_empty(Path::new("prompts/lean-prover.md"));
    }

    let interface = read_or_empty(&state.instance_dir().join("Interface.lean"));
    if !interface.is_empty() {
        prompt.push_str("\n\n## Challenge interface (trusted — do not restate)\n```lean\n");
        prompt.push_str(&interface);
        prompt.push_str("\n```\n");
    }

    let challenge = read_or_empty(&state.instance_dir().join("Challenge.lean"));
    if let Some(stmt) = decl_body(&challenge, obligation) {
        prompt.push_str("\n## The obligation being proven\n```lean\n");
        prompt.push_str(&stmt);
        prompt.push_str("\n```\n");
    }

    if let Some(section) = playbook_section(obligation) {
        prompt.push_str("\n## Playbook guidance for this obligation\n");
        prompt.push_str(&section);
        prompt.push('\n');
    }
    prompt
}

fn golf_prompt_path() -> PathBuf {
    if let Ok(dir) = std::env::var("SCRIBE_PROMPTS_DIR") {
        let p = Path::new(&dir).join("golf-prover.md");
        if p.exists() {
            return p;
        }
    }
    PathBuf::from("prompts/golf-prover.md")
}

fn read_or_empty(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_default()
}

/// Extract the `### <obligation>` subsection of §4 plus §5 (survival rules)
/// from docs/clean-playbook.md.
fn playbook_section(obligation: &str) -> Option<String> {
    let playbook = read_or_empty(Path::new("docs/clean-playbook.md"));
    if playbook.is_empty() {
        return None;
    }
    // isR1CS_Cidentity reuses the isR1CS section (plus §7 covers the deltas).
    let key = if obligation.starts_with("isR1CS") {
        "isR1CS"
    } else {
        obligation
    };
    let mut out = String::new();
    if let Some(sec) = markdown_section(&playbook, &format!("### {key}")) {
        out.push_str(&sec);
    }
    if let Some(sec) = markdown_section(&playbook, "## 5. Elaboration-cost survival rules") {
        out.push('\n');
        out.push_str(&sec);
    }
    if obligation == "isR1CS_Cidentity" {
        if let Some(sec) = markdown_section(&playbook, "## 7. Canonical challenges") {
            out.push('\n');
            out.push_str(&sec);
        }
    }
    if out.is_empty() { None } else { Some(out) }
}

/// The text from a heading line (prefix match) to the next heading of the same
/// or shallower level.
fn markdown_section(text: &str, heading_prefix: &str) -> Option<String> {
    let level = heading_prefix.chars().take_while(|c| *c == '#').count();
    let mut lines = Vec::new();
    let mut inside = false;
    for line in text.lines() {
        if line.starts_with('#') {
            let l = line.chars().take_while(|c| *c == '#').count();
            if inside && l <= level {
                break;
            }
            inside = inside || line.starts_with(heading_prefix);
        }
        if inside {
            lines.push(line);
        }
    }
    if lines.is_empty() {
        None
    } else {
        Some(lines.join("\n"))
    }
}

// ── check ────────────────────────────────────────────────────────────────────

fn cmd_check(slug: &str, max_heartbeats: u64) -> i32 {
    let state = match load_state(slug) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[scribe golf] {e}");
            return 2;
        }
    };
    let mut failures: Vec<String> = Vec::new();

    // 1. Forbidden tokens + heartbeat cap in every solution source.
    for (path, text) in solution_sources(&state) {
        if let Some(tok) = forbidden_source_token(&text) {
            failures.push(format!("{}: forbidden token `{tok}`", path.display()));
        }
        for line in text.lines() {
            if let Some(rest) = line.trim().strip_prefix("set_option maxHeartbeats") {
                let n: u64 = rest
                    .trim()
                    .trim_end_matches(" in")
                    .trim()
                    .parse()
                    .unwrap_or(u64::MAX);
                if n > max_heartbeats {
                    failures.push(format!(
                        "{}: maxHeartbeats {n} exceeds cap {max_heartbeats}",
                        path.display()
                    ));
                }
            }
        }
    }

    // 2. Toolchain files must be untouched.
    let diff = Command::new("git")
        .args([
            "-C",
            &state.project,
            "status",
            "--porcelain",
            "--",
            "lean-toolchain",
            "lakefile.lean",
            "lake-manifest.json",
        ])
        .output();
    match diff {
        Ok(o) => {
            let s = String::from_utf8_lossy(&o.stdout);
            if !s.trim().is_empty() {
                failures.push(format!("toolchain files modified:\n{}", s.trim_end()));
            }
        }
        Err(e) => failures.push(format!("git status failed: {e}")),
    }

    // 3. Green build of the solution module, with no sorry warnings.
    eprintln!("[scribe golf] building {}…", state.solution_module);
    match lake_build_module(&state.project, &state.solution_module) {
        Ok(output) => {
            if output.contains("declaration uses 'sorry'") {
                failures.push("build has `sorry` warnings".to_string());
            }
        }
        Err(e) => failures.push(format!("build failed:\n{e}")),
    }

    // 4. Axiom audit: #print axioms for every pinned theorem.
    if failures.is_empty() {
        match audit_axioms(&state) {
            Ok(violations) => failures.extend(violations),
            Err(e) => failures.push(format!("axiom audit failed: {e}")),
        }
    } else {
        eprintln!("[scribe golf] skipping axiom audit (earlier failures)");
    }

    // 5. Score.
    let (alloc, cons) = extract_cost(&state);
    render_board(&state, None);

    if failures.is_empty() {
        let score = match (alloc, cons) {
            (Some(a), Some(c)) => format!("score={} (a={a}, c={c})", a + c),
            _ => "score=unknown (allocations/constraints not found)".to_string(),
        };
        println!("GOLF CHECK PASS: {slug} {score}");
        0
    } else {
        for f in &failures {
            eprintln!("[scribe golf] {RED}FAIL{RESET}: {f}");
        }
        println!("GOLF CHECK FAIL: {slug} ({} problem(s))", failures.len());
        1
    }
}

/// `lake build <module>`; Ok(combined output) on success, Err(output) on
/// failure.
fn lake_build_module(project: &str, module: &str) -> Result<String, String> {
    let out = Command::new("lake")
        .arg("build")
        .arg(module)
        .current_dir(project)
        .output()
        .map_err(|e| format!("cannot run lake: {e}"))?;
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    if out.status.success() {
        Ok(combined)
    } else {
        Err(combined)
    }
}

/// Write a scratch file importing the solution and `#print axioms` for every
/// pinned theorem, elaborate it, and compare against the permitted list.
fn audit_axioms(state: &GolfState) -> Result<Vec<String>, String> {
    let scratch = Path::new(&state.project).join(".golf-axiom-audit.lean");
    let mut src = format!("import {}\n", state.solution_module);
    for thm in &state.theorems {
        src.push_str(&format!("#print axioms {thm}\n"));
    }
    fs::write(&scratch, src).map_err(|e| e.to_string())?;

    let out = Command::new("lake")
        .args(["env", "lean", ".golf-axiom-audit.lean"])
        .current_dir(&state.project)
        .output();
    let _ = fs::remove_file(&scratch);
    let out = out.map_err(|e| format!("cannot run lake env lean: {e}"))?;
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    if !out.status.success() {
        return Err(combined);
    }

    // Output shape (the axiom list wraps across lines):
    //   'Ns.thm' depends on axioms: [propext,
    //    Classical.choice,
    //    Quot.sound]
    Ok(parse_axiom_report(&combined, &state.permitted_axioms))
}

fn parse_axiom_report(report: &str, permitted: &[String]) -> Vec<String> {
    let mut violations = Vec::new();
    let mut current: Option<(String, String)> = None; // (theorem, accumulated list)
    let flush = |who: &str, list: &str, violations: &mut Vec<String>| {
        for ax in list.split(',').map(str::trim).filter(|a| !a.is_empty()) {
            if !permitted.iter().any(|p| p == ax) {
                violations.push(format!("{who}: non-permitted axiom `{ax}`"));
            }
        }
    };
    for line in report.lines() {
        if let Some((who, rest)) = line.split_once("depends on axioms:") {
            let who = who.trim().trim_matches('\'').to_string();
            let rest = rest.trim().trim_start_matches('[');
            if let Some(inner) = rest.strip_suffix(']') {
                flush(&who, inner, &mut violations);
            } else {
                current = Some((who, rest.to_string()));
            }
        } else if let Some((who, acc)) = current.as_mut() {
            let piece = line.trim();
            if let Some(inner) = piece.strip_suffix(']') {
                acc.push(',');
                acc.push_str(inner);
                let (who, acc) = (who.clone(), acc.clone());
                current = None;
                flush(&who, &acc, &mut violations);
            } else {
                acc.push(',');
                acc.push_str(piece);
            }
        }
    }
    violations
}

// ── tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slug_parse_finds_instance() {
        // structure mirrors instances.yml
        let dir = std::env::temp_dir().join(format!("golf-test-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join("instances.yml"),
            "# header\nassert-bytes:\n  type: public\n  instance: AssertBytes\nother:\n  instance: Other\n",
        )
        .unwrap();
        assert_eq!(slug_to_instance(&dir, "assert-bytes").unwrap(), "AssertBytes");
        assert_eq!(slug_to_instance(&dir, "other").unwrap(), "Other");
        assert!(slug_to_instance(&dir, "nope").is_err());
        fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn decl_body_extracts_theorem_region() {
        let src = "import Foo\n\ntheorem soundness : Bar := by\n  sorry\n\ntheorem completeness : Baz := by\n  exact trivial\n";
        let s = decl_body(src, "soundness").unwrap();
        assert!(s.contains("sorry"));
        assert!(!s.contains("completeness"));
        let c = decl_body(src, "completeness").unwrap();
        assert!(!c.contains("sorry"));
        assert!(decl_body(src, "missing").is_none());
    }

    #[test]
    fn decl_body_stops_at_attribute_and_namespace() {
        let src = "theorem mainCost : X := by\n  ring\nattribute [local irreducible] foo\ntheorem isR1CS : Y := by\n  sorry\nend Ns\n";
        let m = decl_body(src, "mainCost").unwrap();
        assert!(!m.contains("isR1CS"));
        let r = decl_body(src, "isR1CS").unwrap();
        assert!(r.contains("sorry"));
        assert!(!r.contains("end Ns"));
    }

    #[test]
    fn markdown_section_slices_between_headings() {
        let md = "# T\n## 4. ref\n### soundness\nalpha\n### completeness\nbeta\n## 5. rules\ngamma\n";
        let s = markdown_section(md, "### soundness").unwrap();
        assert!(s.contains("alpha"));
        assert!(!s.contains("beta"));
        let five = markdown_section(md, "## 5.").unwrap();
        assert!(five.contains("gamma"));
    }

    #[test]
    fn axiom_report_parses_multiline_lists() {
        let permitted: Vec<String> = ["propext", "Quot.sound", "Classical.choice"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let report = "'Ns.soundness' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'Ns.mainCost' depends on axioms: [propext, sorryAx]\n";
        let v = parse_axiom_report(report, &permitted);
        assert_eq!(v, vec!["Ns.mainCost: non-permitted axiom `sorryAx`"]);
        // violation hidden on a continuation line must be caught
        let report2 = "'Ns.t' depends on axioms: [propext,\n Lean.ofReduceBool]\n";
        let v2 = parse_axiom_report(report2, &permitted);
        assert_eq!(v2, vec!["Ns.t: non-permitted axiom `Lean.ofReduceBool`"]);
        // clean multi-theorem report has no violations
        let report3 = "'Ns.a' depends on axioms: [propext]\n'Ns.b' depends on axioms: []\n";
        assert!(parse_axiom_report(report3, &permitted).is_empty());
    }

    #[test]
    fn obligation_short_names() {
        let state = GolfState {
            slug: "s".into(),
            instance: "I".into(),
            project: "p".into(),
            namespace: "Solution.I".into(),
            solution_module: "Solution.I.Main".into(),
            theorems: vec![
                "Solution.I.soundness".into(),
                "Solution.I.isR1CS_Cidentity".into(),
            ],
            permitted_axioms: vec![],
        };
        assert_eq!(state.obligations(), vec!["soundness", "isR1CS_Cidentity"]);
    }
}
