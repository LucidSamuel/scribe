//! ZKGadgetEval — benchmark runner for ZK gadget proof completion.
//!
//! For each gadget in the suite: emit a Lean scaffold, run proof-pilot,
//! record pass/fail + iterations + wall time. Output JSON results.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use proof_pilot::backend::{
    resolve_api_key, AnthropicApi, Backend, ClaudeCli, OpenAiCompatible,
};
use proof_pilot::session::{self, SessionConfig, SessionResult};
use serde::{Deserialize, Serialize};

// ─── Suite manifest ─────────────────────────────────────────────────────────

#[derive(Deserialize)]
struct SuiteManifest {
    version: String,
    gadgets: Vec<GadgetEntry>,
}

#[derive(Deserialize)]
struct GadgetEntry {
    file: String,
    tier: u8,
    constraints: usize,
    #[allow(dead_code)]
    description: String,
}

// ─── Results ────────────────────────────────────────────────────────────────

#[derive(Serialize)]
struct BenchResults {
    suite_version: String,
    backend: String,
    budget: u32,
    use_lsp: bool,
    results: Vec<GadgetResult>,
    summary: Summary,
}

#[derive(Serialize)]
struct GadgetResult {
    gadget: String,
    tier: u8,
    constraints: usize,
    proved: bool,
    iterations: u32,
    wall_time_s: f64,
    error: Option<String>,
}

#[derive(Serialize)]
struct Summary {
    total: usize,
    passed: usize,
    pass_rate: f64,
    pass_at_1: f64,
    total_time_s: f64,
    by_tier: std::collections::BTreeMap<u8, TierSummary>,
}

#[derive(Serialize)]
struct TierSummary {
    total: usize,
    passed: usize,
    pass_rate: f64,
}

// ─── Main ───────────────────────────────────────────────────────────────────

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut suite_path = PathBuf::from("benchmark/suite.toml");
    let mut lake_dir = String::from("lean");
    let mut budget = 10u32;
    let mut model: Option<String> = None;
    let mut backend_name = String::from("claude");
    let mut api_key: Option<String> = None;
    let mut base_url: Option<String> = None;
    let mut system_prompt_file = Some("prompts/lean-prover.md".to_string());
    let mut use_lsp = false;
    let mut output_file: Option<String> = None;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--suite" => {
                i += 1;
                suite_path = PathBuf::from(&args[i]);
            }
            "--lake-dir" => {
                i += 1;
                lake_dir = args[i].clone();
            }
            "--budget" => {
                i += 1;
                budget = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("invalid --budget value");
                    std::process::exit(1);
                });
            }
            "--model" => {
                i += 1;
                model = Some(args[i].clone());
            }
            "--backend" => {
                i += 1;
                backend_name = args[i].clone();
            }
            "--api-key" => {
                i += 1;
                api_key = Some(args[i].clone());
            }
            "--base-url" => {
                i += 1;
                base_url = Some(args[i].clone());
            }
            "--system-prompt" => {
                i += 1;
                system_prompt_file = Some(args[i].clone());
            }
            "--lsp" => {
                use_lsp = true;
            }
            "--output" | "-o" => {
                i += 1;
                output_file = Some(args[i].clone());
            }
            "--help" | "-h" => {
                print_usage();
                return;
            }
            other => {
                eprintln!("unknown flag: {other}");
                print_usage();
                std::process::exit(1);
            }
        }
        i += 1;
    }

    // Load suite manifest
    let suite_dir = suite_path.parent().unwrap_or(Path::new("."));
    let manifest_text = fs::read_to_string(&suite_path).unwrap_or_else(|e| {
        eprintln!("cannot read suite manifest {}: {e}", suite_path.display());
        std::process::exit(1);
    });
    let manifest: SuiteManifest = toml::from_str(&manifest_text).unwrap_or_else(|e| {
        eprintln!("invalid suite manifest: {e}");
        std::process::exit(1);
    });

    // Construct backend
    let backend = build_backend(&backend_name, model, api_key.as_deref(), base_url);

    // Read system prompt
    let system_prompt = system_prompt_file.and_then(|path| {
        fs::read_to_string(&path)
            .map_err(|e| eprintln!("[bench] warning: could not read system prompt {path}: {e}"))
            .ok()
    });

    eprintln!(
        "=== ZKGadgetEval v{} ===",
        manifest.version
    );
    eprintln!("backend:  {}", backend.name());
    eprintln!("budget:   {budget} iterations");
    eprintln!("gadgets:  {}", manifest.gadgets.len());
    eprintln!("lsp:      {use_lsp}");
    eprintln!();

    // Ensure output directory for scaffolds
    let scaffold_dir = PathBuf::from(&lake_dir).join("ZkGadgets").join("Bench");
    fs::create_dir_all(&scaffold_dir).unwrap_or_else(|e| {
        eprintln!("cannot create scaffold dir {}: {e}", scaffold_dir.display());
        std::process::exit(1);
    });

    let mut results = Vec::new();
    let total_start = Instant::now();

    for (idx, entry) in manifest.gadgets.iter().enumerate() {
        let gadget_path = suite_dir.join(&entry.file);
        let gadget = match gadget_ir::load_gadget_file(&gadget_path) {
            Ok(g) => g,
            Err(e) => {
                eprintln!(
                    "[{}/{}] SKIP {} — load error: {e}",
                    idx + 1,
                    manifest.gadgets.len(),
                    entry.file
                );
                results.push(GadgetResult {
                    gadget: gadget_name(&entry.file),
                    tier: entry.tier,
                    constraints: entry.constraints,
                    proved: false,
                    iterations: 0,
                    wall_time_s: 0.0,
                    error: Some(format!("load: {e}")),
                });
                continue;
            }
        };

        // Emit Lean scaffold
        let scaffold = match lean_emit::emit_lean(&gadget) {
            Ok(s) => s,
            Err(e) => {
                eprintln!(
                    "[{}/{}] SKIP {} — emit error: {e}",
                    idx + 1,
                    manifest.gadgets.len(),
                    entry.file
                );
                results.push(GadgetResult {
                    gadget: gadget_name(&entry.file),
                    tier: entry.tier,
                    constraints: entry.constraints,
                    proved: false,
                    iterations: 0,
                    wall_time_s: 0.0,
                    error: Some(format!("emit: {e}")),
                });
                continue;
            }
        };

        let lean_filename = format!("Bench{}.lean", sanitize(&gadget.name));
        let lean_path = scaffold_dir.join(&lean_filename);
        if let Err(e) = fs::write(&lean_path, &scaffold) {
            eprintln!("cannot write {}: {e}", lean_path.display());
            continue;
        }

        let lean_file_str = lean_path.to_string_lossy().to_string();
        let transcript_path = format!(
            "benchmark/results/{}.log",
            gadget_name(&entry.file)
        );
        let _ = fs::create_dir_all("benchmark/results");

        let config = SessionConfig {
            lean_file: lean_file_str.clone(),
            lake_dir: lake_dir.clone(),
            max_iterations: budget,
            system_prompt: system_prompt.clone(),
            transcript: Some(transcript_path),
            use_lsp,
        };

        eprint!(
            "[{}/{}] {} (tier {}, {} constraints) ... ",
            idx + 1,
            manifest.gadgets.len(),
            gadget_name(&entry.file),
            entry.tier,
            entry.constraints
        );

        let start = Instant::now();
        let (result, _journal) = session::run(&config, backend.as_ref());
        let elapsed = start.elapsed().as_secs_f64();

        let (proved, iterations, error) = match result {
            SessionResult::Proven { iterations } => {
                eprintln!("PASS ({iterations} iter, {elapsed:.1}s)");
                (true, iterations, None)
            }
            SessionResult::Exhausted {
                iterations,
                last_error,
            } => {
                eprintln!("FAIL ({iterations} iter, {elapsed:.1}s)");
                (false, iterations, Some(first_line(&last_error)))
            }
            SessionResult::Failed(msg) => {
                eprintln!("ERROR: {msg}");
                (false, 0, Some(msg))
            }
        };

        results.push(GadgetResult {
            gadget: gadget_name(&entry.file),
            tier: entry.tier,
            constraints: entry.constraints,
            proved,
            iterations,
            wall_time_s: elapsed,
            error,
        });

        // Restore the scaffold (sorry) for clean reruns
        let _ = fs::write(&lean_path, &scaffold);
    }

    let total_time = total_start.elapsed().as_secs_f64();

    // Build summary
    let total = results.len();
    let passed = results.iter().filter(|r| r.proved).count();
    let pass_at_1 = results
        .iter()
        .filter(|r| r.proved && r.iterations <= 1)
        .count() as f64
        / total as f64;

    let mut by_tier = std::collections::BTreeMap::new();
    for r in &results {
        let entry = by_tier.entry(r.tier).or_insert(TierSummary {
            total: 0,
            passed: 0,
            pass_rate: 0.0,
        });
        entry.total += 1;
        if r.proved {
            entry.passed += 1;
        }
    }
    for tier in by_tier.values_mut() {
        tier.pass_rate = tier.passed as f64 / tier.total as f64;
    }

    let bench_results = BenchResults {
        suite_version: manifest.version,
        backend: backend.name().to_string(),
        budget,
        use_lsp,
        results,
        summary: Summary {
            total,
            passed,
            pass_rate: passed as f64 / total as f64,
            pass_at_1,
            total_time_s: total_time,
            by_tier,
        },
    };

    // Output
    let json = serde_json::to_string_pretty(&bench_results).unwrap();

    if let Some(path) = output_file {
        fs::write(&path, &json).unwrap_or_else(|e| {
            eprintln!("cannot write output {path}: {e}");
        });
        eprintln!("\nResults written to {path}");
    } else {
        println!("{json}");
    }

    // Print summary table
    eprintln!("\n=== Summary ===");
    eprintln!(
        "Pass rate: {}/{} ({:.0}%)",
        passed,
        total,
        bench_results.summary.pass_rate * 100.0
    );
    eprintln!("Pass@1:    {:.0}%", pass_at_1 * 100.0);
    eprintln!("Total time: {total_time:.1}s");
    for (tier, s) in &bench_results.summary.by_tier {
        eprintln!(
            "  Tier {tier}: {}/{} ({:.0}%)",
            s.passed,
            s.total,
            s.pass_rate * 100.0
        );
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

fn build_backend(
    name: &str,
    model: Option<String>,
    api_key: Option<&str>,
    base_url: Option<String>,
) -> Box<dyn Backend> {
    match name {
        "claude" | "claude-cli" => {
            let m = model.unwrap_or_else(|| "claude-sonnet-4-20250514".into());
            Box::new(ClaudeCli::new(m))
        }
        "anthropic" => {
            let m = model.unwrap_or_else(|| "claude-sonnet-4-20250514".into());
            let key = resolve_api_key(api_key, "ANTHROPIC_API_KEY").unwrap_or_else(|| {
                eprintln!("anthropic backend requires --api-key or ANTHROPIC_API_KEY");
                std::process::exit(1);
            });
            let mut b = AnthropicApi::new(m, key);
            if let Some(url) = base_url {
                b = b.with_base_url(url);
            }
            Box::new(b)
        }
        "openai" => {
            let m = model.unwrap_or_else(|| "gpt-4o".into());
            let key = resolve_api_key(api_key, "OPENAI_API_KEY").unwrap_or_else(|| {
                eprintln!("openai backend requires --api-key or OPENAI_API_KEY");
                std::process::exit(1);
            });
            let url = base_url.unwrap_or_else(|| "https://api.openai.com/v1".into());
            Box::new(
                OpenAiCompatible::new(m, Some(key), url)
                    .with_completion_tokens()
                    .with_name("openai".into()),
            )
        }
        "leanstral-local" => {
            let m = model.unwrap_or_else(|| "leanstral-v1".into());
            let url = base_url.unwrap_or_else(|| "http://localhost:8000/v1".into());
            Box::new(
                OpenAiCompatible::new(m, api_key.map(String::from), url)
                    .with_name("leanstral-local".into()),
            )
        }
        "openai-compat" => {
            let m = model.unwrap_or_else(|| {
                eprintln!("openai-compat requires --model");
                std::process::exit(1);
            });
            let url = base_url.unwrap_or_else(|| {
                eprintln!("openai-compat requires --base-url");
                std::process::exit(1);
            });
            Box::new(
                OpenAiCompatible::new(m, api_key.map(String::from), url)
                    .with_name("openai-compat".into()),
            )
        }
        other => {
            eprintln!("unknown backend: {other}");
            std::process::exit(1);
        }
    }
}

fn gadget_name(file: &str) -> String {
    Path::new(file)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or(file)
        .to_string()
}

fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect::<String>()
        .split("__")
        .collect::<Vec<_>>()
        .join("_")
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or(s).to_string()
}

fn print_usage() {
    eprintln!("zkgadget-eval — benchmark runner for ZK gadget proof completion");
    eprintln!();
    eprintln!("usage: zkgadget-eval [flags]");
    eprintln!();
    eprintln!("flags:");
    eprintln!("  --suite <path>            Suite manifest (default: benchmark/suite.toml)");
    eprintln!("  --lake-dir <dir>          Lake project directory (default: lean)");
    eprintln!("  --budget <n>              Max iterations per gadget (default: 10)");
    eprintln!("  --backend <name>          claude | anthropic | openai | leanstral-local | openai-compat");
    eprintln!("  --model <model>           Model name");
    eprintln!("  --api-key <key>           API key");
    eprintln!("  --base-url <url>          API base URL");
    eprintln!("  --system-prompt <file>    System prompt file");
    eprintln!("  --lsp                     Use LSP feedback");
    eprintln!("  -o, --output <file>       Write JSON results to file");
    eprintln!();
    eprintln!("example:");
    eprintln!("  zkgadget-eval --backend claude --budget 5 -o results.json");
    eprintln!("  zkgadget-eval --backend leanstral-local --base-url http://localhost:8000/v1");
}
