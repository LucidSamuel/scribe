//! ZKGadgetEval — benchmark runner for ZK gadget proof completion.
//!
//! For each gadget in the suite, and for each feedback mode × sample: emit a
//! Lean scaffold, run proof-pilot, record pass/fail + iterations + wall time.
//! Positive gadgets are scored with an unbiased pass@k estimator and a Wilson
//! 95% interval over the k samples. Negative gadgets (deliberately
//! under-constrained circuits whose spec is false) are graded on the loop
//! REFUSING to prove them — a "proved" negative is a soundness alarm that fails
//! the whole run. Output JSON results.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use proof_pilot::backend::{resolve_api_key, AnthropicApi, Backend, ClaudeCli, OpenAiCompatible};
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
    #[serde(default)]
    kind: GadgetKind,
}

/// Whether the gadget's spec is true (the loop should prove it) or deliberately
/// false via under-constraint (the loop must fail — proving it is an alarm).
#[derive(Deserialize, Serialize, Clone, Copy, PartialEq, Eq, Default)]
#[serde(rename_all = "lowercase")]
enum GadgetKind {
    #[default]
    Positive,
    Negative,
}

// ─── Feedback modes ─────────────────────────────────────────────────────────

/// A feedback-mode axis inside one run, so raw-vs-LSP is an in-harness A/B
/// rather than "run the suite twice and diff the JSONs".
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Build,
    Lsp,
}

impl Mode {
    fn name(self) -> &'static str {
        match self {
            Mode::Build => "build",
            Mode::Lsp => "lsp",
        }
    }

    fn parse(s: &str) -> Option<Mode> {
        match s {
            "build" | "raw" => Some(Mode::Build),
            "lsp" => Some(Mode::Lsp),
            _ => None,
        }
    }
}

// ─── Results ────────────────────────────────────────────────────────────────

#[derive(Serialize)]
struct BenchResults {
    suite_version: String,
    backend: String,
    budget: u32,
    samples: u32,
    modes: Vec<String>,
    results: Vec<GadgetResult>,
    summary: Summary,
}

#[derive(Serialize)]
struct GadgetResult {
    gadget: String,
    tier: u8,
    constraints: usize,
    kind: GadgetKind,
    mode: String,
    /// Samples attempted (0 when the gadget failed to load/emit).
    n: u32,
    /// Samples the loop proved. For negatives, anything above 0 is an alarm.
    proved: u32,
    /// Samples that failed for infrastructure/runtime reasons, not proof refusal.
    failed: u32,
    /// Unbiased pass@k estimate for each k in 1..=n: 1 - C(n-c,k)/C(n,k).
    pass_at: BTreeMap<u32, f64>,
    /// Wilson 95% interval on the per-sample prove probability.
    wilson95: [f64; 2],
    /// True iff this is a negative gadget that got "proved" at least once.
    soundness_alarm: bool,
    samples: Vec<SampleResult>,
    /// Load/emit error, when the gadget never ran.
    error: Option<String>,
}

#[derive(Serialize)]
struct SampleResult {
    status: SampleStatus,
    proved: bool,
    iterations: u32,
    wall_time_s: f64,
    error: Option<String>,
}

#[derive(Serialize, Clone, Copy, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum SampleStatus {
    Proven,
    Exhausted,
    Failed,
}

#[derive(Serialize)]
struct Summary {
    total_time_s: f64,
    /// Positive-gadget stats, keyed by feedback mode.
    positives: BTreeMap<String, ModeSummary>,
    negatives: NegativeSummary,
    /// Harness/runtime errors such as load/emit failures, backend failures, or
    /// Lean/LSP invocation failures. These invalidate the eval run.
    infrastructure_errors: Vec<String>,
}

#[derive(Serialize)]
struct ModeSummary {
    gadgets: usize,
    samples: u32,
    proved_samples: u32,
    /// Micro pass rate over all samples in this mode.
    pass_rate: f64,
    /// Macro mean of per-gadget pass@1 (each gadget weighted equally).
    mean_pass_at_1: f64,
    by_tier: BTreeMap<u8, TierSummary>,
}

#[derive(Serialize)]
struct TierSummary {
    samples: u32,
    proved: u32,
    pass_rate: f64,
}

#[derive(Serialize)]
struct NegativeSummary {
    gadgets: usize,
    samples: u32,
    /// Samples where the loop correctly failed to prove the false spec.
    refused: u32,
    /// Samples that did not grade because the harness/session failed.
    failed: u32,
    /// gadget×mode combinations where a false spec was "proved". Must be empty.
    soundness_alarms: Vec<String>,
}

// ─── Statistics ─────────────────────────────────────────────────────────────

/// Unbiased pass@k estimator over n samples with c successes:
/// `1 - C(n-c, k) / C(n, k)`, computed as a stable running product.
fn pass_at_k(n: u32, c: u32, k: u32) -> f64 {
    if n == 0 || k == 0 || k > n {
        return 0.0;
    }
    if n - c < k {
        return 1.0;
    }
    let mut fail_all = 1.0f64;
    for j in 0..k {
        fail_all *= (n - c - j) as f64 / (n - j) as f64;
    }
    1.0 - fail_all
}

/// Wilson score interval (95%, z = 1.96) for a binomial proportion — a sane
/// confidence interval even at the small n this suite runs with.
fn wilson95(proved: u32, n: u32) -> [f64; 2] {
    if n == 0 {
        return [0.0, 1.0];
    }
    let z = 1.96f64;
    let nf = n as f64;
    let p = proved as f64 / nf;
    let z2 = z * z;
    let denom = 1.0 + z2 / nf;
    let center = p + z2 / (2.0 * nf);
    let margin = z * ((p * (1.0 - p) + z2 / (4.0 * nf)) / nf).sqrt();
    [
        ((center - margin) / denom).max(0.0),
        ((center + margin) / denom).min(1.0),
    ]
}

fn pass_at_table(n: u32, c: u32) -> BTreeMap<u32, f64> {
    (1..=n).map(|k| (k, pass_at_k(n, c, k))).collect()
}

// ─── Main ───────────────────────────────────────────────────────────────────

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut suite_path = PathBuf::from("benchmark/suite.toml");
    let mut lake_dir = String::from("lean");
    let mut budget = 10u32;
    let mut samples = 1u32;
    let mut modes: Vec<Mode> = vec![Mode::Build];
    let mut model: Option<String> = None;
    let mut backend_name = String::from("claude");
    let mut api_key: Option<String> = None;
    let mut base_url: Option<String> = None;
    let mut system_prompt_file = Some("prompts/lean-prover.md".to_string());
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
            "--samples" => {
                i += 1;
                samples = args[i].parse().ok().filter(|&s| s >= 1).unwrap_or_else(|| {
                    eprintln!("invalid --samples value (must be >= 1)");
                    std::process::exit(1);
                });
            }
            "--modes" => {
                i += 1;
                modes = args[i]
                    .split(',')
                    .map(|s| {
                        Mode::parse(s.trim()).unwrap_or_else(|| {
                            eprintln!("invalid mode '{s}' (expected build|lsp)");
                            std::process::exit(1);
                        })
                    })
                    .collect();
                modes.dedup_by_key(|m| m.name());
                if modes.is_empty() {
                    eprintln!("--modes must name at least one of build,lsp");
                    std::process::exit(1);
                }
            }
            // Back-compat alias for `--modes lsp`.
            "--lsp" => {
                modes = vec![Mode::Lsp];
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

    let mode_names: Vec<String> = modes.iter().map(|m| m.name().to_string()).collect();
    let negatives = manifest
        .gadgets
        .iter()
        .filter(|g| g.kind == GadgetKind::Negative)
        .count();

    eprintln!("=== ZKGadgetEval v{} ===", manifest.version);
    eprintln!("backend:  {}", backend.name());
    eprintln!("budget:   {budget} iterations");
    eprintln!(
        "gadgets:  {} ({negatives} negative)",
        manifest.gadgets.len()
    );
    eprintln!("samples:  {samples} per gadget per mode");
    eprintln!("modes:    {}", mode_names.join(", "));
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
        let loaded = gadget_ir::load_gadget_file(&gadget_path)
            .map_err(|e| format!("load: {e}"))
            .and_then(|g| {
                lean_emit::emit_lean(&g)
                    .map(|s| (g, s))
                    .map_err(|e| format!("emit: {e}"))
            });
        let (gadget, scaffold) = match loaded {
            Ok(pair) => pair,
            Err(e) => {
                eprintln!(
                    "[{}/{}] SKIP {} — {e}",
                    idx + 1,
                    manifest.gadgets.len(),
                    entry.file
                );
                for mode in &modes {
                    results.push(failed_result(entry, mode.name(), &e));
                }
                continue;
            }
        };

        let lean_filename = format!("Bench{}.lean", sanitize(&gadget.name));
        let lean_path = scaffold_dir.join(&lean_filename);
        let lean_file_str = lean_path.to_string_lossy().to_string();
        let _ = fs::create_dir_all("benchmark/results");

        for mode in &modes {
            let mut sample_results = Vec::new();

            for s in 1..=samples {
                // Fresh scaffold (sorry) so every sample starts from scratch.
                if let Err(e) = fs::write(&lean_path, &scaffold) {
                    let msg = format!("write {}: {e}", lean_path.display());
                    eprintln!("cannot {msg}");
                    sample_results.push(SampleResult {
                        status: SampleStatus::Failed,
                        proved: false,
                        iterations: 0,
                        wall_time_s: 0.0,
                        error: Some(msg),
                    });
                    break;
                }

                let transcript_path = format!(
                    "benchmark/results/{}-{}-s{s}.log",
                    gadget_name(&entry.file),
                    mode.name()
                );
                let config = SessionConfig {
                    lean_file: lean_file_str.clone(),
                    lake_dir: lake_dir.clone(),
                    max_iterations: budget,
                    system_prompt: system_prompt.clone(),
                    transcript: Some(transcript_path),
                    use_lsp: *mode == Mode::Lsp,
                    samples_per_iter: 1,
                };

                eprint!(
                    "[{}/{}] {} (tier {}, {} constraints{}) [{} s{s}/{samples}] ... ",
                    idx + 1,
                    manifest.gadgets.len(),
                    gadget_name(&entry.file),
                    entry.tier,
                    entry.constraints,
                    if entry.kind == GadgetKind::Negative {
                        ", NEGATIVE"
                    } else {
                        ""
                    },
                    mode.name()
                );

                let start = Instant::now();
                let (result, _journal) = session::run(&config, backend.as_ref());
                let elapsed = start.elapsed().as_secs_f64();

                let (status, proved, iterations, error) = match result {
                    SessionResult::Proven { iterations } => {
                        if entry.kind == GadgetKind::Negative {
                            eprintln!("PROVED A FALSE SPEC ({iterations} iter, {elapsed:.1}s) ⚠");
                        } else {
                            eprintln!("PASS ({iterations} iter, {elapsed:.1}s)");
                        }
                        (SampleStatus::Proven, true, iterations, None)
                    }
                    SessionResult::Exhausted {
                        iterations,
                        last_error,
                    } => {
                        if entry.kind == GadgetKind::Negative {
                            eprintln!("REFUSED — correct ({iterations} iter, {elapsed:.1}s)");
                        } else {
                            eprintln!("FAIL ({iterations} iter, {elapsed:.1}s)");
                        }
                        (
                            SampleStatus::Exhausted,
                            false,
                            iterations,
                            Some(first_line(&last_error)),
                        )
                    }
                    SessionResult::Failed(msg) => {
                        eprintln!("ERROR: {msg}");
                        (SampleStatus::Failed, false, 0, Some(msg))
                    }
                };

                sample_results.push(SampleResult {
                    status,
                    proved,
                    iterations,
                    wall_time_s: elapsed,
                    error,
                });
            }

            // Restore the scaffold (sorry) for clean reruns
            let _ = fs::write(&lean_path, &scaffold);

            let n = sample_results.len() as u32;
            let proved = sample_results.iter().filter(|s| s.proved).count() as u32;
            let failed = sample_results
                .iter()
                .filter(|s| s.status == SampleStatus::Failed)
                .count() as u32;
            let alarm = entry.kind == GadgetKind::Negative && proved > 0;
            if alarm {
                eprintln!(
                    "⚠ SOUNDNESS ALARM: negative gadget {} was \"proved\" {proved}/{n} times \
                     under mode {} — the loop accepted a false spec",
                    gadget_name(&entry.file),
                    mode.name()
                );
            }

            results.push(GadgetResult {
                gadget: gadget_name(&entry.file),
                tier: entry.tier,
                constraints: entry.constraints,
                kind: entry.kind,
                mode: mode.name().to_string(),
                n,
                proved,
                failed,
                pass_at: pass_at_table(n, proved),
                wilson95: wilson95(proved, n),
                soundness_alarm: alarm,
                samples: sample_results,
                error: None,
            });
        }
    }

    let total_time = total_start.elapsed().as_secs_f64();
    let summary = summarize(&results, total_time);
    let has_alarms = !summary.negatives.soundness_alarms.is_empty();
    let has_infra_errors = !summary.infrastructure_errors.is_empty();

    let bench_results = BenchResults {
        suite_version: manifest.version,
        backend: backend.name().to_string(),
        budget,
        samples,
        modes: mode_names,
        results,
        summary,
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

    print_summary(&bench_results.summary);

    // A proved negative is a soundness alarm: fail the run loudly.
    if has_alarms {
        std::process::exit(2);
    }
    if has_infra_errors {
        std::process::exit(1);
    }
}

fn failed_result(entry: &GadgetEntry, mode: &str, error: &str) -> GadgetResult {
    GadgetResult {
        gadget: gadget_name(&entry.file),
        tier: entry.tier,
        constraints: entry.constraints,
        kind: entry.kind,
        mode: mode.to_string(),
        n: 0,
        proved: 0,
        failed: 0,
        pass_at: BTreeMap::new(),
        wilson95: wilson95(0, 0),
        soundness_alarm: false,
        samples: Vec::new(),
        error: Some(error.to_string()),
    }
}

fn summarize(results: &[GadgetResult], total_time_s: f64) -> Summary {
    let mut positives: BTreeMap<String, ModeSummary> = BTreeMap::new();
    let mut neg_gadgets: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
    let mut neg_samples = 0u32;
    let mut neg_refused = 0u32;
    let mut neg_failed = 0u32;
    let mut alarms = Vec::new();
    let mut infrastructure_errors = Vec::new();

    for r in results {
        if let Some(error) = &r.error {
            infrastructure_errors.push(format!("{} [{}]: {error}", r.gadget, r.mode));
        }
        for (idx, sample) in r.samples.iter().enumerate() {
            if sample.status == SampleStatus::Failed {
                let error = sample.error.as_deref().unwrap_or("session failed");
                infrastructure_errors.push(format!(
                    "{} [{} sample {}]: {error}",
                    r.gadget,
                    r.mode,
                    idx + 1
                ));
            }
        }

        match r.kind {
            GadgetKind::Negative => {
                neg_gadgets.insert(&r.gadget);
                neg_samples += r.n;
                neg_failed += r.failed;
                neg_refused += r.n.saturating_sub(r.proved + r.failed);
                if r.soundness_alarm {
                    alarms.push(format!("{} [{}]", r.gadget, r.mode));
                }
            }
            GadgetKind::Positive => {
                let mode = positives.entry(r.mode.clone()).or_insert(ModeSummary {
                    gadgets: 0,
                    samples: 0,
                    proved_samples: 0,
                    pass_rate: 0.0,
                    mean_pass_at_1: 0.0,
                    by_tier: BTreeMap::new(),
                });
                mode.gadgets += 1;
                mode.samples += r.n;
                mode.proved_samples += r.proved;
                // Accumulate pass@1 into the mean slot; divided by gadget count below.
                mode.mean_pass_at_1 += r.pass_at.get(&1).copied().unwrap_or(0.0);
                let tier = mode.by_tier.entry(r.tier).or_insert(TierSummary {
                    samples: 0,
                    proved: 0,
                    pass_rate: 0.0,
                });
                tier.samples += r.n;
                tier.proved += r.proved;
            }
        }
    }

    for mode in positives.values_mut() {
        if mode.samples > 0 {
            mode.pass_rate = mode.proved_samples as f64 / mode.samples as f64;
        }
        if mode.gadgets > 0 {
            mode.mean_pass_at_1 /= mode.gadgets as f64;
        }
        for tier in mode.by_tier.values_mut() {
            if tier.samples > 0 {
                tier.pass_rate = tier.proved as f64 / tier.samples as f64;
            }
        }
    }

    Summary {
        total_time_s,
        positives,
        negatives: NegativeSummary {
            gadgets: neg_gadgets.len(),
            samples: neg_samples,
            refused: neg_refused,
            failed: neg_failed,
            soundness_alarms: alarms,
        },
        infrastructure_errors,
    }
}

fn print_summary(summary: &Summary) {
    eprintln!("\n=== Summary ===");
    for (mode, s) in &summary.positives {
        eprintln!(
            "[{mode}] pass rate: {}/{} ({:.0}%), mean pass@1: {:.0}%",
            s.proved_samples,
            s.samples,
            s.pass_rate * 100.0,
            s.mean_pass_at_1 * 100.0
        );
        for (tier, t) in &s.by_tier {
            eprintln!(
                "  Tier {tier}: {}/{} ({:.0}%)",
                t.proved,
                t.samples,
                t.pass_rate * 100.0
            );
        }
    }
    let neg = &summary.negatives;
    if neg.samples > 0 {
        eprintln!(
            "Negatives: refused {}/{} false specs{}",
            neg.refused,
            neg.samples,
            if neg.soundness_alarms.is_empty() {
                if neg.failed == 0 {
                    " — correct".to_string()
                } else {
                    format!(" — {}/{} infrastructure failures", neg.failed, neg.samples)
                }
            } else {
                format!(" — ⚠ ALARMS: {}", neg.soundness_alarms.join(", "))
            }
        );
    }
    if !summary.infrastructure_errors.is_empty() {
        eprintln!(
            "Infrastructure errors: {} (eval invalid)",
            summary.infrastructure_errors.len()
        );
        for error in &summary.infrastructure_errors {
            eprintln!("  {error}");
        }
    }
    eprintln!("Total time: {:.1}s", summary.total_time_s);
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
            let m = model.unwrap_or_else(|| proof_pilot::backend::DEFAULT_ANTHROPIC_MODEL.into());
            Box::new(ClaudeCli::new(m))
        }
        "anthropic" => {
            let m = model.unwrap_or_else(|| proof_pilot::backend::DEFAULT_ANTHROPIC_MODEL.into());
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
    eprintln!("  --budget <n>              Max iterations per proof attempt (default: 10)");
    eprintln!("  --samples <n>             Samples per gadget per mode (default: 1)");
    eprintln!("  --modes <list>            Feedback modes to A/B, comma-separated: build,lsp");
    eprintln!("                            (default: build)");
    eprintln!(
        "  --backend <name>          claude | anthropic | openai | leanstral-local | openai-compat"
    );
    eprintln!("  --model <model>           Model name");
    eprintln!("  --api-key <key>           API key");
    eprintln!("  --base-url <url>          API base URL");
    eprintln!("  --system-prompt <file>    System prompt file");
    eprintln!("  --lsp                     Alias for --modes lsp");
    eprintln!("  -o, --output <file>       Write JSON results to file");
    eprintln!();
    eprintln!("Negative gadgets (kind = \"negative\" in the manifest) are false specs the");
    eprintln!("loop must FAIL to prove; a \"proved\" negative exits 2 (soundness alarm).");
    eprintln!();
    eprintln!("example:");
    eprintln!(
        "  zkgadget-eval --backend claude --budget 5 --samples 3 --modes build,lsp -o results.json"
    );
    eprintln!("  zkgadget-eval --backend leanstral-local --base-url http://localhost:8000/v1");
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pass_at_k_matches_closed_form() {
        // n=1: pass@1 is just the success indicator.
        assert_eq!(pass_at_k(1, 0, 1), 0.0);
        assert_eq!(pass_at_k(1, 1, 1), 1.0);
        // n=4, c=2: pass@1 = c/n.
        assert!((pass_at_k(4, 2, 1) - 0.5).abs() < 1e-12);
        // n=4, c=2, k=2: 1 - C(2,2)/C(4,2) = 1 - 1/6.
        assert!((pass_at_k(4, 2, 2) - (1.0 - 1.0 / 6.0)).abs() < 1e-12);
        // k > n - c: at least one success is guaranteed in any k-subset.
        assert_eq!(pass_at_k(4, 2, 3), 1.0);
        assert_eq!(pass_at_k(4, 4, 1), 1.0);
        // Degenerate inputs.
        assert_eq!(pass_at_k(0, 0, 1), 0.0);
        assert_eq!(pass_at_k(4, 0, 5), 0.0);
    }

    #[test]
    fn pass_at_table_covers_all_k() {
        let t = pass_at_table(3, 1);
        assert_eq!(t.len(), 3);
        assert!((t[&1] - 1.0 / 3.0).abs() < 1e-12);
        assert_eq!(t[&3], 1.0);
    }

    #[test]
    fn wilson_interval_sane() {
        // Full failure / full success at n=1 still spans a wide interval.
        let [lo, hi] = wilson95(0, 1);
        assert_eq!(lo, 0.0);
        assert!(hi > 0.5 && hi < 1.0);
        let [lo, hi] = wilson95(1, 1);
        assert!(lo > 0.0 && lo < 0.5);
        assert_eq!(hi, 1.0);
        // Interval tightens with n and stays within [0,1], containing p̂.
        let [lo, hi] = wilson95(5, 10);
        assert!(lo > 0.2 && lo < 0.5);
        assert!(hi > 0.5 && hi < 0.8);
        // n=0 is the vacuous interval.
        assert_eq!(wilson95(0, 0), [0.0, 1.0]);
    }

    #[test]
    fn shipped_manifest_parses_and_contains_negative_gadgets() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../benchmark/suite.toml");
        let manifest: SuiteManifest =
            toml::from_str(&std::fs::read_to_string(path).expect("read suite.toml"))
                .expect("parse suite.toml");
        let negatives: Vec<&str> = manifest
            .gadgets
            .iter()
            .filter(|g| g.kind == GadgetKind::Negative)
            .map(|g| g.file.as_str())
            .collect();
        // The suite must keep at least one false spec, or it cannot distinguish
        // "proves true specs" from "proves anything you hand it".
        assert!(!negatives.is_empty());
        assert!(negatives.contains(&"suite/16-neg-underconstrained-range.toml"));
        assert!(negatives.contains(&"suite/17-neg-vacuous-constraint.toml"));
        // Every gadget file referenced by the manifest exists and loads as gadget IR.
        let suite_dir = Path::new(path).parent().unwrap();
        for g in &manifest.gadgets {
            gadget_ir::load_gadget_file(&suite_dir.join(&g.file))
                .unwrap_or_else(|e| panic!("{} does not load: {e}", g.file));
        }
    }

    #[test]
    fn negative_gadget_alarm_feeds_summary_and_positive_stats_split_by_mode() {
        let make = |gadget: &str, kind, mode: &str, tier, n, proved, alarm| GadgetResult {
            gadget: gadget.to_string(),
            tier,
            constraints: 1,
            kind,
            mode: mode.to_string(),
            n,
            proved,
            failed: 0,
            pass_at: pass_at_table(n, proved),
            wilson95: wilson95(proved, n),
            soundness_alarm: alarm,
            samples: Vec::new(),
            error: None,
        };
        let results = vec![
            make("pos-a", GadgetKind::Positive, "build", 1, 4, 4, false),
            make("pos-b", GadgetKind::Positive, "build", 2, 4, 1, false),
            make("pos-a", GadgetKind::Positive, "lsp", 1, 4, 2, false),
            // A negative that was correctly refused everywhere...
            make("neg-ok", GadgetKind::Negative, "build", 1, 4, 0, false),
            // ...and one that was "proved" once: alarm.
            make("neg-bad", GadgetKind::Negative, "build", 1, 4, 1, true),
        ];
        let s = summarize(&results, 1.0);

        let build = &s.positives["build"];
        assert_eq!(build.gadgets, 2);
        assert_eq!((build.samples, build.proved_samples), (8, 5));
        assert!((build.pass_rate - 5.0 / 8.0).abs() < 1e-12);
        // mean of pass@1 = mean(1.0, 0.25)
        assert!((build.mean_pass_at_1 - 0.625).abs() < 1e-12);
        assert_eq!(build.by_tier[&1].proved, 4);
        assert_eq!(build.by_tier[&2].proved, 1);

        let lsp = &s.positives["lsp"];
        assert_eq!(lsp.gadgets, 1);
        assert!((lsp.pass_rate - 0.5).abs() < 1e-12);

        assert_eq!(s.negatives.gadgets, 2);
        assert_eq!((s.negatives.samples, s.negatives.refused), (8, 7));
        assert_eq!(s.negatives.failed, 0);
        assert_eq!(s.negatives.soundness_alarms, vec!["neg-bad [build]"]);
        assert!(s.infrastructure_errors.is_empty());
    }

    #[test]
    fn failed_negative_sample_is_infrastructure_error_not_refusal() {
        let results = vec![GadgetResult {
            gadget: "neg-backend-down".to_string(),
            tier: 1,
            constraints: 1,
            kind: GadgetKind::Negative,
            mode: "build".to_string(),
            n: 2,
            proved: 0,
            failed: 1,
            pass_at: pass_at_table(2, 0),
            wilson95: wilson95(0, 2),
            soundness_alarm: false,
            samples: vec![
                SampleResult {
                    status: SampleStatus::Exhausted,
                    proved: false,
                    iterations: 3,
                    wall_time_s: 0.1,
                    error: Some("unsolved".to_string()),
                },
                SampleResult {
                    status: SampleStatus::Failed,
                    proved: false,
                    iterations: 0,
                    wall_time_s: 0.0,
                    error: Some("backend: unavailable".to_string()),
                },
            ],
            error: None,
        }];

        let s = summarize(&results, 1.0);

        assert_eq!(s.negatives.samples, 2);
        assert_eq!(s.negatives.refused, 1);
        assert_eq!(s.negatives.failed, 1);
        assert_eq!(s.negatives.soundness_alarms.len(), 0);
        assert_eq!(s.infrastructure_errors.len(), 1);
        assert!(s.infrastructure_errors[0].contains("backend: unavailable"));
    }
}
