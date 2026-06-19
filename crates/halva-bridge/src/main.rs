use std::fs;
use std::process;

use halva_bridge::{parse_halva_output, scaffold_raw, scaffold_soundness, SpecConfig};
use proof_pilot::backend::make_backend;
use proof_pilot::session::{self, SessionConfig, SessionResult};

const DEFAULT_SYSTEM_PROMPT: &str = "prompts/lean-prover.md";

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        usage();
        process::exit(1);
    }
    if matches!(args[1].as_str(), "--help" | "-h") {
        usage();
        return;
    }
    if args[1].starts_with('-') {
        eprintln!("unknown flag: {}", args[1]);
        usage();
        process::exit(1);
    }

    let halva_file = &args[1];

    // Defaults
    let mut spec: Option<String> = None;
    let mut spec_file: Option<String> = None;
    let mut output: Option<String> = None;
    let mut extra_imports = Vec::new();
    let mut prove = false;
    let mut lake_dir = String::from("lean");
    let mut max_iterations = 10u32;
    let mut model: Option<String> = None;
    let mut system_prompt_file = Some(DEFAULT_SYSTEM_PROMPT.to_string());
    let mut transcript = None;
    let mut use_lsp = false;
    let mut backend_name = String::from("claude");
    let mut api_key: Option<String> = None;
    let mut base_url: Option<String> = None;

    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--spec" => spec = Some(flag_value(&args, &mut i, "--spec")),
            "--spec-file" => spec_file = Some(flag_value(&args, &mut i, "--spec-file")),
            "--extra-import" => {
                extra_imports.push(flag_value(&args, &mut i, "--extra-import"));
            }
            "--extra-imports" => {
                let imports = flag_value(&args, &mut i, "--extra-imports");
                extra_imports.extend(
                    imports
                        .split(',')
                        .map(str::trim)
                        .filter(|import| !import.is_empty())
                        .map(str::to_string),
                );
            }
            "--output" | "-o" => output = Some(flag_value(&args, &mut i, "--output")),
            "--prove" => prove = true,
            "--lake-dir" => lake_dir = flag_value(&args, &mut i, "--lake-dir"),
            "--max-iters" => {
                let v = flag_value(&args, &mut i, "--max-iters");
                max_iterations = v.parse().unwrap_or_else(|_| {
                    eprintln!("invalid --max-iters value");
                    process::exit(1);
                });
            }
            "--model" => model = Some(flag_value(&args, &mut i, "--model")),
            "--system-prompt" => {
                system_prompt_file = Some(flag_value(&args, &mut i, "--system-prompt"));
            }
            "--transcript" => transcript = Some(flag_value(&args, &mut i, "--transcript")),
            "--lsp" => use_lsp = true,
            "--backend" => backend_name = flag_value(&args, &mut i, "--backend"),
            "--api-key" => api_key = Some(flag_value(&args, &mut i, "--api-key")),
            "--base-url" => base_url = Some(flag_value(&args, &mut i, "--base-url")),
            "--help" | "-h" => {
                usage();
                return;
            }
            other => {
                eprintln!("unknown flag: {other}");
                usage();
                process::exit(1);
            }
        }
        i += 1;
    }

    if spec.is_some() && spec_file.is_some() {
        eprintln!("error: --spec and --spec-file are mutually exclusive");
        process::exit(1);
    }
    if spec_file.is_some() && !extra_imports.is_empty() {
        eprintln!("error: --extra-import and --extra-imports require --spec");
        process::exit(1);
    }

    // Read the Halva output file.
    let halva_content = fs::read_to_string(halva_file).unwrap_or_else(|e| {
        eprintln!("error reading {halva_file}: {e}");
        process::exit(1);
    });

    // Parse it.
    let halva = parse_halva_output(&halva_content).unwrap_or_else(|e| {
        eprintln!("error parsing Halva output: {e}");
        process::exit(1);
    });

    eprintln!(
        "[halva-bridge] namespace: {}, meets_constraints: found",
        halva.namespace
    );

    // Build combined file.
    let combined = if let Some(snippet_path) = &spec_file {
        // Raw snippet mode: insert file contents verbatim.
        let snippet = fs::read_to_string(snippet_path).unwrap_or_else(|e| {
            eprintln!("error reading spec file {snippet_path}: {e}");
            process::exit(1);
        });
        scaffold_raw(&halva, &snippet)
    } else if let Some(spec_body) = &spec {
        // Structured mode: auto-generate Spec def + soundness theorem.
        let config = SpecConfig {
            spec_body: spec_body.clone(),
            extra_imports,
        };
        scaffold_soundness(&halva, &config)
    } else {
        eprintln!("error: must provide --spec <expression> or --spec-file <path>");
        process::exit(1);
    };

    // Determine output path.
    let out_path = output.unwrap_or_else(|| {
        // Default: write next to the Halva file with _soundness suffix.
        let p = std::path::Path::new(halva_file);
        let stem = p.file_stem().unwrap_or_default().to_string_lossy();
        let parent = p.parent().unwrap_or(std::path::Path::new("."));
        parent
            .join(format!("{stem}_soundness.lean"))
            .to_string_lossy()
            .into_owned()
    });

    fs::write(&out_path, &combined).unwrap_or_else(|e| {
        eprintln!("error writing {out_path}: {e}");
        process::exit(1);
    });
    eprintln!("[halva-bridge] wrote {out_path}");

    if !prove {
        // Just emit the file, don't run proof-pilot.
        println!("{out_path}");
        return;
    }

    // Run proof-pilot on the combined file.
    eprintln!("[halva-bridge] launching proof-pilot...");

    let system_prompt = system_prompt_file.map(|path| {
        fs::read_to_string(&path).unwrap_or_else(|e| {
            eprintln!("error reading system prompt {path}: {e}");
            process::exit(1);
        })
    });

    let backend = make_backend(&backend_name, model, api_key, base_url);

    let config = SessionConfig {
        lean_file: out_path.clone(),
        lake_dir,
        max_iterations,
        system_prompt,
        transcript,
        use_lsp,
    };

    let (result, _journal) = session::run(&config, backend.as_ref());
    match result {
        SessionResult::Proven { iterations } => {
            if iterations == 0 {
                eprintln!("[halva-bridge] already proven");
            } else {
                eprintln!("[halva-bridge] proof complete in {iterations} iteration(s)");
            }
        }
        SessionResult::Exhausted {
            iterations,
            last_error,
        } => {
            eprintln!("[halva-bridge] gave up after {iterations} iterations");
            eprintln!("last error:\n{last_error}");
            process::exit(1);
        }
        SessionResult::Failed(msg) => {
            eprintln!("[halva-bridge] fatal: {msg}");
            process::exit(2);
        }
    }
}

fn flag_value(args: &[String], i: &mut usize, flag: &str) -> String {
    *i += 1;
    args.get(*i).cloned().unwrap_or_else(|| {
        eprintln!("missing value for {flag}");
        process::exit(1);
    })
}

fn usage() {
    eprintln!("usage: halva-bridge <halva-output.lean> [flags]");
    eprintln!();
    eprintln!("Bridges Halva halo2-to-Lean extraction to scribe's proof-pilot.");
    eprintln!("Takes a Lean file emitted by Halva, appends a soundness theorem,");
    eprintln!("and optionally runs proof-pilot to close the proof.");
    eprintln!();
    eprintln!("flags:");
    eprintln!("  --spec <expr>             Spec body (Lean prop over c: ValidCircuit)");
    eprintln!("  --spec-file <path>        Raw Lean snippet with Spec + theorem");
    eprintln!("  --extra-import <module>   Extra import for --spec (repeatable)");
    eprintln!("  --extra-imports <list>    Comma-separated extra imports for --spec");
    eprintln!("  -o, --output <path>       Output .lean file (default: <input>_soundness.lean)");
    eprintln!("  --prove                   Run proof-pilot after scaffolding");
    eprintln!("  --lake-dir <dir>          Lake project directory (default: lean)");
    eprintln!("  --max-iters <n>           Max proof iterations (default: 10)");
    eprintln!("  --backend <name>          Backend (default: claude)");
    eprintln!("      claude               Claude CLI");
    eprintln!("      anthropic            Anthropic Messages API");
    eprintln!("      openai               OpenAI Chat Completions");
    eprintln!("      leanstral            Leanstral hosted API");
    eprintln!("      leanstral-local      Leanstral self-hosted");
    eprintln!("      openai-compat        Generic OpenAI-compatible API");
    eprintln!("  --model <model>           Model name");
    eprintln!("  --system-prompt <file>    System prompt file");
    eprintln!("  --transcript <file>       Transcript log file");
    eprintln!("  --lsp                     Use LSP feedback");
    eprintln!("  --api-key <key>           API key");
    eprintln!("  --base-url <url>          API endpoint override");
}
