use proof_pilot::backend::{resolve_api_key, AnthropicApi, ClaudeCli, OpenAiCompatible, Backend};
use proof_pilot::session::{self, SessionConfig, SessionResult};

const DEFAULT_SYSTEM_PROMPT: &str = "prompts/lean-prover.md";

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: proof-pilot <path/to/File.lean> [flags]");
        eprintln!();
        eprintln!("flags:");
        eprintln!("  --lake-dir <dir>          Lake project directory (default: lean)");
        eprintln!("  --max-iters <n>           Max iterations (default: 10)");
        eprintln!("  --model <model>           Model name (default depends on backend)");
        eprintln!("  --system-prompt <file>    System prompt file");
        eprintln!("  --transcript <file>       Transcript log file");
        eprintln!("  --lsp                     Use LSP feedback");
        eprintln!("  --backend <name>          Backend (default: claude)");
        eprintln!("      claude               Claude CLI (shells out to `claude -p`)");
        eprintln!("      anthropic            Anthropic Messages API (ANTHROPIC_API_KEY)");
        eprintln!("      openai               OpenAI Chat Completions (OPENAI_API_KEY)");
        eprintln!("      leanstral            Leanstral hosted API (LEANSTRAL_API_KEY + --base-url)");
        eprintln!("      leanstral-local      Leanstral self-hosted (localhost, no auth)");
        eprintln!("      openai-compat        Generic OpenAI-compatible (--base-url, optional auth)");
        eprintln!("  --api-key <key>           API key (or set env var per backend)");
        eprintln!("  --base-url <url>          API base URL (override default endpoint)");
        std::process::exit(1);
    }

    let lean_file = args[1].clone();

    // Defaults
    let mut lake_dir = String::from("lean");
    let mut max_iterations = 10u32;
    let mut model: Option<String> = None;
    let mut system_prompt_file = Some(DEFAULT_SYSTEM_PROMPT.to_string());
    let mut transcript = None;
    let mut use_lsp = false;
    let mut backend_name = String::from("claude");
    let mut api_key: Option<String> = None;
    let mut base_url: Option<String> = None;

    // Parse optional flags
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--lake-dir" => {
                lake_dir = flag_value(&args, &mut i, "--lake-dir");
            }
            "--max-iters" => {
                let value = flag_value(&args, &mut i, "--max-iters");
                max_iterations = value.parse().unwrap_or_else(|_| {
                    eprintln!("invalid --max-iters value");
                    std::process::exit(1);
                });
            }
            "--model" => {
                model = Some(flag_value(&args, &mut i, "--model"));
            }
            "--system-prompt" => {
                system_prompt_file = Some(flag_value(&args, &mut i, "--system-prompt"));
            }
            "--transcript" => {
                transcript = Some(flag_value(&args, &mut i, "--transcript"));
            }
            "--lsp" => {
                use_lsp = true;
            }
            "--backend" => {
                backend_name = flag_value(&args, &mut i, "--backend");
            }
            "--api-key" => {
                api_key = Some(flag_value(&args, &mut i, "--api-key"));
            }
            "--base-url" => {
                base_url = Some(flag_value(&args, &mut i, "--base-url"));
            }
            other => {
                eprintln!("unknown flag: {}", other);
                std::process::exit(1);
            }
        }
        i += 1;
    }

    // Read system prompt from file if provided
    let system_prompt = system_prompt_file.map(|path| {
        std::fs::read_to_string(&path).unwrap_or_else(|e| {
            eprintln!("error reading system prompt {}: {}", path, e);
            std::process::exit(1);
        })
    });

    // Construct backend
    let backend: Box<dyn Backend> = match backend_name.as_str() {
        "claude" | "claude-cli" => {
            let m = model.unwrap_or_else(|| "claude-sonnet-4-20250514".into());
            Box::new(ClaudeCli::new(m))
        }
        "anthropic" => {
            let m = model.unwrap_or_else(|| "claude-sonnet-4-20250514".into());
            let key = require_api_key(api_key.as_deref(), "ANTHROPIC_API_KEY", "anthropic");
            let mut b = AnthropicApi::new(m, key);
            if let Some(url) = base_url {
                b = b.with_base_url(url);
            }
            Box::new(b)
        }
        "openai" => {
            let m = model.unwrap_or_else(|| "gpt-4o".into());
            let key = require_api_key(api_key.as_deref(), "OPENAI_API_KEY", "openai");
            let url = base_url.unwrap_or_else(|| "https://api.openai.com/v1".into());
            Box::new(
                OpenAiCompatible::new(m, Some(key), url)
                    .with_completion_tokens()
                    .with_name("openai".into()),
            )
        }
        "leanstral" => {
            let m = model.unwrap_or_else(|| "leanstral-v1".into());
            let key = require_api_key(api_key.as_deref(), "LEANSTRAL_API_KEY", "leanstral");
            let url = base_url.unwrap_or_else(|| {
                eprintln!("leanstral backend requires --base-url (e.g. https://api.leanstral.ai/v1)");
                std::process::exit(1);
            });
            Box::new(
                OpenAiCompatible::new(m, Some(key), url).with_name("leanstral".into()),
            )
        }
        "leanstral-local" => {
            let m = model.unwrap_or_else(|| "leanstral-v1".into());
            let url = base_url.unwrap_or_else(|| "http://localhost:8000/v1".into());
            // No auth required for local endpoints
            Box::new(
                OpenAiCompatible::new(m, api_key, url).with_name("leanstral-local".into()),
            )
        }
        "openai-compat" => {
            let m = model.unwrap_or_else(|| {
                eprintln!("openai-compat backend requires --model");
                std::process::exit(1);
            });
            let url = base_url.unwrap_or_else(|| {
                eprintln!("openai-compat backend requires --base-url");
                std::process::exit(1);
            });
            // Auth is optional — pass through whatever the user gave
            Box::new(
                OpenAiCompatible::new(m, api_key, url).with_name("openai-compat".into()),
            )
        }
        other => {
            eprintln!("unknown backend: {other}");
            eprintln!("available: claude, anthropic, openai, leanstral, leanstral-local, openai-compat");
            std::process::exit(1);
        }
    };

    eprintln!("[proof-pilot] backend: {}", backend.name());

    let config = SessionConfig {
        lean_file,
        lake_dir,
        max_iterations,
        system_prompt,
        transcript,
        use_lsp,
    };

    match session::run(&config, backend.as_ref()) {
        SessionResult::Proven { iterations } => {
            if iterations == 0 {
                eprintln!("already proven");
            } else {
                eprintln!("proof complete in {} iteration(s)", iterations);
            }
        }
        SessionResult::Exhausted {
            iterations,
            last_error,
        } => {
            eprintln!("gave up after {} iterations", iterations);
            eprintln!("last error:\n{}", last_error);
            std::process::exit(1);
        }
        SessionResult::Failed(msg) => {
            eprintln!("fatal: {}", msg);
            std::process::exit(2);
        }
    }
}

fn flag_value(args: &[String], i: &mut usize, flag: &str) -> String {
    *i += 1;
    args.get(*i).cloned().unwrap_or_else(|| {
        eprintln!("missing value for {}", flag);
        std::process::exit(1);
    })
}

fn require_api_key(explicit: Option<&str>, env_var: &str, backend: &str) -> String {
    resolve_api_key(explicit, env_var).unwrap_or_else(|| {
        eprintln!("{backend} backend requires --api-key or {env_var} env var");
        std::process::exit(1);
    })
}
