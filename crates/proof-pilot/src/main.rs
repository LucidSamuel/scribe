use proof_pilot::session::{self, SessionConfig, SessionResult};

const DEFAULT_SYSTEM_PROMPT: &str = "prompts/lean-prover.md";

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: proof-pilot <path/to/File.lean> [--lake-dir <dir>] [--max-iters <n>] [--model <model>] [--system-prompt <file>] [--transcript <file>]");
        std::process::exit(1);
    }

    let lean_file = args[1].clone();

    // Defaults
    let mut lake_dir = String::from("lean");
    let mut max_iterations = 10u32;
    let mut model = String::from("claude-sonnet-4-20250514");
    let mut system_prompt_file = Some(DEFAULT_SYSTEM_PROMPT.to_string());
    let mut transcript = None;

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
                model = flag_value(&args, &mut i, "--model");
            }
            "--system-prompt" => {
                system_prompt_file = Some(flag_value(&args, &mut i, "--system-prompt"));
            }
            "--transcript" => {
                transcript = Some(flag_value(&args, &mut i, "--transcript"));
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

    let config = SessionConfig {
        lean_file,
        lake_dir,
        max_iterations,
        model,
        system_prompt,
        transcript,
    };

    match session::run(&config) {
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
