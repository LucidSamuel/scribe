use proof_pilot::session::{self, SessionConfig, SessionResult};

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
    let mut system_prompt = None;
    let mut transcript = None;

    // Parse optional flags
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--lake-dir" => {
                i += 1;
                lake_dir = args[i].clone();
            }
            "--max-iters" => {
                i += 1;
                max_iterations = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("invalid --max-iters value");
                    std::process::exit(1);
                });
            }
            "--model" => {
                i += 1;
                model = args[i].clone();
            }
            "--system-prompt" => {
                i += 1;
                system_prompt = Some(args[i].clone());
            }
            "--transcript" => {
                i += 1;
                transcript = Some(args[i].clone());
            }
            other => {
                eprintln!("unknown flag: {}", other);
                std::process::exit(1);
            }
        }
        i += 1;
    }

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
            eprintln!("proof complete in {} iteration(s)", iterations);
        }
        SessionResult::Exhausted { iterations, last_error } => {
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
