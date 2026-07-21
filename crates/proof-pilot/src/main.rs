use proof_pilot::backend::make_backend;
use proof_pilot::notes::render_notes;
use proof_pilot::replay;
use proof_pilot::session::{self, SessionConfig, SessionResult};
use proof_pilot::transcript;

const DEFAULT_SYSTEM_PROMPT: &str = "prompts/lean-prover.md";
const EMBEDDED_SYSTEM_PROMPT: &str = include_str!("../prompts/lean-prover.md");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: proof-pilot <path/to/File.lean> [flags]");
        eprintln!();
        eprintln!("flags:");
        eprintln!("  --lake-dir <dir>              Lake project directory (default: lean)");
        eprintln!("  --max-iters <n>               Max iterations (default: 10)");
        eprintln!("  --model <model>               Model name (default depends on backend)");
        eprintln!("  --system-prompt <file>        System prompt file");
        eprintln!("  --transcript <file>           Transcript log file (plaintext)");
        eprintln!("  --save-transcript <file>      Save session journal as versioned JSON");
        eprintln!("  --notes [<file>]              Write NOTES.md on failure (default: <lean_file>.notes.md)");
        eprintln!("  --replay <file.json>          Replay a saved transcript (skips LLM)");
        eprintln!("  --verify                      Verify each replay step with lake build");
        eprintln!("  --allow-toolchain-mismatch    Warn (not error) on toolchain/mathlib mismatch during replay");
        eprintln!("  --lsp                         Use LSP feedback");
        eprintln!("  --backend <name>              Backend (default: claude)");
        eprintln!("      claude               Claude CLI (shells out to `claude -p`)");
        eprintln!("      anthropic            Anthropic Messages API (ANTHROPIC_API_KEY)");
        eprintln!("      openai               OpenAI Chat Completions (OPENAI_API_KEY)");
        eprintln!(
            "      leanstral            Leanstral hosted API (LEANSTRAL_API_KEY + --base-url)"
        );
        eprintln!("      leanstral-local      Leanstral self-hosted (localhost, no auth)");
        eprintln!(
            "      openai-compat        Generic OpenAI-compatible (--base-url, optional auth)"
        );
        eprintln!("  --api-key <key>               API key (or set env var per backend)");
        eprintln!("  --base-url <url>              API base URL (override default endpoint)");
        std::process::exit(1);
    }

    let lean_file = args[1].clone();

    // Defaults
    let mut lake_dir = String::from("lean");
    let mut max_iterations = 10u32;
    let mut model: Option<String> = None;
    let mut system_prompt_file = Some(DEFAULT_SYSTEM_PROMPT.to_string());
    let mut system_prompt_explicit = false;
    let mut transcript_path: Option<String> = None;
    let mut save_transcript: Option<String> = None;
    // --notes takes an optional explicit path; None means "derive from lean_file".
    let mut notes_flag = false;
    let mut notes_path: Option<String> = None;
    let mut replay_path: Option<String> = None;
    let mut verify = false;
    let mut allow_toolchain_mismatch = false;
    let mut use_lsp = false;
    let mut samples_per_iter = 1u32;
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
                system_prompt_explicit = true;
            }
            "--transcript" => {
                transcript_path = Some(flag_value(&args, &mut i, "--transcript"));
            }
            "--save-transcript" => {
                save_transcript = Some(flag_value(&args, &mut i, "--save-transcript"));
            }
            "--notes" => {
                notes_flag = true;
                // Optional path: if the next arg does not start with '--' and is not the lean file, use it.
                if let Some(next) = args.get(i + 1) {
                    if !next.starts_with("--") {
                        notes_path = Some(next.clone());
                        i += 1;
                    }
                }
            }
            "--replay" => {
                replay_path = Some(flag_value(&args, &mut i, "--replay"));
            }
            "--verify" => {
                verify = true;
            }
            "--allow-toolchain-mismatch" => {
                allow_toolchain_mismatch = true;
            }
            "--lsp" => {
                use_lsp = true;
            }
            "--samples-per-iter" => {
                samples_per_iter = flag_value(&args, &mut i, "--samples-per-iter")
                    .parse()
                    .ok()
                    .filter(|&n| n >= 1)
                    .unwrap_or_else(|| {
                        eprintln!("invalid --samples-per-iter value (must be >= 1)");
                        std::process::exit(1);
                    });
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

    // ── Replay mode (no LLM) ─────────────────────────────────────────────────
    if let Some(ref rpath) = replay_path {
        eprintln!("[proof-pilot] replay mode: {}", rpath);
        match replay::replay(
            rpath,
            &lean_file,
            &lake_dir,
            verify,
            allow_toolchain_mismatch,
        ) {
            Ok(result) => {
                eprintln!("[replay] applied {} step(s)", result.steps_applied);
                if verify {
                    for step in &result.steps {
                        let status = match step.build_passed {
                            Some(true) => "PASS",
                            Some(false) => "FAIL",
                            None => "skip",
                        };
                        eprintln!("[replay] step {} — {}", step.index, status);
                    }
                    if result.final_build_passed {
                        eprintln!("[replay] final build: PASSED");
                    } else {
                        eprintln!("[replay] final build: FAILED");
                        std::process::exit(1);
                    }
                }
            }
            Err(e) => {
                eprintln!("[replay] error: {}", e);
                std::process::exit(2);
            }
        }
        return;
    }

    // ── Normal proof-pilot session ───────────────────────────────────────────

    // Read system prompt from file if provided. The default falls back to an
    // embedded crate-local prompt so the crates.io binary is self-contained.
    let system_prompt =
        system_prompt_file.map(|path| read_system_prompt(&path, system_prompt_explicit));

    // Construct backend
    let backend = make_backend(&backend_name, model, api_key, base_url).unwrap_or_else(|e| {
        eprintln!("error: {e}");
        std::process::exit(1);
    });

    eprintln!("[proof-pilot] backend: {}", backend.name());

    let config = SessionConfig {
        lean_file: lean_file.clone(),
        lake_dir: lake_dir.clone(),
        max_iterations,
        system_prompt,
        transcript: transcript_path,
        use_lsp,
        samples_per_iter,
    };

    let (result, journal) = session::run(&config, backend.as_ref());

    // ── Post-session actions ─────────────────────────────────────────────────

    // Save versioned JSON transcript if requested.
    if let Some(ref path) = save_transcript {
        let mathlib_rev = transcript::read_mathlib_rev(&lake_dir);
        match transcript::save(&journal, path, mathlib_rev) {
            Ok(()) => eprintln!("[proof-pilot] transcript saved to: {}", path),
            Err(e) => eprintln!("[proof-pilot] warning: could not save transcript: {}", e),
        }
    }

    // Write NOTES.md when the flag is given, or automatically on failure.
    let should_write_notes = notes_flag
        || matches!(
            &result,
            SessionResult::Exhausted { .. } | SessionResult::Failed(_)
        );

    if should_write_notes {
        let effective_notes_path = notes_path
            .clone()
            // Default: <lean_file>.notes.md
            .unwrap_or_else(|| format!("{}.notes.md", lean_file));

        let md = render_notes(&journal);
        match std::fs::write(&effective_notes_path, md) {
            Ok(()) => eprintln!("[proof-pilot] notes written to: {}", effective_notes_path),
            Err(e) => eprintln!("[proof-pilot] warning: could not write notes: {}", e),
        }
    }

    // Report final result.
    match result {
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

fn read_system_prompt(path: &str, explicit: bool) -> String {
    match std::fs::read_to_string(path) {
        Ok(prompt) => prompt,
        Err(e) if explicit => {
            eprintln!("error reading system prompt {path}: {e}");
            std::process::exit(1);
        }
        Err(e) if path == DEFAULT_SYSTEM_PROMPT => {
            eprintln!(
                "[proof-pilot] warning: could not read default system prompt {path}: {e}; \
                 using bundled prompt"
            );
            EMBEDDED_SYSTEM_PROMPT.to_string()
        }
        Err(e) => {
            eprintln!("error reading system prompt {path}: {e}");
            std::process::exit(1);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn embedded_default_system_prompt_is_available() {
        assert!(EMBEDDED_SYSTEM_PROMPT.contains("Lean 4"));
        assert!(EMBEDDED_SYSTEM_PROMPT.contains("Do not use `sorry`"));
        assert!(EMBEDDED_SYSTEM_PROMPT.contains("Do not modify the theorem statement"));
    }
}
