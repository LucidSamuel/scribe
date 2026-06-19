//! Orchestration logic for `scribe verify` and `scribe demo`.

use std::fs;
use std::path::Path;
use std::process;

use halva_bridge::{parse_halva_output, scaffold_raw, scaffold_soundness, SpecConfig};
use proof_pilot::backend::make_backend;
use proof_pilot::journal::SessionJournal;
use proof_pilot::notes::render_notes;
use proof_pilot::session::{self, SessionConfig, SessionResult};
use proof_pilot::transcript;

use crate::demo_cmd::DemoArgs;
use crate::extract;
use crate::verify_cmd::VerifyArgs;

// ── Default paths / environment ──────────────────────────────────────────────

const FALLBACK_SYSTEM_PROMPT: &str = "prompts/lean-prover.md";

/// Resolve the system prompt path:
/// 1. Explicit `--system-prompt <file>` flag.
/// 2. `$SCRIBE_PROMPTS_DIR/lean-prover.md` environment variable.
/// 3. `prompts/lean-prover.md` relative to CWD.
fn resolve_system_prompt(explicit: Option<&str>) -> Option<String> {
    resolve_system_prompt_from(explicit, std::env::var("SCRIBE_PROMPTS_DIR").ok())
}

/// Pure resolution split out of `resolve_system_prompt` so it can be unit
/// tested without mutating the process environment (which races under the
/// parallel test runner).
fn resolve_system_prompt_from(
    explicit: Option<&str>,
    prompts_dir: Option<String>,
) -> Option<String> {
    if let Some(path) = explicit {
        return Some(path.to_string());
    }
    if let Some(dir) = prompts_dir {
        let path = format!("{dir}/lean-prover.md");
        if Path::new(&path).exists() {
            return Some(path);
        }
    }
    Some(FALLBACK_SYSTEM_PROMPT.to_string())
}

/// Resolve the lake dir: explicit `--lake-dir` → `$LAKE_DIR` → `lean`.
fn resolve_lake_dir(explicit: Option<&str>) -> String {
    resolve_dir(explicit, std::env::var("LAKE_DIR").ok(), "lean")
}

/// Resolve the bundled examples dir (for `demo --live` assets):
/// `$SCRIBE_EXAMPLES_DIR` (set to /opt/scribe/examples in the Docker image)
/// → `examples` relative to CWD (the repo root).
fn resolve_examples_dir() -> String {
    resolve_dir(None, std::env::var("SCRIBE_EXAMPLES_DIR").ok(), "examples")
}

/// Pure precedence resolver: explicit flag → environment value → default.
/// Kept free of global state so unit tests need not mutate the process env.
fn resolve_dir(explicit: Option<&str>, env: Option<String>, default: &str) -> String {
    explicit
        .map(str::to_string)
        .or(env)
        .unwrap_or_else(|| default.to_string())
}

// ── scribe verify ────────────────────────────────────────────────────────────

pub fn run_verify(args: VerifyArgs) {
    // 1. Extraction phase.
    let halva_content = if let Some(ref path) = args.halva_output {
        extract::from_halva_file(path)
    } else if let Some(ref dir) = args.circuit {
        extract::from_circuit_project(dir)
    } else {
        unreachable!("main already checks that one of --halva-output / --circuit is set");
    };

    // 2. Parse the Halva output.
    let halva = parse_halva_output(&halva_content).unwrap_or_else(|e| {
        eprintln!("error: failed to parse Halva output: {e}");
        process::exit(1);
    });
    eprintln!(
        "[scribe] parsed namespace: {}, meets_constraints: found",
        halva.namespace
    );

    // 3. Scaffold the combined Lean file.
    let combined = if let Some(ref snippet_path) = args.spec_file {
        let snippet = fs::read_to_string(snippet_path).unwrap_or_else(|e| {
            eprintln!("error: cannot read --spec-file {snippet_path}: {e}");
            process::exit(1);
        });
        scaffold_raw(&halva, &snippet)
    } else if let Some(ref spec_body) = args.spec {
        let config = SpecConfig {
            spec_body: spec_body.clone(),
            extra_imports: args.extra_imports.clone(),
        };
        scaffold_soundness(&halva, &config)
    } else {
        eprintln!("error: one of --spec or --spec-file is required");
        process::exit(1);
    };

    // 4. Determine output path.
    let out_path = args.output.clone().unwrap_or_else(|| {
        let src = args
            .halva_output
            .as_deref()
            .or(args.circuit.as_deref())
            .unwrap_or("output");
        let p = Path::new(src);
        let stem = p.file_stem().unwrap_or_default().to_string_lossy();
        let parent = p.parent().unwrap_or(Path::new("."));
        parent
            .join(format!("{stem}_soundness.lean"))
            .to_string_lossy()
            .into_owned()
    });

    // 5. Write the scaffolded file.
    fs::write(&out_path, &combined).unwrap_or_else(|e| {
        eprintln!("error: cannot write {out_path}: {e}");
        process::exit(1);
    });
    eprintln!("[scribe] wrote {out_path}");

    // Scaffold-only mode: write the Lean file (still containing `sorry`) and stop.
    if args.no_prove {
        eprintln!("[scribe] --no-prove: scaffold written, skipping the proof loop");
        println!("{out_path}");
        return;
    }

    // 6. Run the proof loop (default). `scribe verify` only exits 0 once the
    //    Lean kernel accepts the proof; pass --no-prove for scaffold-only.
    eprintln!("[scribe] launching proof-pilot...");

    let lake_dir = resolve_lake_dir(args.lake_dir.as_deref());
    let system_prompt_path = resolve_system_prompt(args.system_prompt.as_deref());
    let system_prompt = system_prompt_path.map(|path| {
        fs::read_to_string(&path).unwrap_or_else(|e| {
            eprintln!("error: cannot read system prompt {path}: {e}");
            process::exit(1);
        })
    });

    let backend = make_backend(
        &args.backend,
        args.model.clone(),
        args.api_key.clone(),
        args.base_url.clone(),
    );
    eprintln!("[scribe] backend: {}", backend.name());

    let config = SessionConfig {
        lean_file: out_path.clone(),
        lake_dir: lake_dir.clone(),
        max_iterations: args.max_iters,
        system_prompt,
        transcript: args.transcript.clone(),
        use_lsp: args.lsp,
    };

    let (result, journal) = session::run(&config, backend.as_ref());

    // ── Post-session actions (mirror proof-pilot's main.rs) ──────────────────
    // Save a versioned JSON transcript if requested.
    if let Some(ref path) = args.save_transcript {
        let mathlib_rev = transcript::read_mathlib_rev(&lake_dir);
        match transcript::save(&journal, path, mathlib_rev) {
            Ok(()) => eprintln!("[scribe] transcript saved to: {path}"),
            Err(e) => eprintln!("[scribe] warning: could not save transcript: {e}"),
        }
    }

    // Write NOTES.md when --notes is given (with or without a path), or
    // automatically on a non-proven outcome.
    let failed = matches!(
        &result,
        SessionResult::Exhausted { .. } | SessionResult::Failed(_)
    );
    match &args.notes {
        Some(explicit) => {
            let path = explicit
                .clone()
                .unwrap_or_else(|| format!("{out_path}.notes.md"));
            write_notes(&journal, &path);
        }
        None if failed => write_notes(&journal, &format!("{out_path}.notes.md")),
        None => {}
    }

    handle_session_result(result, &out_path);
}

/// Render and write a NOTES.md debugging report from the session journal.
fn write_notes(journal: &SessionJournal, path: &str) {
    let md = render_notes(journal);
    match fs::write(path, md) {
        Ok(()) => eprintln!("[scribe] notes written to: {path}"),
        Err(e) => eprintln!("[scribe] warning: could not write notes: {e}"),
    }
}

fn handle_session_result(result: SessionResult, lean_file: &str) {
    match result {
        SessionResult::Proven { iterations } => {
            if iterations == 0 {
                eprintln!("[scribe] already proven (no LLM iterations needed)");
            } else {
                eprintln!("[scribe] proof complete in {iterations} iteration(s)");
            }
            println!("PROVEN: {lean_file}");
        }
        SessionResult::Exhausted {
            iterations,
            last_error,
        } => {
            eprintln!("[scribe] gave up after {iterations} iteration(s)");
            eprintln!("last build error:\n{last_error}");
            process::exit(1);
        }
        SessionResult::Failed(msg) => {
            eprintln!("[scribe] fatal error: {msg}");
            process::exit(2);
        }
    }
}

// ── scribe demo ──────────────────────────────────────────────────────────────

/// Bundled range-check IR snippet for the dry-run demo.
/// This is from examples/range-check/gadget.toml (8-bit variant).
const DEMO_GADGET_DESCRIPTION: &str =
    "// proving an 8-bit range check: every witness bit is constrained to {0,1} \
     and they recompose the input value";

const DEMO_IR_SNIPPET: &str = r#"# gadget.toml (range-check-8bit)
name = "range-check-8bit"
soundness_spec = "∃ k : Fin 256, (k.val : ZMod p) = x"

[[constraints]]
label = "bit_0"
terms = [{ coeff = "1", vars = [1, 1] }, { coeff = "-1", vars = [1] }]
# ... (8 boolean bit constraints + 1 decomposition constraint)"#;

const DEMO_SCAFFOLD_SNIPPET: &str = r#"-- Generated Lean 4 scaffold (lean-emit → sorry stub)
theorem range_check_8bit_sound
    (x : ZMod p) (bits : Fin 8 → ZMod p)
    (h_bit : ∀ i : Fin 8, bits i * (bits i - 1) = 0)
    (h_decomp : (∑ i : Fin 8, bits i * (2 : ZMod p) ^ (i : ℕ)) = x) :
    ∃ k : Fin 256, (k.val : ZMod p) = x := by
  sorry  -- ← proof-pilot will fill this in"#;

const DEMO_PROOF_LOOP_SNIPPET: &str = r#"-- proof-pilot loop (iteration 1/10) → backend: claude-cli
-- Lean LSP feedback:  unsolved goal  ⊢ ∃ k : Fin 256, (k.val : ZMod p) = x
-- Tactic probe: `ring` — no progress; `norm_num` — no progress
-- LLM response: extracted proof body via linear_combination + Fin witness
-- patch applied: OK  →  lake build: SUCCESS (0 errors, 0 sorry)"#;

const DEMO_KERNEL_SNIPPET: &str = r#"-- Lean kernel check (lake build + lake env lean ZkGadgets/RangeCheck.lean)
-- Result: ✓  no errors, no sorry, no axioms beyond Mathlib"#;

const DEMO_STAGE_LABELS: [&str; 4] = [
    "Stage 1: IR → scaffold",
    "Stage 2: sorry-stub Lean",
    "Stage 3: proof loop (LLM + lake build feedback)",
    "Stage 4: kernel-checked proof",
];

pub fn run_demo(args: DemoArgs) {
    let lake_dir = resolve_lake_dir(args.lake_dir.as_deref());

    if args.verify {
        run_demo_verify(&lake_dir);
    } else if args.live {
        run_demo_live(&args, &lake_dir);
    } else {
        run_demo_dryrun();
    }
}

/// Default demo tier: dry-run, no Lean / API key required.
fn run_demo_dryrun() {
    println!("scribe demo — range-check pipeline walkthrough");
    println!("{}", "=".repeat(60));
    println!();
    println!("{DEMO_GADGET_DESCRIPTION}");
    println!();

    println!("{}:", DEMO_STAGE_LABELS[0]);
    println!("{DEMO_IR_SNIPPET}");
    println!();

    println!("{}:", DEMO_STAGE_LABELS[1]);
    println!("{DEMO_SCAFFOLD_SNIPPET}");
    println!();

    println!("{}:", DEMO_STAGE_LABELS[2]);
    println!("{DEMO_PROOF_LOOP_SNIPPET}");
    println!();

    println!("{}:", DEMO_STAGE_LABELS[3]);
    println!("{DEMO_KERNEL_SNIPPET}");
    println!();

    println!("{}", "=".repeat(60));
    println!("To verify the pre-computed proof:  scribe demo --verify  (needs Lean)");
    println!("To run the live LLM loop:          scribe demo --live    (needs Lean + API key)");
}

/// --verify tier: run `lake build` on the pre-computed RangeCheck.lean.
fn run_demo_verify(lake_dir: &str) {
    let lean_file = format!("{lake_dir}/ZkGadgets/RangeCheck.lean");

    eprintln!("[scribe demo --verify] checking {lean_file}");

    // Delegate to proof_pilot's lake runner.
    use proof_pilot::lean_runner::run_lake_build_for_file;

    let lake_path = Path::new(lake_dir);
    let lean_path = Path::new(&lean_file);

    let result = run_lake_build_for_file(lake_path, lean_path).unwrap_or_else(|e| {
        eprintln!("error: lake build failed: {e}");
        process::exit(1);
    });

    if result.success {
        println!("[scribe demo --verify] PASSED: {lean_file} is kernel-checked");
    } else {
        eprintln!("[scribe demo --verify] FAILED:");
        eprintln!("{}", result.combined);
        process::exit(1);
    }
}

/// --live tier: run the full LLM proof loop on a fresh scaffold.
fn run_demo_live(args: &DemoArgs, lake_dir: &str) {
    eprintln!("[scribe demo --live] building fresh scaffold from bundled assets...");

    // Use the halva-range-check extracted.lean as the demo Halva output.
    // Resolve via $SCRIBE_EXAMPLES_DIR so this works from the installed image
    // (WORKDIR /workspace) as well as from the repo root.
    let examples_dir = resolve_examples_dir();
    let halva_content_path = format!("{examples_dir}/halva-range-check/extracted.lean");
    let spec_file_path = format!("{examples_dir}/halva-range-check/spec.lean");

    let halva_content = fs::read_to_string(&halva_content_path).unwrap_or_else(|e| {
        eprintln!(
            "error: cannot read bundled demo asset {halva_content_path}: {e}\n\
             Set $SCRIBE_EXAMPLES_DIR or run from the scribe repo root."
        );
        process::exit(1);
    });

    let halva = parse_halva_output(&halva_content).unwrap_or_else(|e| {
        eprintln!("error: failed to parse bundled Halva output: {e}");
        process::exit(1);
    });

    let snippet = fs::read_to_string(&spec_file_path).unwrap_or_else(|e| {
        eprintln!(
            "error: cannot read bundled spec {spec_file_path}: {e}\n\
             Set $SCRIBE_EXAMPLES_DIR or run from the scribe repo root."
        );
        process::exit(1);
    });

    let combined = scaffold_raw(&halva, &snippet);

    // Write a temporary output file inside the lake dir.
    let out_path = format!("{lake_dir}/ZkGadgets/HalvaRangeCheckLive.lean");
    fs::write(&out_path, &combined).unwrap_or_else(|e| {
        eprintln!("error: cannot write live scaffold {out_path}: {e}");
        process::exit(1);
    });
    eprintln!("[scribe demo --live] wrote {out_path}");

    let system_prompt_path = resolve_system_prompt(args.system_prompt.as_deref());
    let system_prompt = system_prompt_path.map(|path| {
        fs::read_to_string(&path).unwrap_or_else(|e| {
            eprintln!("error: cannot read system prompt {path}: {e}");
            process::exit(1);
        })
    });

    let backend = make_backend(
        &args.backend,
        args.model.clone(),
        args.api_key.clone(),
        args.base_url.clone(),
    );
    eprintln!("[scribe demo --live] backend: {}", backend.name());

    let config = SessionConfig {
        lean_file: out_path.clone(),
        lake_dir: lake_dir.to_string(),
        max_iterations: 10,
        system_prompt,
        transcript: None,
        use_lsp: false,
    };

    let (result, _journal) = session::run(&config, backend.as_ref());
    handle_session_result(result, &out_path);
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Confirm that the dry-run demo produces output with the gadget description
    /// and all four stage labels. No Lean / API key required — this runs in CI.
    #[test]
    fn demo_dryrun_output_contains_required_content() {
        // Capture stdout by running the dry-run logic and inspecting the expected
        // strings in the embedded constants (unit-level check; we cannot capture
        // println! output here without extra machinery, but we can verify the
        // constants are correct and that the stage labels array is complete).

        // The gadget description must mention range check semantics.
        assert!(
            DEMO_GADGET_DESCRIPTION.contains("range check"),
            "gadget description should mention range check"
        );
        assert!(
            DEMO_GADGET_DESCRIPTION.contains("{0,1}"),
            "gadget description should mention bit constraint"
        );

        // All 4 stage labels must be present and non-empty.
        assert_eq!(
            DEMO_STAGE_LABELS.len(),
            4,
            "should have exactly 4 stage labels"
        );
        for label in DEMO_STAGE_LABELS {
            assert!(!label.is_empty(), "stage label must not be empty");
        }
        assert!(
            DEMO_STAGE_LABELS[0].contains("IR"),
            "stage 1 should mention IR"
        );
        assert!(
            DEMO_STAGE_LABELS[1].contains("sorry"),
            "stage 2 should mention sorry"
        );
        assert!(
            DEMO_STAGE_LABELS[2].contains("loop"),
            "stage 3 should mention loop"
        );
        assert!(
            DEMO_STAGE_LABELS[3].contains("kernel"),
            "stage 4 should mention kernel"
        );

        // Snippet constants must contain representative tokens.
        assert!(DEMO_IR_SNIPPET.contains("range-check-8bit"));
        assert!(DEMO_SCAFFOLD_SNIPPET.contains("sorry"));
        assert!(DEMO_PROOF_LOOP_SNIPPET.contains("lake build"));
        assert!(DEMO_KERNEL_SNIPPET.contains("kernel"));
    }

    // These exercise the pure resolvers directly, so they never touch the
    // process environment and cannot race under the parallel test runner.

    #[test]
    fn resolve_dir_uses_explicit_first() {
        // Explicit flag wins even when an env value is present.
        assert_eq!(
            resolve_dir(Some("custom-lean"), Some("env-lean".to_string()), "lean"),
            "custom-lean"
        );
    }

    #[test]
    fn resolve_dir_falls_back_to_default() {
        assert_eq!(resolve_dir(None, None, "lean"), "lean");
    }

    #[test]
    fn resolve_dir_uses_env_when_no_flag() {
        assert_eq!(
            resolve_dir(None, Some("my-lean-dir".to_string()), "lean"),
            "my-lean-dir"
        );
    }

    #[test]
    fn resolve_system_prompt_uses_explicit_first() {
        assert_eq!(
            resolve_system_prompt_from(Some("/custom/prompt.md"), None).as_deref(),
            Some("/custom/prompt.md")
        );
    }

    #[test]
    fn resolve_system_prompt_falls_back_to_default() {
        assert_eq!(
            resolve_system_prompt_from(None, None).as_deref(),
            Some(FALLBACK_SYSTEM_PROMPT)
        );
    }
}
