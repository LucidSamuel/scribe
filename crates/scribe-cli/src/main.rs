use clap::{Parser, Subcommand};
use std::process;

mod extract;
mod init;
mod orchestrate;

/// scribe — formal verification of ZK circuit gadgets using Lean 4.
///
/// scribe bridges Halva halo2-to-Lean extraction with proof-pilot's LLM-driven
/// proof loop. The user authors the Halva extractor program; scribe takes it
/// from there to a kernel-checked Lean 4 proof.
#[derive(Parser)]
#[command(name = "scribe", version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
// VerifyArgs carries many flags and is far larger than DemoArgs; the size
// difference is expected for a CLI dispatch enum that is constructed once.
#[allow(clippy::large_enum_variant)]
enum Commands {
    /// Verify a ZK gadget: extract → scaffold → prove.
    ///
    /// Takes a Halva extractor project or pre-extracted Halva output, merges your
    /// specification, and runs the LLM proof loop until the Lean kernel accepts
    /// the proof or the budget is exhausted. Pass `--no-prove` to stop after
    /// writing the scaffold and skip the proof loop.
    Verify(verify_cmd::VerifyArgs),

    /// Run the range-check demonstration pipeline (no Lean or API key required
    /// by default).
    ///
    /// Three tiers:
    ///   (default)  Dry-run: walk through the pipeline conceptually using bundled
    ///              assets. ~30s, zero external dependencies.
    ///   --verify   Run `lake build` on the pre-computed RangeCheck.lean proof.
    ///              Requires Lean / Lake installed; no API key needed.
    ///   --live     Run the full LLM proof loop on a fresh scaffold. Requires
    ///              Lean and a configured backend (API key or claude CLI).
    Demo(demo_cmd::DemoArgs),

    /// Generate a Halva extractor project template for a raw halo2 circuit.
    ///
    /// The generated project is the editable adapter that `scribe verify
    /// --circuit` expects: a Cargo project whose `cargo run --release` prints
    /// Halva Lean output to stdout.
    Init(init_cmd::InitArgs),

    /// Adversarially attack a gadget's spec: hunt for a kernel-checked
    /// counterexample (verdict engine C4).
    ///
    /// Emits the soundness statement at a concrete small prime, NEGATED, and
    /// runs an LLM refuter loop that tries to prove the negation — i.e. exhibit
    /// witness values satisfying every constraint while violating the spec.
    ///
    /// Exit codes: 2 = REFUTED (a kernel-checked counterexample exists — the
    /// circuit is under-constrained or the spec is wrong); 0 = SURVIVED (no
    /// refutation found within the budget; evidence, not proof, of soundness);
    /// 1 = infrastructure error.
    Refute(refute_cmd::RefuteArgs),

    /// Judge a gadget: prove AND attack, emit a verdict.
    ///
    /// Runs the prover loop first (a kernel-accepted proof settles the question
    /// — no counterexample can exist). If proving exhausts its budget, runs the
    /// adversarial refuter. The verdict is backed by a kernel-checked artifact
    /// whenever it is SOUND or UNSOUND.
    ///
    /// Exit codes (stable — script against them):
    ///   0 = SOUND        (kernel-accepted proof of the spec)
    ///   1 = UNDETERMINED (neither proof nor refutation within budget)
    ///   2 = UNSOUND      (kernel-checked counterexample to the spec)
    ///   3 = infrastructure error
    Judge(judge_cmd::JudgeArgs),

    /// Import a circom .r1cs circuit (plus its .sym signal map) as a
    /// reviewable gadget TOML.
    ///
    /// Parses the iden3 R1CS binary format, expands each rank-1 row into
    /// scribe's sum-of-products IR (coefficients canonicalized to signed
    /// form), and writes gadget TOML — the auditable artifact the rest of the
    /// pipeline consumes: `scribe judge --gadget out.toml`, `scribe refute`,
    /// the eval suite. R1CS carries constraints, never intent, so the
    /// soundness spec is yours to state via --spec.
    ImportR1cs(import_r1cs_cmd::ImportR1csArgs),
}

mod verify_cmd {
    use clap::Args;

    #[derive(Args)]
    pub struct VerifyArgs {
        /// Read a pre-extracted Halva .lean file (fast path; mutually exclusive
        /// with --circuit).
        #[arg(long, value_name = "FILE", conflicts_with = "circuit")]
        pub halva_output: Option<String>,

        /// Path to a Halva EXTRACTOR PROJECT directory. scribe will run
        /// `cargo run --release` inside it and capture the emitted Lean output.
        /// NOTE: this is NOT a raw halo2 circuit directory — the user must
        /// first author a Halva extractor program targeting their circuit.
        /// (Mutually exclusive with --halva-output.)
        #[arg(long, value_name = "DIR", conflicts_with = "halva_output")]
        pub circuit: Option<String>,

        /// Lean proposition body for the Spec definition (auto-generates
        /// `def Spec` + `theorem soundness ... := by sorry`).
        /// Mutually exclusive with --spec-file.
        #[arg(long, value_name = "EXPR", conflicts_with = "spec_file")]
        pub spec: Option<String>,

        /// Path to a raw Lean snippet containing your Spec definition and
        /// soundness theorem (with `sorry`). Inserted verbatim before the
        /// closing `end`. Mutually exclusive with --spec.
        #[arg(long, value_name = "FILE", conflicts_with = "spec")]
        pub spec_file: Option<String>,

        /// Extra Lean import to add at the file header (repeatable).
        /// Only valid with --spec; not accepted with --spec-file.
        #[arg(long = "extra-import", value_name = "MODULE")]
        pub extra_imports: Vec<String>,

        /// Output path for the scaffolded Lean file.
        #[arg(short = 'o', long, value_name = "FILE")]
        pub output: Option<String>,

        /// Scaffold only: write the Lean file and stop, skipping the proof loop.
        /// By default `scribe verify` runs proof-pilot until the Lean kernel
        /// accepts the proof (or the iteration budget is exhausted).
        #[arg(long)]
        pub no_prove: bool,

        /// Skip the `#audit_axioms` gate and its `ZkGadgets.Audit` import.
        /// Use when the target lake dir is not scribe's own `lean/` project
        /// (the gate's command is defined by scribe's ZkGadgets library).
        /// Without the gate, an unproven scaffold builds with a warning
        /// instead of failing, so prefer keeping it on.
        #[arg(long)]
        pub no_audit_gate: bool,

        /// Lake project directory (default: $LAKE_DIR env var, else `lean`).
        #[arg(long, value_name = "DIR")]
        pub lake_dir: Option<String>,

        /// Maximum number of proof iterations (default: 10).
        #[arg(long, value_name = "N", default_value = "10")]
        pub max_iters: u32,

        /// LLM backend to use (default: claude).
        ///
        /// Available backends:
        ///   claude          Claude CLI (shells out to `claude -p`)
        ///   anthropic       Anthropic Messages API (ANTHROPIC_API_KEY)
        ///   openai          OpenAI Chat Completions (OPENAI_API_KEY)
        ///   leanstral       Leanstral hosted API (LEANSTRAL_API_KEY + --base-url)
        ///   leanstral-local Leanstral self-hosted (localhost, no auth)
        ///   openai-compat   Generic OpenAI-compatible (--base-url, optional auth)
        #[arg(long, value_name = "NAME", default_value = "claude")]
        pub backend: String,

        /// Model name override (backend-specific default is used if not set).
        #[arg(long, value_name = "MODEL")]
        pub model: Option<String>,

        /// API key for the selected backend (or set the backend-specific env var).
        #[arg(long, value_name = "KEY")]
        pub api_key: Option<String>,

        /// API base URL override (required for leanstral, openai-compat).
        #[arg(long, value_name = "URL")]
        pub base_url: Option<String>,

        /// System prompt file path (default: $SCRIBE_PROMPTS_DIR/lean-prover.md,
        /// else `prompts/lean-prover.md`).
        #[arg(long, value_name = "FILE")]
        pub system_prompt: Option<String>,

        /// Transcript log file path (optional).
        #[arg(long, value_name = "FILE")]
        pub transcript: Option<String>,

        /// Save the session journal as versioned JSON (coexists with --transcript).
        #[arg(long, value_name = "FILE")]
        pub save_transcript: Option<String>,

        /// Write a NOTES.md debugging report. With no value, defaults to
        /// `<output>.notes.md`. Always written when this flag is present; also
        /// written automatically on failure even without the flag.
        #[arg(long, value_name = "FILE", num_args = 0..=1)]
        pub notes: Option<Option<String>>,

        /// Use Lean LSP for structured feedback instead of raw `lake build` text.
        #[arg(long)]
        pub lsp: bool,

        /// Best-of-n: sampled proof attempts per iteration; the kernel filters
        /// (default: 1). Lake-build mode only.
        #[arg(long, value_name = "K", default_value = "1")]
        pub samples_per_iter: u32,
    }
}

mod demo_cmd {
    use clap::Args;

    #[derive(Args)]
    pub struct DemoArgs {
        /// Run `lake build` on the pre-computed RangeCheck.lean proof.
        /// Requires Lean / Lake. Mutually exclusive with --live.
        #[arg(long, conflicts_with = "live")]
        pub verify: bool,

        /// Run the full LLM proof loop on a fresh scaffold from the bundled
        /// range-check assets. Requires Lean and a configured backend.
        /// Mutually exclusive with --verify.
        #[arg(long, conflicts_with = "verify")]
        pub live: bool,

        /// Lake project directory for --verify / --live
        /// (default: $LAKE_DIR env var, else `lean`).
        #[arg(long, value_name = "DIR")]
        pub lake_dir: Option<String>,

        /// LLM backend to use with --live (default: claude).
        #[arg(long, value_name = "NAME", default_value = "claude")]
        pub backend: String,

        /// Model name override for --live.
        #[arg(long, value_name = "MODEL")]
        pub model: Option<String>,

        /// API key for --live backend.
        #[arg(long, value_name = "KEY")]
        pub api_key: Option<String>,

        /// API base URL override for --live.
        #[arg(long, value_name = "URL")]
        pub base_url: Option<String>,

        /// System prompt file for --live
        /// (default: $SCRIBE_PROMPTS_DIR/lean-prover.md, else `prompts/lean-prover.md`).
        #[arg(long, value_name = "FILE")]
        pub system_prompt: Option<String>,
    }
}

mod init_cmd {
    use clap::Args;

    #[derive(Args)]
    pub struct InitArgs {
        /// Path to the raw halo2 circuit crate or source directory to wrap.
        #[arg(long, value_name = "DIR")]
        pub circuit: String,

        /// Output directory for the generated extractor project.
        /// Defaults to `<circuit-package>-halva-extractor`.
        #[arg(short = 'o', long, value_name = "DIR")]
        pub output: Option<String>,

        /// Base name for the generated package and Lean namespace.
        /// Defaults to the circuit crate package name when Cargo.toml is present.
        #[arg(long, value_name = "NAME")]
        pub name: Option<String>,

        /// Overwrite template files when the output directory already exists.
        #[arg(long)]
        pub force: bool,

        /// Git URL for the Halva extractor dependency.
        ///
        /// If omitted, the generated Cargo.toml contains a TODO placeholder
        /// instead of a guessed repository URL.
        #[arg(long, value_name = "URL")]
        pub halva_git: Option<String>,

        /// Optional Halva git revision to pin in the generated Cargo.toml.
        #[arg(long, value_name = "REV")]
        pub halva_rev: Option<String>,
    }
}

mod refute_cmd {
    use clap::Args;

    #[derive(Args)]
    pub struct RefuteArgs {
        /// Gadget IR file (TOML) whose soundness spec should be attacked.
        #[arg(long, value_name = "FILE")]
        pub gadget: String,

        /// Probe prime for the finite model. Default: the smallest prime
        /// satisfying every `p > N` hypothesis the gadget declares (floor 5).
        #[arg(long, value_name = "P")]
        pub prime: Option<u64>,

        /// Output path for the refutation scaffold
        /// (default: `<lake-dir>/ZkGadgets/Bench/Refute<Name>.lean`).
        #[arg(short = 'o', long, value_name = "FILE")]
        pub output: Option<String>,

        /// Write the scaffold and stop; skip the refuter loop.
        #[arg(long)]
        pub scaffold_only: bool,

        /// Lake project directory (default: $LAKE_DIR env var, else `lean`).
        #[arg(long, value_name = "DIR")]
        pub lake_dir: Option<String>,

        /// Maximum refutation attempts (default: 6).
        #[arg(long, value_name = "N", default_value = "6")]
        pub max_iters: u32,

        /// LLM backend to use (default: claude). See `scribe verify --help`.
        #[arg(long, value_name = "NAME", default_value = "claude")]
        pub backend: String,

        /// Model name override.
        #[arg(long, value_name = "MODEL")]
        pub model: Option<String>,

        /// API key for the selected backend.
        #[arg(long, value_name = "KEY")]
        pub api_key: Option<String>,

        /// API base URL override.
        #[arg(long, value_name = "URL")]
        pub base_url: Option<String>,

        /// System prompt file (default: $SCRIBE_PROMPTS_DIR/lean-refuter.md,
        /// else `prompts/lean-refuter.md`).
        #[arg(long, value_name = "FILE")]
        pub system_prompt: Option<String>,

        /// Transcript log file path (optional).
        #[arg(long, value_name = "FILE")]
        pub transcript: Option<String>,

        /// Best-of-n: sampled refutation attempts per iteration; the kernel
        /// filters (default: 1).
        #[arg(long, value_name = "K", default_value = "1")]
        pub samples_per_iter: u32,
    }
}

mod judge_cmd {
    use clap::Args;

    #[derive(Args)]
    pub struct JudgeArgs {
        /// Gadget IR file (TOML) to judge.
        #[arg(long, value_name = "FILE")]
        pub gadget: String,

        /// Probe prime for the refutation phase (default: auto from `p > N`
        /// hypotheses, floor 5).
        #[arg(long, value_name = "P")]
        pub prime: Option<u64>,

        /// Maximum prover iterations (default: 5).
        #[arg(long, value_name = "N", default_value = "5")]
        pub prove_iters: u32,

        /// Maximum refuter iterations (default: 4).
        #[arg(long, value_name = "N", default_value = "4")]
        pub refute_iters: u32,

        /// Best-of-n: sampled attempts per iteration in BOTH phases; the kernel
        /// filters (default: 1).
        #[arg(long, value_name = "K", default_value = "1")]
        pub samples_per_iter: u32,

        /// Lake project directory (default: $LAKE_DIR env var, else `lean`).
        #[arg(long, value_name = "DIR")]
        pub lake_dir: Option<String>,

        /// LLM backend to use (default: claude). See `scribe verify --help`.
        #[arg(long, value_name = "NAME", default_value = "claude")]
        pub backend: String,

        /// Model name override.
        #[arg(long, value_name = "MODEL")]
        pub model: Option<String>,

        /// API key for the selected backend.
        #[arg(long, value_name = "KEY")]
        pub api_key: Option<String>,

        /// API base URL override.
        #[arg(long, value_name = "URL")]
        pub base_url: Option<String>,
    }
}

mod import_r1cs_cmd {
    use clap::Args;

    #[derive(Args)]
    pub struct ImportR1csArgs {
        /// Path to the .r1cs binary (circom --r1cs output).
        #[arg(long, value_name = "FILE")]
        pub r1cs: String,

        /// Path to the companion .sym signal map (circom --sym output).
        /// Optional; without it, witnesses are named w<wire>.
        #[arg(long, value_name = "FILE")]
        pub sym: Option<String>,

        /// Soundness spec: a Lean proposition over the witness names
        /// (e.g. "ZMod.val in_ < 4"). Omitting it emits TOML without a spec,
        /// which downstream commands will refuse to judge — the spec is the
        /// human trust root, not something R1CS can supply.
        #[arg(long, value_name = "EXPR")]
        pub spec: Option<String>,

        /// Gadget name (default: the .r1cs file stem).
        #[arg(long, value_name = "NAME")]
        pub name: Option<String>,

        /// Extra hypothesis for the theorem, repeatable, as NAME:LEAN_TYPE
        /// (e.g. "hp:p > 4"). Use for load-bearing field-size bounds.
        #[arg(long = "hypothesis", value_name = "NAME:TYPE")]
        pub hypotheses: Vec<String>,

        /// Reject canonical coefficients wider than this many bits (circuits
        /// whose arithmetic only means something at the exact header prime
        /// need prime-pinned emission, which is not supported yet).
        #[arg(long, value_name = "BITS", default_value = "64")]
        pub max_coeff_bits: u64,

        /// Output TOML path (default: <r1cs stem>.gadget.toml next to input).
        #[arg(short = 'o', long, value_name = "FILE")]
        pub output: Option<String>,
    }
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Verify(args) => {
            if args.halva_output.is_none() && args.circuit.is_none() {
                eprintln!("error: one of --halva-output or --circuit is required");
                process::exit(1);
            }
            orchestrate::run_verify(args);
        }
        Commands::Demo(args) => {
            orchestrate::run_demo(args);
        }
        Commands::Init(args) => {
            init::run_init(args);
        }
        Commands::Refute(args) => {
            orchestrate::run_refute(args);
        }
        Commands::Judge(args) => {
            orchestrate::run_judge(args);
        }
        Commands::ImportR1cs(args) => {
            orchestrate::run_import_r1cs(args);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── clap structural tests (no filesystem / network access) ──────────────

    #[test]
    fn verify_halva_output_accepted() {
        let cli = Cli::try_parse_from([
            "scribe",
            "verify",
            "--halva-output",
            "out.lean",
            "--spec",
            "True",
        ])
        .expect("should parse");
        if let Commands::Verify(args) = cli.command {
            assert_eq!(args.halva_output.as_deref(), Some("out.lean"));
            assert_eq!(args.spec.as_deref(), Some("True"));
            assert!(args.circuit.is_none());
        } else {
            panic!("expected Verify");
        }
    }

    #[test]
    fn verify_circuit_accepted() {
        let cli = Cli::try_parse_from([
            "scribe",
            "verify",
            "--circuit",
            "/path/to/extractor",
            "--spec",
            "True",
        ])
        .expect("should parse");
        if let Commands::Verify(args) = cli.command {
            assert_eq!(args.circuit.as_deref(), Some("/path/to/extractor"));
            assert!(args.halva_output.is_none());
        } else {
            panic!("expected Verify");
        }
    }

    #[test]
    fn verify_halva_output_and_circuit_are_mutually_exclusive() {
        let result = Cli::try_parse_from([
            "scribe",
            "verify",
            "--halva-output",
            "out.lean",
            "--circuit",
            "dir",
        ]);
        assert!(result.is_err(), "clap should reject both flags together");
    }

    #[test]
    fn verify_spec_and_spec_file_are_mutually_exclusive() {
        let result = Cli::try_parse_from([
            "scribe",
            "verify",
            "--halva-output",
            "out.lean",
            "--spec",
            "True",
            "--spec-file",
            "foo.lean",
        ]);
        assert!(
            result.is_err(),
            "clap should reject --spec with --spec-file"
        );
    }

    #[test]
    fn verify_extra_imports_collected() {
        let cli = Cli::try_parse_from([
            "scribe",
            "verify",
            "--halva-output",
            "out.lean",
            "--spec",
            "True",
            "--extra-import",
            "Mathlib.Data.Fin.Basic",
            "--extra-import",
            "Mathlib.Tactic",
        ])
        .expect("should parse");
        if let Commands::Verify(args) = cli.command {
            assert_eq!(
                args.extra_imports,
                vec!["Mathlib.Data.Fin.Basic", "Mathlib.Tactic"]
            );
        } else {
            panic!("expected Verify");
        }
    }

    #[test]
    fn verify_proves_by_default() {
        let cli = Cli::try_parse_from([
            "scribe",
            "verify",
            "--halva-output",
            "out.lean",
            "--spec",
            "True",
        ])
        .expect("should parse");
        if let Commands::Verify(args) = cli.command {
            // Default contract: the proof loop runs unless --no-prove is given.
            assert!(!args.no_prove);
        } else {
            panic!("expected Verify");
        }
    }

    #[test]
    fn verify_no_prove_flag_set() {
        let cli = Cli::try_parse_from([
            "scribe",
            "verify",
            "--halva-output",
            "out.lean",
            "--spec",
            "True",
            "--no-prove",
        ])
        .expect("should parse");
        if let Commands::Verify(args) = cli.command {
            assert!(args.no_prove);
        } else {
            panic!("expected Verify");
        }
    }

    #[test]
    fn judge_args_parse_with_defaults() {
        let cli =
            Cli::try_parse_from(["scribe", "judge", "--gadget", "g.toml"]).expect("should parse");
        if let Commands::Judge(args) = cli.command {
            assert_eq!(args.gadget, "g.toml");
            assert_eq!(args.prove_iters, 5);
            assert_eq!(args.refute_iters, 4);
            assert_eq!(args.samples_per_iter, 1);
            assert_eq!(args.prime, None);
        } else {
            panic!("expected Judge");
        }

        let cli = Cli::try_parse_from([
            "scribe",
            "judge",
            "--gadget",
            "g.toml",
            "--samples-per-iter",
            "3",
            "--prove-iters",
            "2",
        ])
        .expect("should parse");
        if let Commands::Judge(args) = cli.command {
            assert_eq!(args.samples_per_iter, 3);
            assert_eq!(args.prove_iters, 2);
        } else {
            panic!("expected Judge");
        }
    }

    #[test]
    fn refute_args_parse_with_defaults() {
        let cli =
            Cli::try_parse_from(["scribe", "refute", "--gadget", "g.toml"]).expect("should parse");
        if let Commands::Refute(args) = cli.command {
            assert_eq!(args.gadget, "g.toml");
            assert_eq!(args.prime, None); // auto-picked from `p > N` hypotheses
            assert_eq!(args.max_iters, 6);
            assert!(!args.scaffold_only);
            assert_eq!(args.backend, "claude");
        } else {
            panic!("expected Refute");
        }

        let cli = Cli::try_parse_from([
            "scribe",
            "refute",
            "--gadget",
            "g.toml",
            "--prime",
            "257",
            "--scaffold-only",
        ])
        .expect("should parse");
        if let Commands::Refute(args) = cli.command {
            assert_eq!(args.prime, Some(257));
            assert!(args.scaffold_only);
        } else {
            panic!("expected Refute");
        }
    }

    #[test]
    fn verify_audit_gate_defaults_on_and_can_be_disabled() {
        let cli = Cli::try_parse_from([
            "scribe",
            "verify",
            "--halva-output",
            "out.lean",
            "--spec",
            "True",
        ])
        .expect("should parse");
        if let Commands::Verify(args) = cli.command {
            assert!(!args.no_audit_gate);
        } else {
            panic!("expected Verify");
        }

        let cli = Cli::try_parse_from([
            "scribe",
            "verify",
            "--halva-output",
            "out.lean",
            "--spec",
            "True",
            "--no-audit-gate",
        ])
        .expect("should parse");
        if let Commands::Verify(args) = cli.command {
            assert!(args.no_audit_gate);
        } else {
            panic!("expected Verify");
        }
    }

    #[test]
    fn verify_default_backend_is_claude() {
        let cli = Cli::try_parse_from([
            "scribe",
            "verify",
            "--halva-output",
            "out.lean",
            "--spec",
            "True",
        ])
        .expect("should parse");
        if let Commands::Verify(args) = cli.command {
            assert_eq!(args.backend, "claude");
        } else {
            panic!("expected Verify");
        }
    }

    #[test]
    fn demo_no_flags_parses() {
        let cli = Cli::try_parse_from(["scribe", "demo"]).expect("should parse");
        if let Commands::Demo(args) = cli.command {
            assert!(!args.verify);
            assert!(!args.live);
        } else {
            panic!("expected Demo");
        }
    }

    #[test]
    fn demo_verify_flag_set() {
        let cli = Cli::try_parse_from(["scribe", "demo", "--verify"]).expect("should parse");
        if let Commands::Demo(args) = cli.command {
            assert!(args.verify);
            assert!(!args.live);
        } else {
            panic!("expected Demo");
        }
    }

    #[test]
    fn demo_live_flag_set() {
        let cli = Cli::try_parse_from(["scribe", "demo", "--live"]).expect("should parse");
        if let Commands::Demo(args) = cli.command {
            assert!(args.live);
            assert!(!args.verify);
        } else {
            panic!("expected Demo");
        }
    }

    #[test]
    fn demo_verify_and_live_are_mutually_exclusive() {
        let result = Cli::try_parse_from(["scribe", "demo", "--verify", "--live"]);
        assert!(
            result.is_err(),
            "clap should reject --verify and --live together"
        );
    }

    #[test]
    fn init_circuit_accepted() {
        let cli = Cli::try_parse_from([
            "scribe",
            "init",
            "--circuit",
            "crates/my-circuit",
            "--output",
            "my-extractor",
            "--name",
            "my-circuit",
            "--halva-rev",
            "abc123",
        ])
        .expect("should parse");
        if let Commands::Init(args) = cli.command {
            assert_eq!(args.circuit, "crates/my-circuit");
            assert_eq!(args.output.as_deref(), Some("my-extractor"));
            assert_eq!(args.name.as_deref(), Some("my-circuit"));
            assert_eq!(args.halva_rev.as_deref(), Some("abc123"));
        } else {
            panic!("expected Init");
        }
    }

    #[test]
    fn init_requires_circuit() {
        let result = Cli::try_parse_from(["scribe", "init"]);
        assert!(result.is_err(), "clap should require --circuit");
    }
}
