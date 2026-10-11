use clap::{Parser, Subcommand};

mod cache;
mod check;
mod citations;
mod corpus_ops;
mod orchestrate;
mod verdict;

/// scribe — formal verification of ZK circuit gadgets using Lean 4.
///
/// Extract circuit claims, audit specifications, and prove or refute them.
#[derive(Parser)]
#[command(name = "scribe", version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
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

    /// Fast, free static checks — no LLM, no API key, seconds not minutes.
    ///
    /// Verifies that the circuit extracts, that the IR validates against
    /// schema/circuit-ir-v1.json, that the theorem statement elaborates as
    /// Lean (typo tier — needs `lake`, never a model), and whether a
    /// kernel-checked artifact is already on file for this exact circuit +
    /// spec (fingerprint cache).
    ///
    /// Exit codes (same convention as `judge` — script against them):
    ///   0 = SOUND        (kernel-checked proof on file for this fingerprint)
    ///   1 = UNDETERMINED (static checks pass; nothing proven — run `judge`)
    ///   2 = UNSOUND      (kernel-checked counterexample on file)
    ///   3 = input / infrastructure error (any failing static check)
    ///
    /// Static checks alone never exit 0: an exit 0 from `check` always means
    /// kernel-checked evidence exists.
    Check(check_cmd::CheckArgs),

    /// Corpus tooling: measure an oracle against its corpus, and grow the
    /// corpus when a real-world bug is confirmed.
    ///
    /// `corpus validate` runs scribe-core's validate() over every instance
    /// and renders the DiscriminationReport with ESCAPES AS ALARMS — an
    /// escaped negative means the oracle accepted something known to be
    /// wrong. Exit codes: 0 = clean discrimination, 1 = incomplete (uncaught
    /// negatives / unaccepted positives, no escapes), 2 = ESCAPE, 3 = infra.
    /// `--dry-run` renders the committed report without calling a model.
    ///
    /// `corpus add` records a new known-bad (or known-good) instance —
    /// corpus entries are permanent evidence (locked decision 5).
    Corpus(corpus_cmd::CorpusArgs),
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

        /// LLM backend to use (default: claude).
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
        /// Circuit to judge: gadget TOML, or CircuitIR JSON (`.json`).
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

        /// LLM backend to use (default: claude).
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

        /// Skip the fingerprint cache and re-judge even if a kernel-checked
        /// artifact is already recorded for this exact circuit + spec.
        #[arg(long)]
        pub no_cache: bool,
    }
}

mod corpus_cmd {
    use clap::{Args, Subcommand};

    #[derive(Args)]
    pub struct CorpusArgs {
        #[command(subcommand)]
        pub action: CorpusAction,
    }

    #[derive(Subcommand)]
    pub enum CorpusAction {
        /// Run validate(oracle, corpus) and render the DiscriminationReport,
        /// escapes first, as alarms.
        Validate(ValidateArgs),
        /// Record a new instance. Corpus entries are permanent evidence.
        Add(AddArgs),
    }

    #[derive(Args)]
    pub struct ValidateArgs {
        /// Corpus directory (contains corpus.toml).
        #[arg(long, value_name = "DIR", default_value = "corpus/circuits")]
        pub corpus: String,

        /// Render the corpus and its COMMITTED report without calling a
        /// model (free tier). Exit code reflects the committed report.
        #[arg(long)]
        pub dry_run: bool,

        /// Output path for the committed validation
        /// (default: `<corpus>/discrimination-report.json`).
        #[arg(long, value_name = "FILE")]
        pub out: Option<String>,

        /// Lake project directory (default: $LAKE_DIR env var, else `lean`).
        #[arg(long, value_name = "DIR")]
        pub lake_dir: Option<String>,

        /// Prover iterations per instance (default: 3).
        #[arg(long, value_name = "N", default_value = "3")]
        pub prove_iters: u32,

        /// Refuter iterations per instance (default: 6).
        #[arg(long, value_name = "N", default_value = "6")]
        pub refute_iters: u32,

        /// LLM backend to use (default: claude).
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

    #[derive(Args)]
    pub struct AddArgs {
        /// Corpus directory (contains corpus.toml).
        #[arg(long, value_name = "DIR", default_value = "corpus/circuits")]
        pub corpus: String,

        /// IR file to add (gadget TOML or CircuitIR JSON). Copied into the
        /// corpus directory; must carry a soundness_spec.
        #[arg(long, value_name = "FILE")]
        pub file: String,

        /// Stable instance id (e.g. `neg-underconstrained-nullifier`). This
        /// is the name an escape is reported by.
        #[arg(long, value_name = "ID")]
        pub id: String,

        /// `negative` (the oracle MUST reject) or `positive` (MUST accept).
        #[arg(long, value_name = "KIND")]
        pub kind: String,

        /// Why this instance is in the corpus (e.g. the bug it reproduces).
        #[arg(long, value_name = "TEXT")]
        pub note: String,

        /// Where it came from (issue link, commit, report).
        #[arg(long, value_name = "TEXT")]
        pub origin: Option<String>,
    }
}

mod check_cmd {
    use clap::Args;

    #[derive(Args)]
    pub struct CheckArgs {
        /// Circuit to check: gadget TOML, or CircuitIR JSON (`.json`,
        /// ir_version enforced).
        #[arg(long, value_name = "FILE")]
        pub gadget: String,

        /// Lake project directory (default: $LAKE_DIR env var, else `lean`).
        #[arg(long, value_name = "DIR")]
        pub lake_dir: Option<String>,

        /// Skip the Lean elaboration probe (the only step that needs `lake`).
        #[arg(long)]
        pub no_elab: bool,

        /// Skip the fingerprint cache lookup.
        #[arg(long)]
        pub no_cache: bool,

        /// Verify a committed Lean proof file with the kernel (lake build,
        /// #audit_axioms gate required) and record it as the SOUND evidence
        /// for this circuit's fingerprint.
        #[arg(long, value_name = "LEAN_FILE")]
        pub record: Option<String>,
    }
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Demo(args) => {
            orchestrate::run_demo(args);
        }
        Commands::Refute(args) => {
            orchestrate::run_refute(args);
        }
        Commands::Judge(args) => {
            orchestrate::run_judge(args);
        }
        Commands::Check(args) => {
            check::run_check(args);
        }
        Commands::Corpus(args) => {
            corpus_ops::run_corpus(args);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── clap structural tests (no filesystem / network access) ──────────────

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
    fn check_args_parse_with_defaults() {
        let cli =
            Cli::try_parse_from(["scribe", "check", "--gadget", "g.toml"]).expect("should parse");
        if let Commands::Check(args) = cli.command {
            assert_eq!(args.gadget, "g.toml");
            assert!(!args.no_elab);
            assert!(!args.no_cache);
            assert!(args.record.is_none());
        } else {
            panic!("expected Check");
        }

        let cli = Cli::try_parse_from([
            "scribe",
            "check",
            "--gadget",
            "g.toml",
            "--no-elab",
            "--record",
            "lean/ZkGadgets/RangeCheck.lean",
        ])
        .expect("should parse");
        if let Commands::Check(args) = cli.command {
            assert!(args.no_elab);
            assert_eq!(
                args.record.as_deref(),
                Some("lean/ZkGadgets/RangeCheck.lean")
            );
        } else {
            panic!("expected Check");
        }
    }

    #[test]
    fn corpus_validate_and_add_parse() {
        let cli = Cli::try_parse_from(["scribe", "corpus", "validate", "--dry-run"])
            .expect("should parse");
        if let Commands::Corpus(args) = cli.command {
            match args.action {
                corpus_cmd::CorpusAction::Validate(v) => {
                    assert!(v.dry_run);
                    assert_eq!(v.corpus, "corpus/circuits");
                    assert_eq!(v.prove_iters, 3);
                    assert_eq!(v.refute_iters, 6);
                }
                _ => panic!("expected Validate"),
            }
        } else {
            panic!("expected Corpus");
        }

        let cli = Cli::try_parse_from([
            "scribe",
            "corpus",
            "add",
            "--file",
            "bug.toml",
            "--id",
            "neg-x",
            "--kind",
            "negative",
            "--note",
            "reproduces issue 42",
        ])
        .expect("should parse");
        if let Commands::Corpus(args) = cli.command {
            match args.action {
                corpus_cmd::CorpusAction::Add(a) => {
                    assert_eq!(a.id, "neg-x");
                    assert_eq!(a.kind, "negative");
                    assert!(a.origin.is_none());
                }
                _ => panic!("expected Add"),
            }
        } else {
            panic!("expected Corpus");
        }

        // note is mandatory: an unexplained corpus entry is not evidence
        assert!(Cli::try_parse_from([
            "scribe", "corpus", "add", "--file", "b.toml", "--id", "x", "--kind", "negative",
        ])
        .is_err());
    }

    #[test]
    fn judge_no_cache_flag_parses() {
        let cli = Cli::try_parse_from(["scribe", "judge", "--gadget", "g.toml", "--no-cache"])
            .expect("should parse");
        if let Commands::Judge(args) = cli.command {
            assert!(args.no_cache);
        } else {
            panic!("expected Judge");
        }
        let cli =
            Cli::try_parse_from(["scribe", "judge", "--gadget", "g.toml"]).expect("should parse");
        if let Commands::Judge(args) = cli.command {
            assert!(!args.no_cache, "cache is on by default");
        } else {
            panic!("expected Judge");
        }
    }
}
