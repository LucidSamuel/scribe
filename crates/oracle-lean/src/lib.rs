//! oracle-lean — the Lean kernel as an [`Oracle`] over circuit claims
//! (roadmap v2.1, Phase B: instance 1 of the verdict core).
//!
//! This crate changes the *shape* of scribe's existing acceptance procedure,
//! not its behavior: the same lean-emit scaffolds, the same proof-pilot
//! prove-then-refute loop `scribe judge` runs, the same `lake build` +
//! `#audit_axioms` gate — wrapped behind `scribe_core::Oracle` so it can be
//! graded by `validate()` against a corpus like any other oracle.
//!
//! Lean has three real states and they map onto [`Outcome`] honestly:
//!
//! - kernel-accepted proof            → `Accept`
//! - kernel-checked refutation found  → `Reject`
//! - budget exhausted / infra failure → `Undetermined`
//!
//! The third is **never** collapsed into the second: "we could not prove it"
//! is not "it is false", and conflating them is how a tool starts lying.

use std::fs;
use std::path::{Path, PathBuf};

use circuit_ir::CircuitIR;
use proof_pilot::backend::Backend;
use proof_pilot::session::{self, SessionConfig, SessionResult};
use scribe_core::{Claim, Diagnostics, Evidence, Oracle, Outcome, Reason};

pub mod corpus;

pub use corpus::{CircuitCorpus, CommittedValidation};

/// The claim kind this oracle adjudicates: "this circuit's constraint system
/// implies its `soundness_spec` for every assignment the verifier accepts."
///
/// The subject — the constraint system itself — is a [`CircuitIR`]; the claim
/// carries only identity. Scribe core never sees inside either.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CircuitClaim {
    /// Stable name (also the corpus instance's human handle).
    pub name: String,
}

impl CircuitClaim {
    pub fn new(name: impl Into<String>) -> Self {
        CircuitClaim { name: name.into() }
    }
}

impl Claim for CircuitClaim {
    type Subject = CircuitIR;

    fn kind(&self) -> &'static str {
        "circuit-soundness"
    }

    fn describe(&self) -> String {
        format!(
            "circuit '{}': every assignment satisfying the constraints satisfies the soundness spec",
            self.name
        )
    }
}

/// The Lean-kernel oracle: prove first (a kernel-accepted proof settles the
/// question), then attack (a kernel-checked counterexample at a small prime
/// refutes the generic statement), mirroring `scribe judge`'s two phases.
pub struct LeanOracle {
    /// The Lake project the scaffolds compile in.
    pub lake_dir: PathBuf,
    /// Where scaffolds are written (must be inside a directory `lake env
    /// lean` can compile; defaults to `<lake_dir>/ZkGadgets/Corpus`).
    pub scaffold_dir: PathBuf,
    /// Prover iteration budget per claim.
    pub prove_iters: u32,
    /// Refuter iteration budget per claim.
    pub refute_iters: u32,
    /// Best-of-n proof samples per iteration.
    pub samples_per_iter: u32,
    /// System prompt text for the prover (not a path).
    pub prover_prompt: Option<String>,
    /// System prompt text for the adversarial refuter (not a path).
    pub refuter_prompt: Option<String>,
    backend: Box<dyn Backend>,
}

impl LeanOracle {
    pub fn new(lake_dir: impl Into<PathBuf>, backend: Box<dyn Backend>) -> Self {
        let lake_dir = lake_dir.into();
        let scaffold_dir = lake_dir.join("ZkGadgets/Corpus");
        LeanOracle {
            lake_dir,
            scaffold_dir,
            prove_iters: 6,
            refute_iters: 6,
            samples_per_iter: 1,
            prover_prompt: None,
            refuter_prompt: None,
            backend,
        }
    }

    /// Load the standard prover/refuter prompts from `<repo>/prompts/`.
    pub fn with_prompts_dir(mut self, prompts_dir: &Path) -> Self {
        self.prover_prompt = fs::read_to_string(prompts_dir.join("lean-prover.md")).ok();
        self.refuter_prompt = fs::read_to_string(prompts_dir.join("lean-refuter.md")).ok();
        self
    }

    pub fn with_budgets(mut self, prove_iters: u32, refute_iters: u32) -> Self {
        self.prove_iters = prove_iters;
        self.refute_iters = refute_iters;
        self
    }

    /// The backend's display name (for reports).
    pub fn backend_name(&self) -> &str {
        self.backend.name()
    }

    fn scaffold_path(&self, prefix: &str, name: &str) -> PathBuf {
        let sanitized: String = name
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect();
        self.scaffold_dir.join(format!("{prefix}{sanitized}.lean"))
    }

    fn run_session(
        &self,
        lean_file: &Path,
        max_iterations: u32,
        prompt: &Option<String>,
    ) -> SessionResult {
        let config = SessionConfig {
            lean_file: lean_file.to_string_lossy().into_owned(),
            lake_dir: self.lake_dir.to_string_lossy().into_owned(),
            max_iterations,
            system_prompt: prompt.clone(),
            transcript: None,
            use_lsp: false,
            samples_per_iter: self.samples_per_iter,
        };
        session::run(&config, self.backend.as_ref()).0
    }
}

impl Oracle<CircuitClaim> for LeanOracle {
    fn adjudicate(&self, _claim: &CircuitClaim, subject: &CircuitIR) -> Outcome {
        if let Err(e) = fs::create_dir_all(&self.scaffold_dir) {
            return infra(format!(
                "cannot create {}: {e}",
                self.scaffold_dir.display()
            ));
        }

        // Scaffold filenames derive from the SUBJECT's (deliberately neutral)
        // name, never from the corpus id: lake diagnostics quote the file
        // path, the model sees those diagnostics, and an id like
        // `neg-underconstrained-range` would leak both the expected answer
        // and the bug class into the measurement.
        let file_stem = &subject.name;

        // ── Phase 1: prove. A kernel-accepted proof settles the question. ──
        let prove_scaffold = match lean_emit::emit_lean(subject) {
            Ok(s) => s,
            Err(e) => return infra(format!("cannot emit prover scaffold: {e}")),
        };
        let prove_path = self.scaffold_path("Prove", file_stem);
        if let Err(e) = fs::write(&prove_path, &prove_scaffold) {
            return infra(format!("cannot write {}: {e}", prove_path.display()));
        }
        let prove_exhausted =
            match self.run_session(&prove_path, self.prove_iters, &self.prover_prompt) {
                SessionResult::Proven { iterations } => {
                    return Outcome::Accept(Evidence {
                        summary: format!(
                            "kernel-accepted proof at {} ({} iteration(s))",
                            prove_path.display(),
                            iterations
                        ),
                        details: vec![
                            "lake build green; #audit_axioms passed (propext / Classical.choice / \
                         Quot.sound only)"
                                .to_string(),
                        ],
                    });
                }
                SessionResult::Failed(msg) => {
                    return infra(format!("prove phase failed: {msg}"));
                }
                SessionResult::Exhausted { iterations, .. } => iterations,
            };

        // ── Phase 2: refute at a concrete small prime. ─────────────────────
        let prime = lean_emit::refutation_prime(subject, 5);
        let refute_scaffold = match lean_emit::emit_refutation(subject, prime) {
            Ok(s) => s,
            // No spec — nothing to refute; the claim is undetermined, not false.
            Err(e) => {
                return Outcome::Undetermined(Reason {
                    summary: format!(
                        "no proof within {prove_exhausted} iteration(s), and no refutation \
                         target: {e}"
                    ),
                })
            }
        };
        let refute_path = self.scaffold_path("Refute", file_stem);
        if let Err(e) = fs::write(&refute_path, &refute_scaffold) {
            return infra(format!("cannot write {}: {e}", refute_path.display()));
        }
        match self.run_session(&refute_path, self.refute_iters, &self.refuter_prompt) {
            SessionResult::Proven { iterations } => Outcome::Reject(Diagnostics {
                summary: format!(
                    "kernel-checked counterexample at {} (p = {prime}, {} iteration(s))",
                    refute_path.display(),
                    iterations
                ),
                details: vec![
                    "the circuit is under-constrained, or the spec is wrong; the \
                     counterexample witness is in the proof"
                        .to_string(),
                ],
            }),
            SessionResult::Failed(msg) => infra(format!("refute phase failed: {msg}")),
            SessionResult::Exhausted { iterations, .. } => Outcome::Undetermined(Reason {
                summary: format!(
                    "neither proof ({prove_exhausted} iteration(s)) nor refutation \
                     ({iterations} iteration(s) at p = {prime}) within budget"
                ),
            }),
        }
    }
}

fn infra(summary: String) -> Outcome {
    Outcome::Undetermined(Reason { summary })
}

#[cfg(test)]
mod tests;
