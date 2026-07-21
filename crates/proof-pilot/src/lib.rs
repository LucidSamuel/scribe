//! # proof-pilot
//!
//! A kernel-arbitrated LLM proof-completion loop for Lean 4, with anti-cheat
//! and deterministic replay.
//!
//! Point it at a Lean file containing a theorem with a `sorry` and a backend
//! (Claude CLI, the Anthropic API, or any OpenAI-compatible endpoint). The loop
//! edits the proof body, compiles the exact target file with `lake build`,
//! feeds the errors (or structured LSP goal states) back to the model, and
//! repeats until the **Lean kernel** accepts or the budget runs out. The model
//! writes the proof; the kernel decides — "I proved it" means the kernel
//! checked it.
//!
//! ## Why trust the output
//!
//! - **The kernel is the oracle.** Success is `lake build` exiting clean on the
//!   exact target file — never the model's claim.
//! - **Anti-cheat.** The patcher structurally cannot modify the theorem
//!   statement (everything up to `:= by` comes from the file; the model only
//!   fills the body, bounded by the next top-level command), and a token-aware
//!   scan rejects `sorry` / `axiom` / `native_decide` in what would be spliced.
//! - **Deterministic replay.** Every session yields a [`journal::SessionJournal`]
//!   (optionally saved as versioned JSON via [`transcript`]) recording each
//!   iteration — and under best-of-n sampling, every candidate plus the
//!   acceptance index. [`replay`] re-applies a transcript without an LLM,
//!   refusing on toolchain/Mathlib mismatch unless overridden.
//! - **Best-of-n, soundness-free.** [`session::SessionConfig::samples_per_iter`]
//!   fires k attempts per iteration and lets the kernel filter: candidates are
//!   deduplicated, tried shortest-first, first to build wins. A wrong candidate
//!   costs a build, never a false acceptance.
//!
//! ## Quick start (library)
//!
//! ```no_run
//! use proof_pilot::backend::make_backend;
//! use proof_pilot::session::{self, SessionConfig};
//!
//! let backend = make_backend("claude", None, None, None).unwrap();
//! let config = SessionConfig {
//!     lean_file: "MyProject/Theorem.lean".into(),
//!     lake_dir: "MyProject".into(),
//!     max_iterations: 10,
//!     system_prompt: None,
//!     transcript: None,
//!     use_lsp: false,
//!     samples_per_iter: 1,
//! };
//! let (result, journal) = session::run(&config, backend.as_ref());
//! println!("{result:?} after {} iteration(s)", journal.iterations.len());
//! ```
//!
//! The `proof-pilot` binary wraps the same loop as a CLI; run
//! `proof-pilot --help`.
//!
//! ## Scope
//!
//! proof-pilot is domain-agnostic: it needs a Lake project and a theorem, not
//! any particular mathematics. It was extracted from
//! [scribe](https://github.com/LucidSamuel/scribe), where it proves soundness
//! theorems for zero-knowledge circuit gadgets against the kernel; scribe also
//! runs the loop *adversarially* (proving negations to hunt counterexamples),
//! which works unchanged because refutations answer to the same kernel.

pub mod backend;
pub mod journal;
pub mod lean_runner;
pub mod lsp_feedback;
pub mod notes;
pub mod patcher;
pub mod replay;
pub mod session;
pub mod transcript;
