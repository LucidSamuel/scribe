//! Non-ZK example: complete an ordinary Mathlib-flavoured proof.
//!
//! Demonstrates that proof-pilot is domain-agnostic — the target here is a
//! plain arithmetic lemma, not a circuit-soundness theorem. Requires:
//! - a Lake project directory (pass as argv[1]) whose `lakefile` can build
//!   files in its root, with Mathlib available if your theorem needs it;
//! - the `claude` CLI on PATH (or edit `make_backend` below).
//!
//! ```sh
//! cargo run -p proof-pilot --example prove_sum_comm -- path/to/lake-project
//! ```

use proof_pilot::backend::make_backend;
use proof_pilot::session::{self, SessionConfig, SessionResult};

const SCAFFOLD: &str = r#"import Mathlib.Tactic.Ring

/-- An ordinary lemma with a `sorry` for the loop to fill. -/
theorem sum_sq_comm (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry
"#;

fn main() {
    let lake_dir = std::env::args()
        .nth(1)
        .expect("usage: prove_sum_comm <lake-project-dir>");
    let lean_file = format!("{lake_dir}/ProofPilotExample.lean");
    std::fs::write(&lean_file, SCAFFOLD).expect("write scaffold");

    let backend = make_backend("claude", None, None, None).expect("backend");
    let config = SessionConfig {
        lean_file: lean_file.clone(),
        lake_dir,
        max_iterations: 5,
        system_prompt: None,
        transcript: None,
        use_lsp: false,
        samples_per_iter: 1,
    };

    match session::run(&config, backend.as_ref()).0 {
        SessionResult::Proven { iterations } => {
            println!("kernel accepted after {iterations} iteration(s): {lean_file}")
        }
        SessionResult::Exhausted { iterations, .. } => {
            println!("no proof in {iterations} iteration(s)")
        }
        SessionResult::Failed(msg) => eprintln!("error: {msg}"),
    }
}
