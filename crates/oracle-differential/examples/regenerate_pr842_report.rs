//! Regenerates `corpus/msm-pr842/discrimination-report.json` from a fresh
//! validation run.
//!
//! Re-run this after any PR #842 corpus change:
//!
//! ```sh
//! cargo run -p oracle-differential --example regenerate_pr842_report
//! ```

use oracle_differential::{DifferentialOracle, MsmCorpus};

fn main() {
    let corpus = MsmCorpus::load_pr842().expect("load corpus/msm-pr842/manifest.json");
    let report = scribe_core::validate(&DifferentialOracle, &corpus);
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../corpus/msm-pr842/discrimination-report.json"
    );
    let json = serde_json::to_string_pretty(&report).expect("serialize report");
    std::fs::write(path, json + "\n").expect("write report");
    println!("wrote {path}");
    println!("{report:#?}");
}
