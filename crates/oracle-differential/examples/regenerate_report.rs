//! Regenerates `corpus/msm/discrimination-report.json` from a fresh
//! `validate(DifferentialOracle, MsmCorpus)` run.
//!
//! The committed report is a corpus artifact (locked decision 5): it is the
//! evidence behind every verdict this oracle issues, and the integration test
//! `committed_report_matches_fresh_validation` fails if it drifts from what
//! validation actually produces. Re-run this after any corpus change:
//!
//! ```sh
//! cargo run -p oracle-differential --example regenerate_report
//! ```

use oracle_differential::{DifferentialOracle, MsmCorpus};

fn main() {
    let corpus = MsmCorpus::load_default().expect("load corpus/msm/manifest.json");
    let report = scribe_core::validate(&DifferentialOracle, &corpus);
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../corpus/msm/discrimination-report.json"
    );
    let json = serde_json::to_string_pretty(&report).expect("serialize report");
    std::fs::write(path, json + "\n").expect("write report");
    println!("wrote {path}");
    println!("{report:#?}");
}
