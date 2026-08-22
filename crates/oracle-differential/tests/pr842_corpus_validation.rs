//! Discrimination checks for the exact size support of ragu PR #842's direct
//! MSM equivalence strategy.

use oracle_differential::{
    candidate_by_name, DifferentialOracle, EquivalenceClaim, EquivalenceSubject, MsmCorpus,
    MsmInputs,
};
use scribe_core::{validate, Corpus, DiscriminationReport, InstanceId, Oracle, Outcome};

fn load() -> MsmCorpus {
    MsmCorpus::load_pr842().expect("corpus/msm-pr842/manifest.json loads")
}

fn expected_strategy_support() -> Vec<usize> {
    let mut sizes: Vec<_> = (0..=128).collect();
    for log_size in 0..=13 {
        let boundary = 1usize << log_size;
        sizes.extend([
            boundary.saturating_sub(1),
            boundary,
            (boundary + 1).min(8192),
        ]);
    }
    sizes.sort_unstable();
    sizes.dedup();
    sizes
}

#[test]
fn manifest_pins_the_complete_pr842_size_strategy_support() {
    let corpus = load();
    assert_eq!(corpus.manifest().input_sizes, expected_strategy_support());
    assert!(!corpus.manifest().input_sizes.contains(&8104));
    assert!(corpus.manifest().input_sizes.contains(&8192));
}

#[test]
fn strategy_support_catches_8192_but_not_the_8104_transition() {
    let corpus = load();
    let report = validate(&DifferentialOracle, &corpus);

    assert_eq!(corpus.version(), "msm-pr842-corpus-v1");
    assert_eq!(report.positives_accepted, 1);
    assert_eq!(report.positives_total, 1);
    assert_eq!(report.negatives_caught, 1);
    assert_eq!(report.negatives_total, 2);
    assert_eq!(
        report.escaped,
        vec![InstanceId::from("msm-pr842-mutant-8104-add-base")]
    );

    let committed = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../corpus/msm-pr842/discrimination-report.json"
    );
    let committed = std::fs::read_to_string(committed).expect("committed report exists");
    let committed: DiscriminationReport =
        serde_json::from_str(&committed).expect("committed report parses");
    assert_eq!(report, committed);
}

#[test]
fn escaped_8104_mutant_is_rejected_when_the_missing_input_is_supplied() {
    let claim = EquivalenceClaim {
        boundary: oracle_differential::Boundary::Msm,
    };
    let subject = EquivalenceSubject {
        reference: oracle_differential::msm_reference,
        candidate: candidate_by_name("mutant-pr842-8104-add-base").unwrap(),
        inputs: MsmInputs::generate(20260822, vec![8104]),
    };

    assert!(matches!(
        DifferentialOracle.adjudicate(&claim, &subject),
        Outcome::Reject(_)
    ));
}
