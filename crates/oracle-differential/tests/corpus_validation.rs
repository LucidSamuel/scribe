//! The Phase C acceptance surface: the `corpus/msm` corpus run through the
//! same `validate()` machinery Phase B uses, its committed
//! `DiscriminationReport`, and a `Verdict` that carries the measurement.
//!
//! The headline assertion is an *escape*: the mutant planted in the wide-window
//! path (`bucket_lookup` selecting `c >= 11`, entered only for `n >= 22027`)
//! is wrongly accepted, because the input distribution mirrors the MSM sizes
//! ragu's fuzz fleet actually reaches (max observed: 5507). Coverage
//! identified the blind spot, the mutant proves it exploitable, and the
//! committed report quantifies it — see `docs/v2.1/equivalence-notes.md`.

use oracle_differential::{
    msm_reference, Boundary, DifferentialOracle, EquivalenceClaim, EquivalenceSubject, MsmCorpus,
    MsmInputs,
};
use scribe_core::{
    validate, Claim, Corpus, Discrimination, DiscriminationReport, InstanceId, Oracle, Outcome,
    Verdict,
};

fn load() -> MsmCorpus {
    MsmCorpus::load_default().expect("corpus/msm/manifest.json loads")
}

/// One validation run shared by the assertions below (the corpus is
/// deterministic, but validation costs seconds in debug builds).
fn fresh_report() -> DiscriminationReport {
    validate(&DifferentialOracle, &load())
}

#[test]
fn corpus_shape_and_claim_metadata() {
    let corpus = load();
    assert_eq!(corpus.version(), "msm-corpus-v1");
    assert_eq!(corpus.positives().len(), 1);
    assert_eq!(corpus.negatives().len(), 3);
    let claim = &corpus.positives()[0].claim;
    assert_eq!(claim.kind(), "implementation-equivalence");
    assert!(claim.describe().contains("MSM"));
}

#[test]
fn validate_catches_reached_mutants_and_reports_the_unreached_escape() {
    let report = fresh_report();
    assert_eq!(report.corpus_version, "msm-corpus-v1");
    assert_eq!(report.positives_total, 1);
    assert_eq!(report.positives_accepted, 1);
    assert_eq!(report.negatives_total, 3);
    // The two mutants on fleet-reached paths are caught...
    assert_eq!(report.negatives_caught, 2);
    // ...and the wide-window mutant escapes: the fleet-shaped input
    // distribution never enters its path. This is the Phase C finding.
    assert_eq!(
        report.escaped,
        vec![InstanceId::from("msm-mutant-wide-window-skip-double")]
    );

    // The committed artifact must match what validation actually produces
    // (regenerate via `cargo run -p oracle-differential --example
    // regenerate_report` after corpus changes).
    let committed = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../corpus/msm/discrimination-report.json"
    );
    let committed: DiscriminationReport = serde_json::from_str(
        &std::fs::read_to_string(committed).expect("committed discrimination report exists"),
    )
    .expect("committed report parses");
    assert_eq!(report, committed);

    // A verdict issued by this oracle carries the escape as loudly as the
    // outcome (locked decision 2): even an ACCEPT renders the alarm.
    let corpus = load();
    let positive = &corpus.positives()[0];
    let outcome = DifferentialOracle.adjudicate(&positive.claim, &positive.subject);
    assert!(matches!(outcome, Outcome::Accept(_)));
    let verdict = Verdict::new(outcome, Discrimination::Measured(report));
    let rendered = verdict.to_string();
    assert!(rendered.starts_with("ACCEPT ("));
    assert!(rendered.contains("2/3 negatives caught"));
    assert!(rendered.contains("ESCAPED NEGATIVES: [msm-mutant-wide-window-skip-double]"));
}

#[test]
fn panic_is_undetermined_not_rejection() {
    fn panicking_candidate(
        _: &[oracle_differential::Scalar],
        _: &[oracle_differential::Affine],
    ) -> oracle_differential::Point {
        panic!("candidate crashed");
    }
    let subject = EquivalenceSubject {
        reference: |c, b| msm_reference(c, b),
        candidate: panicking_candidate,
        inputs: MsmInputs::generate(1, vec![4]),
    };
    let claim = EquivalenceClaim {
        boundary: Boundary::Msm,
    };
    // A crash is evidence of a crash, not proof of inequivalence.
    let outcome = DifferentialOracle.adjudicate(&claim, &subject);
    assert!(matches!(outcome, Outcome::Undetermined(_)));
}

#[test]
fn manifest_with_unknown_candidate_is_rejected_at_load_time() {
    let result = MsmCorpus::from_manifest_str(
        r#"{
            "version": "v0",
            "ragu_revision": "deadbeef",
            "pool_seed": 1,
            "input_sizes": [4],
            "positives": [],
            "negatives": [
                {"id": "x", "candidate": "no-such-impl", "description": ""}
            ]
        }"#,
    );
    let Err(err) = result else {
        panic!("unknown candidate must fail to load");
    };
    assert!(err.contains("no-such-impl"));
}
