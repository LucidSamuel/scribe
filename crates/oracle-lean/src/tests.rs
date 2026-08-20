use std::path::{Path, PathBuf};

use proof_pilot::backend::{Backend, BackendError};
use scribe_core::{validate, Corpus, Discrimination, Outcome, Verdict};

use super::*;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn corpus_dir() -> PathBuf {
    repo_root().join("corpus/circuits")
}

fn report_path() -> PathBuf {
    corpus_dir().join("discrimination-report.json")
}

/// A backend that always answers with an unusable non-proof. Used to exercise
/// the oracle's control flow without a model.
struct StubBackend;

impl Backend for StubBackend {
    fn complete(&self, _: &str, _: Option<&str>) -> Result<String, BackendError> {
        Ok("I cannot prove this.".to_string())
    }
    fn name(&self) -> &str {
        "stub"
    }
}

// ── Claim ───────────────────────────────────────────────────────────────────

#[test]
fn claim_kind_is_stable_and_describes_itself() {
    let claim = CircuitClaim::new("range-check-2bit");
    assert_eq!(claim.kind(), "circuit-soundness");
    assert!(claim.describe().contains("range-check-2bit"));
    assert!(claim.describe().contains("soundness spec"));
}

// ── Corpus ──────────────────────────────────────────────────────────────────

#[test]
fn corpus_loads_five_negatives_and_positives_with_stable_ids() {
    let corpus = CircuitCorpus::load(&corpus_dir()).unwrap();
    assert_eq!(corpus.version(), "circuits-corpus-v1");

    let negatives = corpus.negatives();
    assert_eq!(
        negatives.len(),
        5,
        "the five suite negatives must all be present"
    );
    let ids: Vec<&str> = negatives.iter().map(|i| i.id.0.as_str()).collect();
    assert_eq!(
        ids,
        vec![
            "neg-underconstrained-range",
            "neg-vacuous-constraint",
            "neg-is-zero-missing-constraint",
            "neg-swap-unconstrained-output",
            "neg-wrong-inverse-constraint",
        ]
    );

    let positives = corpus.positives();
    assert!(
        positives.len() >= 3,
        "corpus must carry positives too — rejecting everything is not discrimination"
    );
    assert!(positives.iter().any(|i| i.id.0 == "pos-ragu-boolean"));

    // Every instance has a spec (there is no claim without one) and the
    // ragu-extracted instance carries a real public/private split.
    for instance in negatives.iter().chain(positives.iter()) {
        assert!(instance.subject.soundness_spec.is_some(), "{}", instance.id);
    }
    let ragu = positives
        .iter()
        .find(|i| i.id.0 == "pos-ragu-boolean")
        .unwrap();
    assert_eq!(ragu.subject.public.len(), 1);
    assert_eq!(ragu.subject.provenance.frontend, "frontend-ragu");
}

#[test]
fn corpus_rejects_bad_manifests() {
    let dir = std::env::temp_dir().join(format!("scribe-corpus-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();

    // unknown kind
    std::fs::write(
        dir.join("corpus.toml"),
        "version = \"v\"\n[[instances]]\nid = \"a\"\nkind = \"maybe\"\nfile = \"a.toml\"\n",
    )
    .unwrap();
    let err = CircuitCorpus::load(&dir).unwrap_err();
    assert!(err.to_string().contains("unknown kind"), "{err}");

    // duplicate id
    std::fs::write(
        dir.join("a.toml"),
        "name = \"a\"\nmodulus = \"7\"\nsoundness_spec = \"x = 0\"\n[[witnesses]]\nid = 0\nname = \"x\"\n[[constraints]]\nlabel = \"c\"\nterms = [{ coeff = \"1\", vars = [0] }]\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("corpus.toml"),
        "version = \"v\"\n[[instances]]\nid = \"a\"\nkind = \"negative\"\nfile = \"a.toml\"\n[[instances]]\nid = \"a\"\nkind = \"positive\"\nfile = \"a.toml\"\n",
    )
    .unwrap();
    let err = CircuitCorpus::load(&dir).unwrap_err();
    assert!(err.to_string().contains("duplicate id"), "{err}");

    // spec-less instance: nothing to adjudicate
    std::fs::write(
        dir.join("nospec.toml"),
        "name = \"n\"\nmodulus = \"7\"\n[[witnesses]]\nid = 0\nname = \"x\"\n[[constraints]]\nlabel = \"c\"\nterms = [{ coeff = \"1\", vars = [0] }]\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("corpus.toml"),
        "version = \"v\"\n[[instances]]\nid = \"n\"\nkind = \"negative\"\nfile = \"nospec.toml\"\n",
    )
    .unwrap();
    let err = CircuitCorpus::load(&dir).unwrap_err();
    assert!(err.to_string().contains("soundness_spec"), "{err}");

    std::fs::remove_dir_all(&dir).ok();
}

// ── Oracle control flow (no model, no kernel) ───────────────────────────────

#[test]
fn scaffold_paths_are_sanitized_and_use_the_subject_name() {
    // Filenames derive from the subject's neutral name, not the corpus id:
    // lake diagnostics quote the path and the model sees them, so an id like
    // `neg-underconstrained-range` would leak the expected answer.
    let oracle = LeanOracle::new("lean", Box::new(StubBackend));
    let path = oracle.scaffold_path("Prove", "range-check-2bit!");
    assert!(path.ends_with("ZkGadgets/Corpus/Proverange_check_2bit_.lean"));
}

/// Infrastructure failure must surface as `Undetermined`, never as `Reject`:
/// "the harness broke" is not "the claim is false".
#[test]
fn infrastructure_failure_is_undetermined_not_reject() {
    let missing = std::env::temp_dir().join(format!("scribe-no-lake-{}", std::process::id()));
    let oracle = LeanOracle::new(&missing, Box::new(StubBackend)).with_budgets(1, 0);
    let corpus = CircuitCorpus::load(&corpus_dir()).unwrap();
    let instance = &corpus.negatives()[1]; // zero-check: smallest subject
    let outcome = oracle.adjudicate(&instance.claim, &instance.subject);
    assert!(
        matches!(outcome, Outcome::Undetermined(_)),
        "expected Undetermined, got {outcome:?}"
    );
    std::fs::remove_dir_all(&missing).ok();
}

// ── The committed validation run ────────────────────────────────────────────

/// The committed DiscriminationReport must describe the corpus as it exists
/// today, and it must show all five negatives caught with zero escapes. If
/// the corpus grows, re-run the ignored validation test below and re-commit.
#[test]
fn committed_report_is_current_and_shows_no_escapes() {
    let committed = CommittedValidation::load(&report_path()).expect(
        "corpus/circuits/discrimination-report.json missing — run the ignored \
         validate_lean_oracle_against_corpus test to generate it",
    );
    let corpus = CircuitCorpus::load(&corpus_dir()).unwrap();

    let report = &committed.report;
    assert_eq!(report.corpus_version, corpus.version());
    assert_eq!(report.negatives_total, corpus.negatives().len());
    assert_eq!(report.positives_total, corpus.positives().len());

    assert_eq!(
        report.negatives_caught, report.negatives_total,
        "a negative was not caught — the oracle failed to refute a known-bad circuit"
    );
    assert!(
        !report.has_escapes(),
        "ESCAPED NEGATIVES {:?}: the oracle accepted known-bad circuits; every verdict \
         it has issued is suspect",
        report.escaped
    );
    assert!(report.positives_accepted >= 1);

    // And a verdict built from this measurement renders it.
    let verdict = Verdict::new(
        Outcome::Accept(scribe_core::Evidence {
            summary: "example".into(),
            details: vec![],
        }),
        Discrimination::Measured(report.clone()),
    );
    assert!(verdict.to_string().contains("5/5 negatives caught"));
}

/// The real thing: run the Lean oracle (live LLM + Lean kernel) over the
/// whole corpus and commit the DiscriminationReport. Ignored by default
/// because it costs real model calls and kernel builds; run manually with
///
/// ```sh
/// cargo test -p oracle-lean --release -- --ignored --nocapture
/// ```
#[test]
#[ignore = "runs the live LLM + Lean kernel loop over the whole corpus"]
fn validate_lean_oracle_against_corpus() {
    let root = repo_root();
    let backend = proof_pilot::backend::make_backend("claude", None, None, None).unwrap();
    let oracle = LeanOracle::new(root.join("lean"), backend)
        .with_prompts_dir(&root.join("prompts"))
        .with_budgets(3, 6);
    let corpus = CircuitCorpus::load(&corpus_dir()).unwrap();

    let report = validate(&oracle, &corpus);
    println!("DiscriminationReport: {report:#?}");

    let committed = CommittedValidation {
        generated: chrono_free_today(),
        oracle: format!(
            "LeanOracle over {} (prove-then-refute)",
            oracle.backend_name()
        ),
        prove_iters: oracle.prove_iters,
        refute_iters: oracle.refute_iters,
        report: report.clone(),
    };
    committed.save(&report_path()).unwrap();
    println!("committed to {}", report_path().display());

    assert!(
        !report.has_escapes(),
        "ESCAPED NEGATIVES {:?} — report loudly, do not tune the corpus",
        report.escaped
    );
    assert_eq!(report.negatives_caught, report.negatives_total);
}

/// Today's date without pulling in chrono: seconds since epoch is enough to
/// order runs, and the human date is in the git history.
fn chrono_free_today() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs();
    format!("unix:{secs}")
}
