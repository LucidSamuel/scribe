//! Locked decision 2 reaching the UI: every verdict line the CLI prints
//! carries its discrimination status. There is no bare ACCEPT anywhere.
//!
//! Circuit corpus measurements exist, but measure `LeanOracle`'s configured
//! prove-then-refute pipeline. They do not measure `check`'s evidence replay or
//! `judge`'s separate orchestration. A matching corpus fingerprint alone cannot
//! establish applicability: the oracle, prompts, budgets and environment also
//! matter. Those historical reports remain available through `corpus validate`;
//! these verdicts honestly say validation was skipped when a corpus is present.

use std::io::ErrorKind;
use std::path::Path;

use scribe_core::{
    Diagnostics, Discrimination, Evidence, Outcome, Reason, UnmeasuredReason, Verdict,
};

/// Measurement status for the CLI's check/judge/demo/refute paths.
/// Never promote a report from a different acceptance procedure to Measured.
pub fn current_discrimination() -> Discrimination {
    match std::env::current_dir() {
        Ok(directory) => discrimination_at(&directory),
        // An unreadable working directory is not evidence that no corpus exists.
        Err(_) => unmeasured(UnmeasuredReason::ValidationSkipped),
    }
}

fn unmeasured(reason: UnmeasuredReason) -> Discrimination {
    Discrimination::Unmeasured { reason }
}

fn discrimination_at(directory: &Path) -> Discrimination {
    // Permit invocation from a repository subdirectory without baking the
    // build machine's CARGO_MANIFEST_DIR into an installed binary. Treat an
    // incomplete/unreadable corpus or orphaned report as skipped validation,
    // never as a measured result or a claim that no corpus has been defined.
    for ancestor in directory.ancestors() {
        match std::fs::symlink_metadata(ancestor.join("corpus/circuits")) {
            Ok(_) => return unmeasured(UnmeasuredReason::ValidationSkipped),
            Err(error) if error.kind() == ErrorKind::NotFound => {}
            Err(_) => return unmeasured(UnmeasuredReason::ValidationSkipped),
        }
    }
    unmeasured(UnmeasuredReason::NoCorpusDefined)
}

/// A `VERDICT:` line for an accepting outcome (kernel-accepted proof).
pub fn accept_line(summary: &str) -> String {
    line(Outcome::Accept(Evidence {
        summary: summary.to_string(),
        details: vec![],
    }))
}

/// A `VERDICT:` line for a rejecting outcome (kernel-checked counterexample).
pub fn reject_line(summary: &str) -> String {
    line(Outcome::Reject(Diagnostics {
        summary: summary.to_string(),
        details: vec![],
    }))
}

/// A `VERDICT:` line for an undetermined outcome (budget exhausted, nothing
/// proven either way).
pub fn undetermined_line(summary: &str) -> String {
    line(Outcome::Undetermined(Reason {
        summary: summary.to_string(),
    }))
}

fn line(outcome: Outcome) -> String {
    format!(
        "VERDICT: {}",
        Verdict::new(outcome, current_discrimination())
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_verdict_line_is_a_bare_accept() {
        let rendered = accept_line("kernel-accepted proof");
        assert!(rendered.starts_with("VERDICT: ACCEPT ("));
        assert!(
            rendered.contains("oracle unmeasured:"),
            "an ACCEPT without measurement status is the failure the product exists to prevent: {rendered}"
        );
    }

    #[test]
    fn reject_and_undetermined_carry_status_too() {
        assert!(reject_line("counterexample").contains("REJECT (oracle unmeasured"));
        assert!(undetermined_line("budgets exhausted").contains("UNDETERMINED (oracle unmeasured"));
    }

    struct Fixture(std::path::PathBuf);

    impl Fixture {
        fn new() -> Self {
            static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!(
                "scribe-discrimination-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            ));
            std::fs::create_dir_all(&path).unwrap();
            Self(path)
        }

        fn corpus(&self) -> std::path::PathBuf {
            let path = self.0.join("corpus/circuits");
            std::fs::create_dir_all(&path).unwrap();
            path
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn assert_reason(path: &Path, expected: UnmeasuredReason) {
        match discrimination_at(path) {
            Discrimination::Unmeasured { reason } => assert_eq!(reason, expected),
            Discrimination::Measured(_) => {
                panic!("a foreign oracle report must not become measured")
            }
        }
    }

    #[test]
    fn absent_corpus_is_distinct_from_skipped_validation() {
        let fixture = Fixture::new();
        assert_reason(&fixture.0, UnmeasuredReason::NoCorpusDefined);
        fixture.corpus();
        assert_reason(&fixture.0, UnmeasuredReason::ValidationSkipped);
    }

    #[test]
    fn corpus_is_discovered_from_subdirectories_without_changing_process_cwd() {
        let fixture = Fixture::new();
        fixture.corpus();
        let nested = fixture.0.join("crates/consumer/src");
        std::fs::create_dir_all(&nested).unwrap();
        assert_reason(&nested, UnmeasuredReason::ValidationSkipped);
    }

    #[test]
    fn historical_report_does_not_measure_a_different_acceptance_procedure() {
        let fixture = Fixture::new();
        let corpus = fixture.corpus();
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/circuits");
        // Exercise the real report, not just a made-up JSON document. Even
        // unchanged corpus content does not bind this report to check/judge.
        for entry in std::fs::read_dir(repository).unwrap() {
            let entry = entry.unwrap();
            if entry.path().is_file() {
                std::fs::copy(entry.path(), corpus.join(entry.file_name())).unwrap();
            }
        }
        let loaded = oracle_lean::CircuitCorpus::load(&corpus).unwrap();
        let mut report =
            oracle_lean::CommittedValidation::load(&corpus.join("discrimination-report.json"))
                .unwrap();
        report.corpus_fingerprint = Some(loaded.content_fingerprint());
        report
            .save(&corpus.join("discrimination-report.json"))
            .unwrap();
        assert_reason(&fixture.0, UnmeasuredReason::ValidationSkipped);

        report.corpus_fingerprint = Some("stale".into());
        report
            .save(&corpus.join("discrimination-report.json"))
            .unwrap();
        assert_reason(&fixture.0, UnmeasuredReason::ValidationSkipped);
        std::fs::write(corpus.join("discrimination-report.json"), "invalid json").unwrap();
        assert_reason(&fixture.0, UnmeasuredReason::ValidationSkipped);
        std::fs::remove_file(corpus.join("discrimination-report.json")).unwrap();
        assert_reason(&fixture.0, UnmeasuredReason::ValidationSkipped);
    }
}
