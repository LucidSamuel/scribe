//! Locked decision 2 reaching the UI: every verdict line the CLI prints
//! carries its discrimination status. There is no bare ACCEPT anywhere.
//!
//! No corpus is wired into the CLI yet — the circuit corpus is a Phase B
//! deliverable, the backend corpus Phase C — so today every verdict honestly
//! renders as unmeasured. That is supposed to look uncomfortable: it is the
//! difference between "the check passed" and "the check passed, and here is
//! why you should believe the check can fail".

use scribe_core::{
    Diagnostics, Discrimination, Evidence, Outcome, Reason, UnmeasuredReason, Verdict,
};

/// The CLI's current measurement status. When Phase B/C corpora land, this is
/// the single place that starts carrying a real `DiscriminationReport`.
pub fn current_discrimination() -> Discrimination {
    Discrimination::Unmeasured {
        reason: UnmeasuredReason::NoCorpusDefined,
    }
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
            rendered.contains("oracle unmeasured: no corpus defined"),
            "an ACCEPT without measurement status is the failure the product exists to prevent: {rendered}"
        );
    }

    #[test]
    fn reject_and_undetermined_carry_status_too() {
        assert!(reject_line("counterexample").contains("REJECT (oracle unmeasured"));
        assert!(undetermined_line("budgets exhausted").contains("UNDETERMINED (oracle unmeasured"));
    }
}
