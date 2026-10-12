//! The verdict core: `Claim` / `Oracle` / `Corpus` / `Verdict`.
//!
//! Scribe is the answer to a question almost nobody asks about their own
//! tooling: **when your check says PASS, can you show that it was capable of
//! saying FAIL?** This crate is that question expressed as types.
//!
//! This crate is deliberately domain-independent (roadmap v2.1, locked
//! decision 1). It knows nothing about circuits, fields, constraints, or
//! polynomials — a claim's payload lives entirely in `Claim::Subject`, an
//! associated type supplied by each domain. It must compile with every
//! subject-type crate removed from its dependencies (it depends on none).
//!
//! The one rule that is the product thesis (locked decision 2): a [`Verdict`]
//! cannot be constructed without stating how the oracle was measured. There is
//! exactly one constructor, it requires a [`Discrimination`], and there is no
//! `Default`, no `From<Outcome>`, and no builder that defaults it. The
//! compile-fail tests under `tests/ui/` are the executable form of this rule —
//! if you are new to this codebase, read them first.

use serde::{Deserialize, Serialize};

/// A falsifiable statement about some subject.
///
/// `Subject` is an associated type, not a shared enum: a circuit claim's
/// subject is a circuit IR, an equivalence claim's subject is a
/// (reference, candidate, seeds) triple. Core never sees inside it.
pub trait Claim {
    type Subject;
    /// Stable machine-readable claim kind, e.g. `"circuit-soundness"`.
    fn kind(&self) -> &'static str;
    /// Human-readable statement of the claim.
    fn describe(&self) -> String;
}

/// An acceptance procedure for one kind of claim.
///
/// An oracle adjudicates; it does not implement other people's acceptance
/// procedures (locked decision 4). Scribe hosts and grades oracles — the
/// grading is [`validate`].
pub trait Oracle<C: Claim> {
    fn adjudicate(&self, claim: &C, subject: &C::Subject) -> Outcome;
}

/// The evidence that backs every verdict an oracle issues.
///
/// A corpus is not test fixtures: it is first-class, versioned, and grows
/// monotonically — every confirmed real-world bug becomes an entry (locked
/// decision 5). It carries `positives()` too, because an oracle that rejects
/// everything has perfect negative discrimination and is useless.
pub trait Corpus<C: Claim> {
    /// Instances the oracle MUST reject.
    fn negatives(&self) -> Vec<Instance<C>>;
    /// Instances the oracle MUST accept.
    fn positives(&self) -> Vec<Instance<C>>;
    fn version(&self) -> &str;
}

/// One corpus entry: a claim, its subject, and a stable id.
pub struct Instance<C: Claim> {
    pub id: InstanceId,
    pub claim: C,
    pub subject: C::Subject,
}

/// Stable identifier of a corpus instance.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InstanceId(pub String);

impl std::fmt::Display for InstanceId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<String> for InstanceId {
    fn from(s: String) -> Self {
        InstanceId(s)
    }
}

impl From<&str> for InstanceId {
    fn from(s: &str) -> Self {
        InstanceId(s.to_string())
    }
}

/// What an oracle says about one claim.
///
/// Three-valued on purpose: budget exhaustion is not rejection, and
/// conflating them is how a tool starts lying.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Outcome {
    Accept(Evidence),
    Reject(Diagnostics),
    Undetermined(Reason),
}

impl Outcome {
    /// Short uppercase tag for rendering (`ACCEPT` / `REJECT` / `UNDETERMINED`).
    pub fn tag(&self) -> &'static str {
        match self {
            Outcome::Accept(_) => "ACCEPT",
            Outcome::Reject(_) => "REJECT",
            Outcome::Undetermined(_) => "UNDETERMINED",
        }
    }
}

/// What backs an acceptance (e.g. a kernel-checked proof, an axiom audit).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Evidence {
    pub summary: String,
    #[serde(default)]
    pub details: Vec<String>,
}

/// Why a claim was rejected, in terms the claimant can act on.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostics {
    pub summary: String,
    #[serde(default)]
    pub details: Vec<String>,
}

/// Why no determination was reached (budget, timeout, missing input, …).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Reason {
    pub summary: String,
}

/// How an oracle performed against a corpus of known-good and known-bad
/// instances. Produced by [`validate`]; consumed by [`Verdict::new`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiscriminationReport {
    pub corpus_version: String,
    pub negatives_caught: usize,
    pub negatives_total: usize,
    /// Negatives the oracle wrongly ACCEPTED. An escape is the loudest signal
    /// the system can produce: the oracle accepted something known to be
    /// wrong, so every verdict it has ever issued is suspect.
    pub escaped: Vec<InstanceId>,
    pub positives_accepted: usize,
    pub positives_total: usize,
}

impl DiscriminationReport {
    pub fn has_escapes(&self) -> bool {
        !self.escaped.is_empty()
    }
}

/// Why an oracle is unmeasured. A closed enum on purpose: a free-form string
/// would readmit `Unmeasured { reason: "TODO" }`, which is precisely the
/// erosion path locked decision 2 exists to block. If a new legitimate way to
/// be unmeasured appears, add a variant here — do not widen this to a string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnmeasuredReason {
    /// No corpus exists for this claim kind at all.
    NoCorpusDefined,
    /// A corpus exists but contains no instances.
    CorpusEmpty,
    /// A corpus with instances exists but validation was not run.
    ValidationSkipped,
}

impl std::fmt::Display for UnmeasuredReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            UnmeasuredReason::NoCorpusDefined => "no corpus defined for this claim kind",
            UnmeasuredReason::CorpusEmpty => "the corpus for this claim kind is empty",
            UnmeasuredReason::ValidationSkipped => "validation against the corpus was skipped",
        })
    }
}

/// The measurement status attached to every verdict.
///
/// `Unmeasured` is a legal state — it must be, or nothing could bootstrap —
/// but renderers must show it as prominently as the outcome itself.
/// `ACCEPT (oracle unmeasured)` is the honest rendering, and it should look
/// uncomfortable.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Discrimination {
    Measured(DiscriminationReport),
    Unmeasured { reason: UnmeasuredReason },
}

impl std::fmt::Display for Discrimination {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Discrimination::Measured(r) => {
                write!(
                    f,
                    "corpus {}: {}/{} negatives caught, {}/{} positives accepted",
                    r.corpus_version,
                    r.negatives_caught,
                    r.negatives_total,
                    r.positives_accepted,
                    r.positives_total,
                )?;
                if r.has_escapes() {
                    let ids: Vec<String> = r.escaped.iter().map(|i| i.0.clone()).collect();
                    write!(
                        f,
                        "; ESCAPED NEGATIVES: [{}] — the oracle accepted known-bad \
                         instances; every verdict it has issued is suspect",
                        ids.join(", ")
                    )?;
                }
                Ok(())
            }
            Discrimination::Unmeasured { reason } => {
                write!(f, "oracle unmeasured: {}", reason)
            }
        }
    }
}

/// An outcome that carries its own credibility.
///
/// Fields are private and there is exactly ONE constructor, which requires a
/// [`Discrimination`]. No `Default`, no `From<Outcome>`, no builder. If a
/// later phase asks for a convenience escape hatch, that request is the bug
/// (locked decision 2).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Verdict {
    outcome: Outcome,
    discrimination: Discrimination,
}

impl Verdict {
    /// The ONLY constructor. There is no path to a `Verdict` that skips
    /// discrimination — see locked decision 2.
    pub fn new(outcome: Outcome, discrimination: Discrimination) -> Self {
        Verdict {
            outcome,
            discrimination,
        }
    }

    pub fn outcome(&self) -> &Outcome {
        &self.outcome
    }

    pub fn discrimination(&self) -> &Discrimination {
        &self.discrimination
    }
}

impl std::fmt::Display for Verdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ({})", self.outcome.tag(), self.discrimination)
    }
}

/// Run an oracle over every corpus instance and measure both directions.
///
/// A caught negative is a `Reject`; anything else on a negative is a miss,
/// and an `Accept` on a negative is an **escape**, reported by id. A counted
/// positive is an `Accept`. `Undetermined` never counts as caught or
/// accepted — an oracle that shrugs at the corpus has not discriminated.
pub fn validate<C, O, K>(oracle: &O, corpus: &K) -> DiscriminationReport
where
    C: Claim,
    O: Oracle<C> + ?Sized,
    K: Corpus<C> + ?Sized,
{
    let negatives = corpus.negatives();
    let positives = corpus.positives();
    let negatives_total = negatives.len();
    let positives_total = positives.len();

    let mut negatives_caught = 0;
    let mut escaped = Vec::new();
    for instance in &negatives {
        match oracle.adjudicate(&instance.claim, &instance.subject) {
            Outcome::Reject(_) => negatives_caught += 1,
            Outcome::Accept(_) => escaped.push(instance.id.clone()),
            Outcome::Undetermined(_) => {}
        }
    }

    let mut positives_accepted = 0;
    for instance in &positives {
        if let Outcome::Accept(_) = oracle.adjudicate(&instance.claim, &instance.subject) {
            positives_accepted += 1;
        }
    }

    DiscriminationReport {
        corpus_version: corpus.version().to_string(),
        negatives_caught,
        negatives_total,
        escaped,
        positives_accepted,
        positives_total,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // A toy domain: claims about integer parity. Deliberately nothing to do
    // with circuits — core must stay domain-blind.
    struct ParityClaim;

    impl Claim for ParityClaim {
        type Subject = i64;
        fn kind(&self) -> &'static str {
            "parity-even"
        }
        fn describe(&self) -> String {
            "the subject is even".to_string()
        }
    }

    /// Correct oracle: accepts evens, rejects odds.
    struct EvenOracle;
    impl Oracle<ParityClaim> for EvenOracle {
        fn adjudicate(&self, _claim: &ParityClaim, subject: &i64) -> Outcome {
            if subject % 2 == 0 {
                Outcome::Accept(Evidence {
                    summary: format!("{subject} is even"),
                    details: vec![],
                })
            } else {
                Outcome::Reject(Diagnostics {
                    summary: format!("{subject} is odd"),
                    details: vec![],
                })
            }
        }
    }

    /// Broken oracle: accepts everything. Its escapes must surface.
    struct YesOracle;
    impl Oracle<ParityClaim> for YesOracle {
        fn adjudicate(&self, _claim: &ParityClaim, _subject: &i64) -> Outcome {
            Outcome::Accept(Evidence::default())
        }
    }

    /// Shrugging oracle: undetermined on everything.
    struct ShrugOracle;
    impl Oracle<ParityClaim> for ShrugOracle {
        fn adjudicate(&self, _claim: &ParityClaim, _subject: &i64) -> Outcome {
            Outcome::Undetermined(Reason {
                summary: "budget exhausted".into(),
            })
        }
    }

    struct ParityCorpus;
    impl Corpus<ParityClaim> for ParityCorpus {
        fn negatives(&self) -> Vec<Instance<ParityClaim>> {
            [1, 3, 5]
                .into_iter()
                .map(|n| Instance {
                    id: format!("odd-{n}").into(),
                    claim: ParityClaim,
                    subject: n,
                })
                .collect()
        }
        fn positives(&self) -> Vec<Instance<ParityClaim>> {
            [2, 4]
                .into_iter()
                .map(|n| Instance {
                    id: format!("even-{n}").into(),
                    claim: ParityClaim,
                    subject: n,
                })
                .collect()
        }
        fn version(&self) -> &str {
            "parity-corpus-v1"
        }
    }

    #[test]
    fn validate_measures_both_directions() {
        let report = validate(&EvenOracle, &ParityCorpus);
        assert_eq!(report.corpus_version, "parity-corpus-v1");
        assert_eq!(report.negatives_caught, 3);
        assert_eq!(report.negatives_total, 3);
        assert_eq!(report.positives_accepted, 2);
        assert_eq!(report.positives_total, 2);
        assert!(!report.has_escapes());
    }

    #[test]
    fn validate_reports_escapes_by_id() {
        let report = validate(&YesOracle, &ParityCorpus);
        assert_eq!(report.negatives_caught, 0);
        assert_eq!(
            report.escaped,
            vec![
                InstanceId::from("odd-1"),
                InstanceId::from("odd-3"),
                InstanceId::from("odd-5")
            ]
        );
        // Accept-everything still aces the positives — which is exactly why
        // negatives are measured at all.
        assert_eq!(report.positives_accepted, 2);
    }

    #[test]
    fn undetermined_counts_as_neither_caught_nor_escaped() {
        let report = validate(&ShrugOracle, &ParityCorpus);
        assert_eq!(report.negatives_caught, 0);
        assert!(report.escaped.is_empty());
        assert_eq!(report.positives_accepted, 0);
    }

    #[test]
    fn verdict_renders_outcome_and_measurement_together() {
        let report = validate(&EvenOracle, &ParityCorpus);
        let verdict = Verdict::new(
            Outcome::Accept(Evidence {
                summary: "4 is even".into(),
                details: vec![],
            }),
            Discrimination::Measured(report),
        );
        let rendered = verdict.to_string();
        assert!(rendered.starts_with("ACCEPT ("));
        assert!(rendered.contains("3/3 negatives caught"));
        assert!(rendered.contains("2/2 positives accepted"));
        assert!(rendered.contains("parity-corpus-v1"));
    }

    #[test]
    fn unmeasured_verdict_is_legal_but_loud() {
        let verdict = Verdict::new(
            Outcome::Accept(Evidence::default()),
            Discrimination::Unmeasured {
                reason: UnmeasuredReason::NoCorpusDefined,
            },
        );
        let rendered = verdict.to_string();
        assert!(rendered.contains("ACCEPT (oracle unmeasured"));
        assert!(rendered.contains("no corpus defined"));
    }

    #[test]
    fn every_unmeasured_reason_renders_distinctly() {
        let reasons = [
            UnmeasuredReason::NoCorpusDefined,
            UnmeasuredReason::CorpusEmpty,
            UnmeasuredReason::ValidationSkipped,
        ];
        let rendered: Vec<String> = reasons.iter().map(|r| r.to_string()).collect();
        for r in &rendered {
            assert!(!r.is_empty());
        }
        assert_ne!(rendered[0], rendered[1]);
        assert_ne!(rendered[1], rendered[2]);
        assert_ne!(rendered[0], rendered[2]);
    }

    #[test]
    fn escapes_render_louder_than_a_summary_line() {
        let report = validate(&YesOracle, &ParityCorpus);
        let verdict = Verdict::new(
            Outcome::Accept(Evidence::default()),
            Discrimination::Measured(report),
        );
        let rendered = verdict.to_string();
        assert!(rendered.contains("ESCAPED NEGATIVES: [odd-1, odd-3, odd-5]"));
        assert!(rendered.contains("every verdict it has issued is suspect"));
    }

    #[test]
    fn verdict_exposes_outcome_and_discrimination_read_only() {
        let verdict = Verdict::new(
            Outcome::Reject(Diagnostics {
                summary: "subject is odd".into(),
                details: vec![],
            }),
            Discrimination::Unmeasured {
                reason: UnmeasuredReason::ValidationSkipped,
            },
        );
        assert_eq!(verdict.outcome().tag(), "REJECT");
        assert!(matches!(
            verdict.discrimination(),
            Discrimination::Unmeasured { .. }
        ));
    }
}
