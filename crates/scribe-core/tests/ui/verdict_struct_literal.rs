// A Verdict's fields are private: no struct-literal construction that could
// invent a measurement status out of thin air.
use scribe_core::{Discrimination, Evidence, Outcome, UnmeasuredReason, Verdict};

fn main() {
    let _v = Verdict {
        outcome: Outcome::Accept(Evidence::default()),
        discrimination: Discrimination::Unmeasured {
            reason: UnmeasuredReason::ValidationSkipped,
        },
    };
}
