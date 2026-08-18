// There is no From<Outcome>: an outcome alone is not a verdict — it says
// nothing about whether the oracle could ever have said FAIL.
use scribe_core::{Evidence, Outcome, Verdict};

fn main() {
    let _v: Verdict = Outcome::Accept(Evidence::default()).into();
}
