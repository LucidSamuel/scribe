// UnmeasuredReason is a closed enum, not a string: `reason: "TODO"` must not
// compile. A free-form reason is the erosion path locked decision 2 blocks —
// every unmeasured verdict states WHICH legitimate bootstrap gap it is in.
use scribe_core::{Discrimination, Evidence, Outcome, Verdict};

fn main() {
    let _v = Verdict::new(
        Outcome::Accept(Evidence::default()),
        Discrimination::Unmeasured {
            reason: "TODO".into(),
        },
    );
}
