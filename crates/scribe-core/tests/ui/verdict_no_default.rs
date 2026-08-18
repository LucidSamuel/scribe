// There is no Default: a defaulted Verdict would be a verdict from an oracle
// nobody measured, silently.
use scribe_core::Verdict;

fn main() {
    let _v = Verdict::default();
}
