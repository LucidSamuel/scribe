//! The product thesis, executable: a `Verdict` cannot be constructed without
//! stating how the oracle was measured (roadmap v2.1, locked decision 2).
//!
//! Each file under `tests/ui/` is an attempted escape hatch, and each one must
//! fail to compile. If one of these ever starts compiling, the thesis died —
//! do not "fix" the test; fix `Verdict`.

#[test]
fn verdict_is_unconstructible_without_discrimination() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/*.rs");
}
