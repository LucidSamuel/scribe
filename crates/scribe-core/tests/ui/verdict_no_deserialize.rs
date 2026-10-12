// Verdict serializes (journals need it) but does NOT deserialize: parsing
// JSON would be a constructor that skips measurement.
use scribe_core::Verdict;

fn main() {
    fn requires_deserialize<'de, T: serde::Deserialize<'de>>() {}
    requires_deserialize::<Verdict>();
}
