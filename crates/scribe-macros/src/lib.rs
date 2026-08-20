//! D1 — extraction is a `cargo test`.
//!
//! ```ignore
//! use scribe_macros as scribe;
//!
//! scribe::extract!(spend_circuit, Fp, SpendCircuit);
//! scribe::extract!(spend_checked, Fp, SpendCircuit,
//!                  spec = "out0 = 0 ∨ out0 = 1");
//! ```
//!
//! Each invocation expands to a `#[test]` that runs `frontend-ragu` over the
//! circuit and writes the extracted `CircuitIR` JSON to
//! `target/scribe/<name>.json`. Extraction becomes something that happens
//! automatically when the user runs the test suite they already have — no
//! new Cargo target, no config file, no separate extractor project.
//!
//! The test *fails* if extraction fails, which includes the extractor's
//! self-validation against ragu's own synthesis counts (locked decision 6):
//! a driver/metrics disagreement breaks the user's CI, not their trust.

/// Re-exported so the macro expansion resolves through `$crate` regardless of
/// what the user's crate imports.
pub use frontend_ragu;

/// Resolve where `target/scribe/` lives: `$CARGO_TARGET_DIR` when set,
/// otherwise the nearest `target/` directory at or above the crate root
/// (covers workspace members, whose target dir is at the workspace root),
/// otherwise `<crate root>/target`.
pub fn scribe_out_dir(manifest_dir: &str) -> std::path::PathBuf {
    let target = match std::env::var_os("CARGO_TARGET_DIR") {
        Some(dir) => std::path::PathBuf::from(dir),
        None => {
            let mut probe = std::path::PathBuf::from(manifest_dir);
            loop {
                if probe.join("target").is_dir() {
                    break probe.join("target");
                }
                if !probe.pop() {
                    break std::path::Path::new(manifest_dir).join("target");
                }
            }
        }
    };
    target.join("scribe")
}

/// Expand to a `#[test]` that extracts `$circuit` (over field `$field`) into
/// `target/scribe/<name>.json`.
///
/// - `$name` — the test's name; also the IR/JSON name with `_` → `-`.
/// - `$field` — the prime field to instantiate the circuit with (e.g. `Fp`).
/// - `$circuit` — an expression yielding the circuit value.
/// - `spec = $spec` (optional) — a raw Lean soundness proposition over the
///   IR's variable names, carried in the JSON for `scribe check` / `judge`.
#[macro_export]
macro_rules! extract {
    ($name:ident, $field:ty, $circuit:expr) => {
        $crate::extract!(
            $name,
            $field,
            $circuit,
            spec_opt = ::core::option::Option::None
        );
    };
    ($name:ident, $field:ty, $circuit:expr, spec = $spec:expr) => {
        $crate::extract!(
            $name,
            $field,
            $circuit,
            spec_opt = ::core::option::Option::Some(::std::string::String::from($spec))
        );
    };
    ($name:ident, $field:ty, $circuit:expr, spec_opt = $spec:expr) => {
        #[test]
        fn $name() {
            let circuit = $circuit;
            let opts = $crate::frontend_ragu::ExtractOptions {
                name: ::core::stringify!($name).replace('_', "-"),
                soundness_spec: $spec,
                hypotheses: ::std::vec::Vec::new(),
                source: ::std::format!("{}:{} (scribe extract!)", ::core::file!(), ::core::line!()),
            };
            let ir = $crate::frontend_ragu::extract_circuit::<$field, _>(&circuit, &opts)
                .unwrap_or_else(|e| ::core::panic!("scribe extract! failed: {e}"));
            let json = ir.to_json().expect("CircuitIR serializes");
            let dir = $crate::scribe_out_dir(::core::env!("CARGO_MANIFEST_DIR"));
            ::std::fs::create_dir_all(&dir)
                .unwrap_or_else(|e| ::core::panic!("cannot create {}: {e}", dir.display()));
            let path = dir.join(::core::concat!(::core::stringify!($name), ".json"));
            ::std::fs::write(&path, ::std::format!("{json}\n"))
                .unwrap_or_else(|e| ::core::panic!("cannot write {}: {e}", path.display()));
            ::std::eprintln!("[scribe extract!] wrote {}", path.display());
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn out_dir_finds_workspace_target() {
        // This crate lives in a workspace whose target/ is two levels up; the
        // resolver must find it rather than inventing crates/scribe-macros/target.
        let dir = super::scribe_out_dir(env!("CARGO_MANIFEST_DIR"));
        assert!(dir.ends_with("scribe"));
        let target = dir.parent().unwrap();
        assert!(target.is_dir(), "{} should exist", target.display());
        assert!(!target.starts_with(concat!(env!("CARGO_MANIFEST_DIR"), "/target")));
    }
}
