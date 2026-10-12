//! Frontend for hand-written gadget TOML files.
//!
//! This is the port of scribe's original TOML path onto the `Frontend` trait,
//! and it is the v2.1 regression anchor: its snapshot tests pin the emitted
//! Lean byte-for-byte for every gadget in `examples/`.

use std::path::PathBuf;

use circuit_ir::{CircuitIR, Provenance};
use scribe_frontend::{Frontend, FrontendError};

/// Extracts a `CircuitIR` from a gadget TOML file (the pre-v2.1 format;
/// `witnesses` is accepted as an alias for `private`).
pub struct TomlFrontend;

impl Frontend for TomlFrontend {
    type Config = PathBuf;

    fn name(&self) -> &str {
        "toml"
    }

    fn version(&self) -> &str {
        env!("CARGO_PKG_VERSION")
    }

    fn extract(&self, path: &PathBuf) -> Result<CircuitIR, FrontendError> {
        let content = std::fs::read_to_string(path).map_err(|e| FrontendError::Io {
            path: path.display().to_string(),
            message: e.to_string(),
        })?;
        let mut ir = circuit_ir::from_toml_str(&content).map_err(|e| FrontendError::Parse {
            source: path.display().to_string(),
            message: e.to_string(),
        })?;
        ir.provenance = Provenance {
            frontend: self.name().to_string(),
            frontend_version: self.version().to_string(),
            source: path.display().to_string(),
            source_rev: None,
        };
        Ok(ir)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn examples_dir() -> PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("examples")
    }

    fn extract(gadget: &str) -> CircuitIR {
        TomlFrontend
            .extract(&examples_dir().join(gadget).join("gadget.toml"))
            .unwrap()
    }

    #[test]
    fn provenance_is_stamped() {
        let ir = extract("range-check");
        assert_eq!(ir.provenance.frontend, "toml");
        assert_eq!(ir.provenance.frontend_version, env!("CARGO_PKG_VERSION"));
        assert!(ir.provenance.source.ends_with("range-check/gadget.toml"));
    }

    #[test]
    fn missing_file_is_an_io_error() {
        let err = TomlFrontend
            .extract(&examples_dir().join("no-such-gadget/gadget.toml"))
            .unwrap_err();
        assert!(matches!(err, FrontendError::Io { .. }));
    }

    #[test]
    fn bad_toml_is_a_parse_error() {
        let dir = std::env::temp_dir().join("frontend-toml-test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("broken.toml");
        std::fs::write(&path, "name = ").unwrap();
        let err = TomlFrontend.extract(&path).unwrap_err();
        assert!(matches!(err, FrontendError::Parse { .. }));
    }

    // -- snapshot tests: the emitted Lean must be byte-identical to the
    // pre-v2.1 pipeline for every gadget in examples/. These snapshots were
    // generated from the last commit before the CircuitIR migration; they
    // change only when the emitter's output is deliberately changed.

    macro_rules! snapshot {
        ($test:ident, $gadget:literal) => {
            #[test]
            fn $test() {
                let ir = extract($gadget);
                assert_eq!(
                    lean_emit::emit_lean(&ir).unwrap(),
                    include_str!(concat!("../tests/snapshots/", $gadget, ".lean")),
                    "emit_lean drifted for {}",
                    $gadget
                );
                assert_eq!(
                    lean_emit::emit_lean_decomposed(&ir).unwrap(),
                    include_str!(concat!("../tests/snapshots/", $gadget, ".decomposed.lean")),
                    "emit_lean_decomposed drifted for {}",
                    $gadget
                );
            }
        };
    }

    snapshot!(snapshot_range_check, "range-check");
    snapshot!(snapshot_conditional_select, "conditional-select");
    snapshot!(snapshot_edwards_addition, "edwards-addition");
    snapshot!(snapshot_nonzero_check, "nonzero-check");
    snapshot!(snapshot_poseidon_sbox, "poseidon-sbox");
}
