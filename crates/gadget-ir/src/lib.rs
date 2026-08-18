//! **Deprecated.** `gadget-ir` is a re-export shim over [`circuit_ir`] for one
//! release (scribe v2.1, Phase A). Use `circuit-ir` for the types and
//! `frontend-toml` for loading gadget TOML files.
//!
//! The old `Gadget` type is now [`circuit_ir::CircuitIR`]; the flat
//! `witnesses` field became `public` / `private` variable groups, and the old
//! TOML files keep loading because `witnesses` deserializes into `private`.
//!
//! The loader functions below intentionally carry no `#[deprecated]`
//! attribute: downstream crates (scribe-cli, bench) are owned by other v2.1
//! phases and build with `-D warnings`, so attribute-level deprecation would
//! break them before their phases migrate. The type aliases, which nothing
//! downstream names, are attributed.

#![allow(deprecated)]

#[deprecated(since = "0.2.0", note = "use circuit_ir::CircuitIR")]
pub type Gadget = circuit_ir::CircuitIR;

#[deprecated(since = "0.2.0", note = "use circuit_ir::Variable")]
pub type WitnessVar = circuit_ir::Variable;

#[deprecated(since = "0.2.0", note = "use circuit_ir::Constraint")]
pub type Constraint = circuit_ir::Constraint;

#[deprecated(since = "0.2.0", note = "use circuit_ir::Term")]
pub type Term = circuit_ir::Term;

#[deprecated(since = "0.2.0", note = "use circuit_ir::Hypothesis")]
pub type Hypothesis = circuit_ir::Hypothesis;

/// Load a gadget from a TOML string.
///
/// Deprecated in favor of `circuit_ir::from_toml_str` (or the `frontend-toml`
/// crate, which also stamps provenance).
pub fn load_gadget(toml_str: &str) -> Result<Gadget, toml::de::Error> {
    circuit_ir::from_toml_str(toml_str)
}

/// Load a gadget from a file path.
///
/// Deprecated in favor of `circuit_ir::load_toml_file` (or the
/// `frontend-toml` crate, which also stamps provenance).
pub fn load_gadget_file(path: &std::path::Path) -> Result<Gadget, Box<dyn std::error::Error>> {
    circuit_ir::load_toml_file(path)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn examples_dir() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("examples")
    }

    #[test]
    fn load_range_check_gadget() {
        let gadget = load_gadget_file(&examples_dir().join("range-check/gadget.toml"))
            .expect("failed to load gadget.toml");
        assert_eq!(gadget.name, "range-check-8bit");
        assert_eq!(gadget.private.len(), 9); // x + 8 bits, via the `witnesses` alias
        assert_eq!(gadget.constraints.len(), 9); // 8 bit constraints + 1 decomposition

        // check first bit constraint has 2 terms
        let bit0 = &gadget.constraints[0];
        assert_eq!(bit0.label, "bit_0");
        assert_eq!(bit0.terms.len(), 2);

        // check decomposition constraint has 9 terms
        let decomp = &gadget.constraints[8];
        assert_eq!(decomp.label, "decomposition");
        assert_eq!(decomp.terms.len(), 9);

        // check hypothesis
        assert_eq!(gadget.hypotheses.len(), 1);
        assert_eq!(gadget.hypotheses[0].name, "hp");
    }

    #[test]
    fn load_poseidon_sbox() {
        let gadget = load_gadget_file(&examples_dir().join("poseidon-sbox/gadget.toml")).unwrap();
        assert_eq!(gadget.name, "poseidon-sbox");
        assert_eq!(gadget.private.len(), 4);
        assert_eq!(gadget.constraints.len(), 3);
    }

    #[test]
    fn load_nonzero_check() {
        let gadget = load_gadget_file(&examples_dir().join("nonzero-check/gadget.toml")).unwrap();
        assert_eq!(gadget.name, "nonzero-check");
        assert_eq!(gadget.private.len(), 2);
        assert_eq!(gadget.constraints.len(), 1);
        assert_eq!(gadget.constraints[0].terms.len(), 2);
    }

    #[test]
    fn load_edwards_addition() {
        let gadget =
            load_gadget_file(&examples_dir().join("edwards-addition/gadget.toml")).unwrap();
        assert_eq!(gadget.name, "edwards-addition");
        assert_eq!(gadget.private.len(), 6);
        assert_eq!(gadget.constraints.len(), 2);
        assert_eq!(gadget.hypotheses.len(), 4);
    }
}
