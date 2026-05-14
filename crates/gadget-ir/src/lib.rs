use serde::{Deserialize, Serialize};

/// A gadget: witness variables + polynomial constraints over a prime field.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Gadget {
    pub name: String,
    /// Prime modulus as a decimal string (arbitrary precision).
    pub modulus: String,
    pub witnesses: Vec<WitnessVar>,
    pub constraints: Vec<Constraint>,
    /// Extra hypotheses (e.g. field-size bounds) emitted as theorem parameters.
    #[serde(default)]
    pub hypotheses: Vec<Hypothesis>,
    #[serde(default)]
    pub soundness_spec: Option<String>,
}

/// An extra hypothesis for the theorem (not derived from constraints).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Hypothesis {
    pub name: String,
    /// Valid Lean 4 type expression (may reference witness names and `p`).
    pub lean_type: String,
}

/// A named witness variable.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WitnessVar {
    pub id: usize,
    pub name: String,
}

/// A polynomial constraint: sum of terms equals zero.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Constraint {
    pub label: String,
    pub terms: Vec<Term>,
}

/// A monomial term: coefficient * product of variables.
///
/// `coeff` is a decimal string (may be negative).
/// `vars` is a list of witness IDs; their product forms the monomial.
/// Example: `{ coeff: "1", vars: [1, 1] }` represents `1 * w1 * w1 = w1^2`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Term {
    pub coeff: String,
    pub vars: Vec<usize>,
}

/// Load a gadget from a TOML string.
pub fn load_gadget(toml_str: &str) -> Result<Gadget, toml::de::Error> {
    toml::from_str(toml_str)
}

/// Load a gadget from a file path.
pub fn load_gadget_file(path: &std::path::Path) -> Result<Gadget, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)?;
    Ok(load_gadget(&content)?)
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
        assert_eq!(gadget.witnesses.len(), 9); // x + 8 bits
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
        assert_eq!(gadget.witnesses.len(), 4);
        assert_eq!(gadget.constraints.len(), 3);
    }

    #[test]
    fn load_nonzero_check() {
        let gadget = load_gadget_file(&examples_dir().join("nonzero-check/gadget.toml")).unwrap();
        assert_eq!(gadget.name, "nonzero-check");
        assert_eq!(gadget.witnesses.len(), 2);
        assert_eq!(gadget.constraints.len(), 1);
        assert_eq!(gadget.constraints[0].terms.len(), 2);
    }

    #[test]
    fn load_edwards_addition() {
        let gadget = load_gadget_file(&examples_dir().join("edwards-addition/gadget.toml")).unwrap();
        assert_eq!(gadget.name, "edwards-addition");
        assert_eq!(gadget.witnesses.len(), 6);
        assert_eq!(gadget.constraints.len(), 2);
        assert_eq!(gadget.hypotheses.len(), 2);
    }
}
