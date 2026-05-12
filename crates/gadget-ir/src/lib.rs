use serde::{Deserialize, Serialize};

/// A gadget: witness variables + polynomial constraints over a prime field.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Gadget {
    pub name: String,
    /// Prime modulus as a decimal string (arbitrary precision).
    pub modulus: String,
    pub witnesses: Vec<WitnessVar>,
    pub constraints: Vec<Constraint>,
    #[serde(default)]
    pub soundness_spec: Option<String>,
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

    #[test]
    fn load_range_check_gadget() {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let path = std::path::Path::new(manifest_dir)
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("examples/range-check/gadget.toml");
        let gadget = load_gadget_file(&path).expect("failed to load gadget.toml");
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
    }
}
