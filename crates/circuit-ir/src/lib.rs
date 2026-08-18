//! Circuit IR — polynomial constraint systems over a prime field.
//!
//! `CircuitIR` is the *subject type* of a circuit claim, not the spine of
//! scribe (roadmap v2.1, locked decision 1). Its vocabulary is exactly: field,
//! public variables, private variables, definitions, constraints, provenance,
//! spec (locked decision 7). If an adapter cannot express something in it,
//! narrow the adapter — do not widen the IR.

use serde::{Deserialize, Serialize};

/// The IR version this crate reads and writes. Serialized as `ir_version`
/// and described by `schema/circuit-ir-v1.json`.
pub const IR_VERSION: &str = "1";

fn default_ir_version() -> String {
    IR_VERSION.to_string()
}

/// A circuit: variables + polynomial constraints over a prime field.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CircuitIR {
    /// IR format version (see `schema/circuit-ir-v1.json`).
    #[serde(default = "default_ir_version")]
    pub ir_version: String,
    pub name: String,
    /// Prime modulus as a decimal string (arbitrary precision).
    pub modulus: String,
    /// Where this IR came from — the frontend is checked, not trusted.
    #[serde(default)]
    pub provenance: Provenance,
    /// Variables the verifier sees. A soundness statement is meaningless
    /// without this distinction.
    #[serde(default)]
    pub public: Vec<Variable>,
    /// Witness variables only the prover knows. `witnesses` is accepted as a
    /// deprecated deserialization alias so pre-v2.1 gadget TOML keeps loading.
    #[serde(default, alias = "witnesses")]
    pub private: Vec<Variable>,
    /// Named linear forms. Emitted as `let` bindings instead of being inlined
    /// into every constraint that mentions them.
    #[serde(default)]
    pub definitions: Vec<Definition>,
    pub constraints: Vec<Constraint>,
    /// Extra hypotheses (e.g. field-size bounds) emitted as theorem parameters.
    #[serde(default)]
    pub hypotheses: Vec<Hypothesis>,
    /// Raw Lean proposition (v2.1 keeps this unstructured by design).
    #[serde(default)]
    pub soundness_spec: Option<String>,
}

/// Where an IR came from: which frontend extracted it, from what source.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Provenance {
    pub frontend: String,
    pub frontend_version: String,
    pub source: String,
    #[serde(default)]
    pub source_rev: Option<String>,
}

/// A named variable. `id` is the handle constraint terms use.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Variable {
    pub id: usize,
    pub name: String,
}

/// A named linear form over variables (LINEAR only — a definition with a
/// higher-degree term is a frontend bug, not a feature request).
///
/// Definitions share the variable id namespace: `id` lets constraint terms
/// reference the definition exactly like a variable, so an unlimited-fan-in
/// wire is emitted once as a `let` binding instead of being inlined
/// everywhere it appears.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Definition {
    pub id: usize,
    pub name: String,
    pub terms: Vec<Term>,
}

/// A polynomial constraint: sum of terms equals zero.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Constraint {
    pub label: String,
    pub terms: Vec<Term>,
    /// Source location this constraint came from (powers source-cited
    /// diagnostics).
    #[serde(default)]
    pub origin: Option<SourceSpan>,
}

/// A monomial term: coefficient * product of variables.
///
/// `coeff` is a decimal string (may be negative).
/// `vars` is a list of variable (or definition) ids; their product forms the
/// monomial. Example: `{ coeff: "1", vars: [1, 1] }` represents `w1^2`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Term {
    pub coeff: String,
    pub vars: Vec<usize>,
}

/// A source location in the frontend's input.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceSpan {
    pub file: String,
    pub line: u32,
    #[serde(default)]
    pub label: Option<String>,
}

/// An extra hypothesis for the theorem (not derived from constraints).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hypothesis {
    pub name: String,
    /// Valid Lean 4 type expression (may reference variable names and `p`).
    pub lean_type: String,
}

/// Manual so `ir_version` matches the serde default — a derived Default would
/// produce an empty version string that [`CircuitIR::from_json`] itself
/// rejects.
impl Default for CircuitIR {
    fn default() -> Self {
        CircuitIR {
            ir_version: default_ir_version(),
            name: String::new(),
            modulus: String::new(),
            provenance: Provenance::default(),
            public: Vec::new(),
            private: Vec::new(),
            definitions: Vec::new(),
            constraints: Vec::new(),
            hypotheses: Vec::new(),
            soundness_spec: None,
        }
    }
}

impl CircuitIR {
    /// All variables in binder order: public first, then private.
    pub fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.public.iter().chain(self.private.iter())
    }

    /// Serialize to the versioned JSON interchange format.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize from the versioned JSON interchange format.
    ///
    /// Rejects unknown `ir_version` majors at parse time, not by convention:
    /// third-party adapters (G5) and fingerprint caching both depend on the
    /// field meaning something, and a silently-accepted future format is how
    /// an extractor stops being checked (locked decision 6).
    pub fn from_json(s: &str) -> Result<Self, FromJsonError> {
        let ir: Self = serde_json::from_str(s).map_err(FromJsonError::Json)?;
        let major = ir.ir_version.split('.').next().unwrap_or("");
        if major != IR_VERSION {
            return Err(FromJsonError::UnsupportedVersion {
                found: ir.ir_version,
                supported: IR_VERSION,
            });
        }
        Ok(ir)
    }
}

/// Why JSON could not become a `CircuitIR`.
#[derive(Debug)]
pub enum FromJsonError {
    Json(serde_json::Error),
    /// The document declares an IR major this crate does not read.
    UnsupportedVersion {
        found: String,
        supported: &'static str,
    },
}

impl std::fmt::Display for FromJsonError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FromJsonError::Json(e) => write!(f, "invalid CircuitIR JSON: {}", e),
            FromJsonError::UnsupportedVersion { found, supported } => write!(
                f,
                "unsupported ir_version {:?}: this build reads major {} \
                 (schema/circuit-ir-v{}.json)",
                found, supported, supported
            ),
        }
    }
}

impl std::error::Error for FromJsonError {}

/// Load a circuit from a TOML string (the pre-v2.1 gadget format, with
/// `witnesses` accepted as an alias for `private`).
pub fn from_toml_str(toml_str: &str) -> Result<CircuitIR, toml::de::Error> {
    toml::from_str(toml_str)
}

/// Load a circuit from a TOML file.
pub fn load_toml_file(path: &std::path::Path) -> Result<CircuitIR, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)?;
    Ok(from_toml_str(&content)?)
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

    fn schema_path() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("schema/circuit-ir-v1.json")
    }

    #[test]
    fn witnesses_alias_deserializes_into_private() {
        let ir = load_toml_file(&examples_dir().join("range-check/gadget.toml")).unwrap();
        assert_eq!(ir.name, "range-check-8bit");
        assert_eq!(ir.ir_version, IR_VERSION);
        assert!(ir.public.is_empty());
        assert_eq!(ir.private.len(), 9); // x + 8 bits
        assert_eq!(ir.constraints.len(), 9);
        assert_eq!(ir.hypotheses.len(), 1);
        assert_eq!(ir.variables().count(), 9);
    }

    #[test]
    fn explicit_public_and_private_groups_load() {
        let ir = from_toml_str(
            r#"
            name = "split"
            modulus = "17"
            [[public]]
            id = 0
            name = "out"
            [[private]]
            id = 1
            name = "w"
            [[constraints]]
            label = "c"
            terms = [{ coeff = "1", vars = [0] }, { coeff = "-1", vars = [1] }]
            "#,
        )
        .unwrap();
        assert_eq!(ir.public.len(), 1);
        assert_eq!(ir.private.len(), 1);
        let names: Vec<&str> = ir.variables().map(|v| v.name.as_str()).collect();
        assert_eq!(names, vec!["out", "w"]); // public first
    }

    #[test]
    fn json_round_trip_preserves_every_field() {
        let mut ir = load_toml_file(&examples_dir().join("range-check/gadget.toml")).unwrap();
        ir.provenance = Provenance {
            frontend: "toml".into(),
            frontend_version: "0.1.0".into(),
            source: "examples/range-check/gadget.toml".into(),
            source_rev: Some("abc123".into()),
        };
        ir.public = vec![Variable {
            id: 100,
            name: "out".into(),
        }];
        ir.definitions = vec![Definition {
            id: 101,
            name: "acc".into(),
            terms: vec![Term {
                coeff: "2".into(),
                vars: vec![1],
            }],
        }];
        ir.constraints[0].origin = Some(SourceSpan {
            file: "src/gadget.rs".into(),
            line: 42,
            label: Some("bit 0".into()),
        });

        let json = ir.to_json().unwrap();
        let back = CircuitIR::from_json(&json).unwrap();
        assert_eq!(ir, back);
    }

    fn compiled_schema() -> jsonschema::Validator {
        let schema: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(schema_path()).unwrap()).unwrap();
        assert_eq!(schema["$id"].as_str().unwrap(), "circuit-ir-v1.json");
        jsonschema::validator_for(&schema).expect("schema must compile")
    }

    /// A fully-populated IR (definitions, origins, provenance) for schema tests.
    fn populated_ir() -> CircuitIR {
        let mut ir = load_toml_file(&examples_dir().join("range-check/gadget.toml")).unwrap();
        ir.provenance = Provenance {
            frontend: "toml".into(),
            frontend_version: "0.1.0".into(),
            source: "examples/range-check/gadget.toml".into(),
            source_rev: Some("abc123".into()),
        };
        ir.public = vec![Variable {
            id: 100,
            name: "out".into(),
        }];
        ir.definitions = vec![Definition {
            id: 101,
            name: "acc".into(),
            terms: vec![Term {
                coeff: "2".into(),
                vars: vec![1],
            }],
        }];
        ir.constraints[0].origin = Some(SourceSpan {
            file: "src/gadget.rs".into(),
            line: 42,
            label: Some("bit 0".into()),
        });
        ir
    }

    #[test]
    fn serialized_instances_validate_against_the_schema() {
        let validator = compiled_schema();
        // Every example gadget, plus a fully-populated IR exercising the
        // optional structures (definitions, origins, provenance.source_rev).
        for gadget in [
            "range-check",
            "conditional-select",
            "edwards-addition",
            "nonzero-check",
            "poseidon-sbox",
        ] {
            let ir = load_toml_file(&examples_dir().join(gadget).join("gadget.toml")).unwrap();
            let value: serde_json::Value = serde_json::from_str(&ir.to_json().unwrap()).unwrap();
            let errors: Vec<String> = validator
                .iter_errors(&value)
                .map(|e| e.to_string())
                .collect();
            assert!(errors.is_empty(), "{gadget} fails schema: {errors:?}");
        }
        let value: serde_json::Value =
            serde_json::from_str(&populated_ir().to_json().unwrap()).unwrap();
        assert!(
            validator.validate(&value).is_ok(),
            "populated IR fails schema"
        );
    }

    #[test]
    fn schema_rejects_unknown_ir_version() {
        let validator = compiled_schema();
        let mut ir = populated_ir();
        ir.ir_version = "2".to_string();
        let value: serde_json::Value = serde_json::from_str(&ir.to_json().unwrap()).unwrap();
        let errors: Vec<String> = validator
            .iter_errors(&value)
            .map(|e| e.to_string())
            .collect();
        assert!(
            !errors.is_empty(),
            "schema accepted ir_version \"2\" — the const pin is gone"
        );
    }

    #[test]
    fn schema_rejects_malformed_source_span() {
        let validator = compiled_schema();
        let mut ir = populated_ir();
        // line 0 is not a source line; serde (u32) accepts it, the schema
        // (minimum: 1) must not — this is what makes validation real.
        ir.constraints[0].origin = Some(SourceSpan {
            file: "src/gadget.rs".into(),
            line: 0,
            label: None,
        });
        let value: serde_json::Value = serde_json::from_str(&ir.to_json().unwrap()).unwrap();
        assert!(
            validator.validate(&value).is_err(),
            "schema accepted a SourceSpan with line 0"
        );

        // A span missing its file entirely (raw JSON — unconstructable via serde).
        let mut raw: serde_json::Value =
            serde_json::from_str(&populated_ir().to_json().unwrap()).unwrap();
        raw["constraints"][0]["origin"] = serde_json::json!({ "line": 42 });
        assert!(
            validator.validate(&raw).is_err(),
            "schema accepted a SourceSpan without a file"
        );
    }

    #[test]
    fn from_json_rejects_unknown_major_at_parse_time() {
        let mut ir = populated_ir();
        ir.ir_version = "2".to_string();
        let json = ir.to_json().unwrap();
        let err = CircuitIR::from_json(&json).unwrap_err();
        assert!(matches!(
            err,
            FromJsonError::UnsupportedVersion { ref found, supported: "1" } if found == "2"
        ));
        let rendered = err.to_string();
        assert!(rendered.contains("unsupported ir_version"));

        // Minor bumps within the major stay readable.
        ir.ir_version = "1.1".to_string();
        assert!(CircuitIR::from_json(&ir.to_json().unwrap()).is_ok());
    }

    #[test]
    fn default_carries_the_current_ir_version() {
        let ir = CircuitIR::default();
        assert_eq!(ir.ir_version, IR_VERSION);
        // a defaulted-then-serialized IR must survive its own version gate
        assert!(CircuitIR::from_json(&ir.to_json().unwrap()).is_ok());
    }

    #[test]
    fn serializes_private_not_witnesses() {
        let ir = load_toml_file(&examples_dir().join("nonzero-check/gadget.toml")).unwrap();
        let json = ir.to_json().unwrap();
        assert!(json.contains("\"private\""));
        assert!(!json.contains("\"witnesses\""));
    }
}
