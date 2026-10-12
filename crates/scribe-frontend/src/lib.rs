//! The `Frontend` trait: how a circuit ecosystem's circuits become
//! [`circuit_ir::CircuitIR`] subjects.
//!
//! A new circuit ecosystem is a new `Frontend` implementation; it requires no
//! changes to scribe core (roadmap v2.1, G5). Kept deliberately small.

use circuit_ir::CircuitIR;

/// An extractor from one circuit ecosystem into `CircuitIR`.
///
/// Frontends are checked, not trusted: an implementation that can compare its
/// extraction against the host framework's own metrics must do so and fail
/// hard on disagreement (locked decision 6) — that is what
/// [`FrontendError::SelfValidation`] is for.
pub trait Frontend {
    type Config;
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn extract(&self, cfg: &Self::Config) -> Result<CircuitIR, FrontendError>;
}

/// Why an extraction failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FrontendError {
    /// The source could not be read.
    Io { path: String, message: String },
    /// The source was read but could not be understood.
    Parse { source: String, message: String },
    /// The extraction disagrees with the host framework's own accounting
    /// (gate counts, constraint counts, …). The extractor is checked, not
    /// trusted — this is a hard failure, never a warning.
    SelfValidation { message: String },
}

impl std::fmt::Display for FrontendError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FrontendError::Io { path, message } => {
                write!(f, "failed to read {}: {}", path, message)
            }
            FrontendError::Parse { source, message } => {
                write!(f, "failed to parse {}: {}", source, message)
            }
            FrontendError::SelfValidation { message } => {
                write!(
                    f,
                    "extractor disagrees with the host framework: {} \
                     (the extractor is checked, not trusted — refusing to emit IR)",
                    message
                )
            }
        }
    }
}

impl std::error::Error for FrontendError {}

#[cfg(test)]
mod tests {
    use super::*;

    /// A minimal in-memory frontend, proving the trait is implementable
    /// without touching the filesystem or any ecosystem.
    struct InlineFrontend;

    impl Frontend for InlineFrontend {
        type Config = String;
        fn name(&self) -> &str {
            "inline"
        }
        fn version(&self) -> &str {
            "0.0.0"
        }
        fn extract(&self, cfg: &String) -> Result<CircuitIR, FrontendError> {
            circuit_ir::from_toml_str(cfg).map_err(|e| FrontendError::Parse {
                source: "inline TOML".to_string(),
                message: e.to_string(),
            })
        }
    }

    #[test]
    fn inline_frontend_extracts() {
        let ir = InlineFrontend
            .extract(
                &r#"
                name = "t"
                modulus = "7"
                [[private]]
                id = 0
                name = "x"
                [[constraints]]
                label = "c"
                terms = [{ coeff = "1", vars = [0] }]
                "#
                .to_string(),
            )
            .unwrap();
        assert_eq!(ir.name, "t");
        assert_eq!(ir.private.len(), 1);
    }

    #[test]
    fn self_validation_failure_is_loud() {
        let err = FrontendError::SelfValidation {
            message: "extracted 4 constraints, host reports 5".into(),
        };
        let rendered = err.to_string();
        assert!(rendered.contains("disagrees with the host framework"));
        assert!(rendered.contains("refusing to emit IR"));
    }
}
