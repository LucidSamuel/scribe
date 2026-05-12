/// Apply a text patch (from LLM output) to a Lean source file.
///
/// The patcher extracts Lean code blocks from the LLM response
/// and replaces the proof body in the target file.
pub fn apply_patch(_source: &str, _llm_response: &str) -> Result<String, PatchError> {
    todo!()
}

#[derive(Debug)]
pub enum PatchError {
    /// Could not find a code block in the LLM response.
    NoCodeBlock,
    /// The patch would modify the theorem statement (forbidden).
    ModifiesStatement,
    /// The patch introduces sorry, axiom, or native_decide.
    ForbiddenTactic,
}

impl std::fmt::Display for PatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatchError::NoCodeBlock => write!(f, "no code block found in LLM response"),
            PatchError::ModifiesStatement => write!(f, "patch modifies theorem statement"),
            PatchError::ForbiddenTactic => write!(f, "patch uses sorry, axiom, or native_decide"),
        }
    }
}

impl std::error::Error for PatchError {}
