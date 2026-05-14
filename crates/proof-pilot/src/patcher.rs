/// Apply a text patch (from LLM output) to a Lean source file.
///
/// Extracts the first Lean/text code block from the LLM response and
/// replaces everything after `by` on the last `:= by` line through EOF.
pub fn apply_patch(source: &str, llm_response: &str) -> Result<String, PatchError> {
    let proof_body = extract_code_block(llm_response).ok_or(PatchError::NoCodeBlock)?;

    // Reject forbidden tactics in the patch
    for kw in &["sorry", "axiom", "native_decide"] {
        if proof_body.contains(kw) {
            return Err(PatchError::ForbiddenTactic);
        }
    }

    // Find the first `:= by` marker (the theorem's, not any inner `have ... := by`)
    let marker = ":= by";
    let marker_pos = source.find(marker).ok_or(PatchError::NoMarker)?;
    let splice_pos = marker_pos + marker.len();

    // Everything before and including `:= by` is the theorem statement
    let header = &source[..splice_pos];

    // Strip leading `by` from the proof body if the LLM included it
    let proof_body = proof_body
        .strip_prefix("by\n")
        .or_else(|| proof_body.strip_prefix("by "))
        .unwrap_or(&proof_body);

    // Reconstruct: header + newline + indented proof body
    let mut result = String::with_capacity(header.len() + proof_body.len() + 2);
    result.push_str(header);
    result.push('\n');
    result.push_str(proof_body);
    if !result.ends_with('\n') {
        result.push('\n');
    }

    // Verify the theorem statement wasn't altered
    if !result.starts_with(header) {
        return Err(PatchError::ModifiesStatement);
    }

    Ok(result)
}

/// Extract the first code block (```lean or ```) from LLM output.
fn extract_code_block(text: &str) -> Option<String> {
    let fence_start = text.find("```")?;
    let after_fence = &text[fence_start + 3..];

    // Skip the language tag line
    let content_start = after_fence.find('\n')? + 1;
    let content = &after_fence[content_start..];

    // Find closing fence
    let fence_end = content.find("```")?;
    let block = content[..fence_end].trim_end();

    if block.is_empty() {
        None
    } else {
        Some(block.to_string())
    }
}

#[derive(Debug)]
pub enum PatchError {
    /// Could not find a code block in the LLM response.
    NoCodeBlock,
    /// The patch would modify the theorem statement (forbidden).
    ModifiesStatement,
    /// The patch introduces sorry, axiom, or native_decide.
    ForbiddenTactic,
    /// Could not find `:= by` marker in source.
    NoMarker,
}

impl std::fmt::Display for PatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatchError::NoCodeBlock => write!(f, "no code block found in LLM response"),
            PatchError::ModifiesStatement => write!(f, "patch modifies theorem statement"),
            PatchError::ForbiddenTactic => write!(f, "patch uses sorry, axiom, or native_decide"),
            PatchError::NoMarker => write!(f, "no ':= by' marker found in source file"),
        }
    }
}

impl std::error::Error for PatchError {}

#[cfg(test)]
mod tests {
    use super::*;

    const SOURCE: &str = r#"import Mathlib.Data.ZMod.Basic

theorem foo_sound
    (x : ZMod p)
    (h : x * x = 0) :
    True := by
  sorry
"#;

    #[test]
    fn applies_valid_patch() {
        let llm = "Here's the proof:\n```lean\n  trivial\n```\n";
        let result = apply_patch(SOURCE, llm).unwrap();
        assert!(result.contains(":= by\n  trivial"));
        assert!(!result.contains("sorry"));
    }

    #[test]
    fn rejects_sorry_in_patch() {
        let llm = "```lean\n  sorry\n```";
        let err = apply_patch(SOURCE, llm).unwrap_err();
        assert!(matches!(err, PatchError::ForbiddenTactic));
    }

    #[test]
    fn rejects_no_code_block() {
        let llm = "I think you should try ring_nf";
        let err = apply_patch(SOURCE, llm).unwrap_err();
        assert!(matches!(err, PatchError::NoCodeBlock));
    }

    #[test]
    fn extracts_lean_fenced_block() {
        let text = "text\n```lean\n  exact foo\n  ring\n```\nmore";
        let block = extract_code_block(text).unwrap();
        assert_eq!(block, "  exact foo\n  ring");
    }

    #[test]
    fn extracts_plain_fenced_block() {
        let text = "```\nsimp [h]\n```";
        let block = extract_code_block(text).unwrap();
        assert_eq!(block, "simp [h]");
    }
}
