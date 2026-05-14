/// Apply a text patch (from LLM output) to a Lean source file.
///
/// Extracts the first Lean/text code block from the LLM response.
/// Import lines at the top of the block are merged into the file header.
/// The rest replaces everything after `:= by`.
pub fn apply_patch(source: &str, llm_response: &str) -> Result<String, PatchError> {
    let code_block = extract_code_block(llm_response).ok_or(PatchError::NoCodeBlock)?;

    // Split code block into import lines and proof body
    let (new_imports, proof_body) = split_imports(&code_block);

    // Reject forbidden tactics in the proof body
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

    // Merge new imports into the header
    let header = if new_imports.is_empty() {
        header.to_string()
    } else {
        merge_imports(header, &new_imports)
    };

    // Reconstruct: header + newline + proof body
    let mut result = String::with_capacity(header.len() + proof_body.len() + 2);
    result.push_str(&header);
    result.push('\n');
    result.push_str(proof_body);
    if !result.ends_with('\n') {
        result.push('\n');
    }

    Ok(result)
}

/// Split a code block into leading import lines and the remaining proof body.
fn split_imports(block: &str) -> (Vec<String>, String) {
    let mut imports = Vec::new();
    let mut body_start = 0;

    for line in block.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("import ") || trimmed.starts_with("open ") {
            imports.push(trimmed.to_string());
            body_start += line.len() + 1; // +1 for newline
        } else if trimmed.is_empty() && !imports.is_empty() {
            body_start += line.len() + 1;
        } else {
            break;
        }
    }

    let body = if body_start < block.len() {
        &block[body_start..]
    } else {
        ""
    };

    (imports, body.to_string())
}

/// Merge new import lines into the file header, deduplicating.
fn merge_imports(header: &str, new_imports: &[String]) -> String {
    // Find where imports end (before the first non-import, non-blank line)
    let mut insert_pos = 0;
    for line in header.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("import ") || trimmed.starts_with("open ") || trimmed.is_empty() {
            insert_pos += line.len() + 1;
        } else {
            break;
        }
    }

    let existing_header = &header[..insert_pos];
    let rest = &header[insert_pos..];

    // Collect existing imports for dedup
    let existing: std::collections::HashSet<&str> = existing_header
        .lines()
        .map(|l| l.trim())
        .filter(|l| l.starts_with("import "))
        .collect();

    // Add only new imports
    let mut result = existing_header.to_string();
    for imp in new_imports {
        if !existing.contains(imp.as_str()) {
            result.push_str(imp);
            result.push('\n');
        }
    }

    result.push_str(rest);
    result
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
    fn applies_patch_with_new_imports() {
        let llm = "```lean\nimport Mathlib.Tactic.Ring\n\n  ring_nf\n  trivial\n```";
        let result = apply_patch(SOURCE, llm).unwrap();
        assert!(result.contains("import Mathlib.Tactic.Ring"));
        assert!(result.contains("import Mathlib.Data.ZMod.Basic"));
        assert!(result.contains(":= by\n  ring_nf\n  trivial"));
    }

    #[test]
    fn deduplicates_existing_imports() {
        let llm = "```lean\nimport Mathlib.Data.ZMod.Basic\n\n  trivial\n```";
        let result = apply_patch(SOURCE, llm).unwrap();
        // Should not duplicate the existing import
        assert_eq!(result.matches("import Mathlib.Data.ZMod.Basic").count(), 1);
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
