//! Bridge from Halva halo2-to-Lean extraction to scribe's proof-pilot.
//!
//! Halva (github.com/NethermindEth/halo2-fv-extractor) extracts halo2 circuits
//! into Lean 4 files with a `meets_constraints` proposition. This crate takes
//! that output, appends a user-provided specification and a `sorry`-stubbed
//! soundness theorem, and feeds it to proof-pilot for LLM-driven proof completion.

use std::fmt;

/// Parsed structure of a Halva-emitted Lean file.
#[derive(Debug, Clone)]
pub struct HalvaFile {
    /// The Lean namespace (e.g. "RangeCheck").
    pub namespace: String,
    /// Full content of the file.
    pub content: String,
    /// Line index (0-based) of `end <namespace>`.
    pub end_line: usize,
    /// Whether `meets_constraints` was found.
    pub has_meets_constraints: bool,
}

#[derive(Debug)]
pub enum ParseError {
    NoNamespace,
    NoEndNamespace { namespace: String },
    NoMeetsConstraints { namespace: String },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::NoNamespace => {
                write!(f, "no `namespace` declaration found in Halva output")
            }
            ParseError::NoEndNamespace { namespace } => {
                write!(f, "no `end {namespace}` found to close the namespace")
            }
            ParseError::NoMeetsConstraints { namespace } => {
                write!(
                    f,
                    "no `meets_constraints` definition found in namespace `{namespace}`"
                )
            }
        }
    }
}

/// Parse a Halva-emitted Lean file to extract structural information.
pub fn parse_halva_output(content: &str) -> Result<HalvaFile, ParseError> {
    let lines: Vec<&str> = content.lines().collect();

    let (namespace_line, namespace) = lines
        .iter()
        .enumerate()
        .find_map(|(i, line)| namespace_decl(line).map(|name| (i, name.to_string())))
        .ok_or(ParseError::NoNamespace)?;

    let mut namespace_stack = vec![namespace.as_str()];
    let mut end_line = None;
    let mut has_meets_constraints = false;

    for (i, line) in lines.iter().enumerate().skip(namespace_line + 1) {
        if namespace_stack.len() == 1 && is_meets_constraints_decl(line) {
            has_meets_constraints = true;
        }

        if let Some(name) = namespace_decl(line) {
            namespace_stack.push(name);
            continue;
        }

        if let Some(name) = end_decl(line) {
            let closes_current = name.is_empty()
                || namespace_stack
                    .last()
                    .is_some_and(|current| *current == name);
            if closes_current {
                namespace_stack.pop();
                if namespace_stack.is_empty() {
                    end_line = Some(i);
                    break;
                }
            }
        }
    }

    let end_line = end_line.ok_or_else(|| ParseError::NoEndNamespace {
        namespace: namespace.clone(),
    })?;

    if !has_meets_constraints {
        return Err(ParseError::NoMeetsConstraints {
            namespace: namespace.clone(),
        });
    }

    Ok(HalvaFile {
        namespace,
        content: content.to_string(),
        end_line,
        has_meets_constraints,
    })
}

fn namespace_decl(line: &str) -> Option<&str> {
    declaration_name(line, "namespace")
}

fn end_decl(line: &str) -> Option<&str> {
    let trimmed = line.trim();
    if trimmed == "end" {
        return Some("");
    }
    declaration_name(line, "end")
}

fn declaration_name<'a>(line: &'a str, keyword: &str) -> Option<&'a str> {
    let rest = line.trim().strip_prefix(keyword)?;
    if !rest.starts_with(char::is_whitespace) {
        return None;
    }
    rest.split_whitespace().next()
}

fn is_meets_constraints_decl(line: &str) -> bool {
    let Some(rest) = line.trim().strip_prefix("def") else {
        return false;
    };
    rest.split_whitespace().next() == Some("meets_constraints")
}

/// Configuration for generating a soundness scaffold.
pub struct SpecConfig {
    /// The body of the Spec definition (Lean expression over `c : ValidCircuit P P_Prime`).
    /// Example: `∀ row : ℕ, c.1.Selector 0 row = 1 → ∃ k : Fin 10, (k.val : ZMod P) = c.1.Advice 0 row`
    pub spec_body: String,
    /// Optional extra imports to add at the top.
    pub extra_imports: Vec<String>,
}

/// Generate a combined Lean file: Halva output + Spec + soundness theorem with `sorry`.
pub fn scaffold_soundness(halva: &HalvaFile, config: &SpecConfig) -> String {
    let lines: Vec<&str> = halva.content.lines().collect();
    let extra_imports: Vec<String> = config
        .extra_imports
        .iter()
        .map(|import| normalize_import(import))
        .collect();
    let extra_import_refs: Vec<&str> = extra_imports.iter().map(String::as_str).collect();
    let mut out = write_prefix_with_header(&lines, halva.end_line, &extra_import_refs);

    // Append the Spec definition and soundness theorem.
    out.push_str(&format!(
        r#"
/-- Specification: what the circuit is supposed to compute semantically.
    This is user-provided and NOT generated by Halva. -/
def Spec (c: ValidCircuit P P_Prime): Prop :=
  {}

/-- Soundness: if the circuit meets all halo2 constraints (extracted by Halva),
    then it satisfies the semantic specification.
    Conditional on Halva's extraction being faithful to halo2 execution semantics. -/
theorem soundness (c: ValidCircuit P P_Prime) (h: meets_constraints c): Spec c := by
  sorry

"#,
        config.spec_body,
    ));

    write_lines(&mut out, &lines[halva.end_line..]);

    out
}

/// Generate a combined Lean file from a raw spec snippet.
///
/// Leading imports, comments, and blank lines are merged into the file header.
/// The remaining body is inserted before the selected namespace's matching `end`.
pub fn scaffold_raw(halva: &HalvaFile, snippet: &str) -> String {
    let halva_lines: Vec<&str> = halva.content.lines().collect();

    let snippet_lines: Vec<&str> = snippet.lines().collect();
    let header_end = leading_import_header_end(&snippet_lines);
    let (header, body_start) = match header_end {
        Some(end) => (&snippet_lines[..end], end),
        None => (&[][..], 0),
    };
    let mut out = write_prefix_with_header(&halva_lines, halva.end_line, header);

    out.push('\n');
    write_lines(&mut out, &snippet_lines[body_start..]);
    out.push('\n');
    write_lines(&mut out, &halva_lines[halva.end_line..]);
    out
}

fn normalize_import(import: &str) -> String {
    let trimmed = import.trim();
    if trimmed.starts_with("import ") {
        trimmed.to_string()
    } else {
        format!("import {trimmed}")
    }
}

fn leading_import_header_end(lines: &[&str]) -> Option<usize> {
    let mut last_import_end = None;
    let mut block_comment_depth = 0;

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let is_block_comment = block_comment_depth > 0 || trimmed.starts_with("/-");
        if is_block_comment {
            update_block_comment_depth(line, &mut block_comment_depth);
        } else if trimmed.is_empty() || trimmed.starts_with("--") || trimmed.starts_with("import ")
        {
            if trimmed.starts_with("import ") {
                last_import_end = Some(i + 1);
            }
        } else {
            break;
        }
    }

    last_import_end
}

fn write_prefix_with_header(lines: &[&str], end_line: usize, header: &[&str]) -> String {
    let prefix = &lines[..end_line];
    let insertion = prefix
        .iter()
        .rposition(|line| line.trim().starts_with("import "))
        .map_or_else(|| leading_comment_end(prefix), |i| i + 1);
    let existing_imports: Vec<&str> = prefix
        .iter()
        .filter_map(|line| {
            let trimmed = line.trim();
            trimmed.starts_with("import ").then_some(trimmed)
        })
        .collect();

    let mut out = String::new();
    write_lines(&mut out, &prefix[..insertion]);
    for line in header {
        let trimmed = line.trim();
        if trimmed.starts_with("import ") && existing_imports.contains(&trimmed) {
            continue;
        }
        out.push_str(line);
        out.push('\n');
    }
    write_lines(&mut out, &prefix[insertion..]);
    out
}

fn leading_comment_end(lines: &[&str]) -> usize {
    let mut block_comment_depth = 0;
    let mut end = 0;

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        let is_block_comment = block_comment_depth > 0 || trimmed.starts_with("/-");
        if is_block_comment {
            update_block_comment_depth(line, &mut block_comment_depth);
            end = i + 1;
        } else if trimmed.is_empty() || trimmed.starts_with("--") {
            end = i + 1;
        } else {
            break;
        }
    }

    end
}

fn update_block_comment_depth(line: &str, depth: &mut usize) {
    let bytes = line.as_bytes();
    let mut i = 0;
    while i + 1 < bytes.len() {
        match (bytes[i], bytes[i + 1]) {
            (b'/', b'-') => {
                *depth += 1;
                i += 2;
            }
            (b'-', b'/') if *depth > 0 => {
                *depth -= 1;
                i += 2;
            }
            _ => i += 1,
        }
    }
}

fn write_lines(out: &mut String, lines: &[&str]) {
    for line in lines {
        out.push_str(line);
        out.push('\n');
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal Halva-style output for testing.
    const SAMPLE_HALVA: &str = r#"import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

set_option linter.unusedVariables false

namespace RangeCheck

def S_T_from_P (S T P : ℕ) : Prop :=
  (2^S * T = P - 1) ∧
  (∀ s' t': ℕ, 2^s' * t' = P - 1 → s' ≤ S)
structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) where
  Advice: ℕ → ℕ → ZMod P
  Fixed: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
  Instance: ℕ → ℕ → ZMod P
variable {P: ℕ} {P_Prime: Nat.Prime P}
abbrev ValidCircuit (P: ℕ) (P_Prime: Nat.Prime P) : Type := {c: Circuit P P_Prime // c.isValid}

def gate_0 (c: ValidCircuit P P_Prime): Prop := ∀ row : ℕ,
  c.get_selector 0 row * (((((((((c.get_advice 0 row * (1 - c.get_advice 0 row)) * (0x2 - c.get_advice 0 row)) * (0x3 - c.get_advice 0 row)) * (0x4 - c.get_advice 0 row)) * (0x5 - c.get_advice 0 row)) * (0x6 - c.get_advice 0 row)) * (0x7 - c.get_advice 0 row)) * (0x8 - c.get_advice 0 row)) * (0x9 - c.get_advice 0 row)) = 0
def all_gates (c: ValidCircuit P P_Prime) : Prop := gate_0 c

def meets_constraints (c: ValidCircuit P P_Prime): Prop :=
  sufficient_rows c ∧
  all_gates c ∧
  all_copy_constraints c

end RangeCheck
"#;

    #[test]
    fn parse_finds_namespace_and_meets_constraints() {
        let halva = parse_halva_output(SAMPLE_HALVA).unwrap();
        assert_eq!(halva.namespace, "RangeCheck");
        assert!(halva.has_meets_constraints);
        // end line should point to the `end RangeCheck` line
        let lines: Vec<&str> = SAMPLE_HALVA.lines().collect();
        assert_eq!(lines[halva.end_line].trim(), "end RangeCheck");
    }

    #[test]
    fn parse_rejects_missing_namespace() {
        let bad = "def foo := 42\n";
        assert!(matches!(
            parse_halva_output(bad),
            Err(ParseError::NoNamespace)
        ));
    }

    #[test]
    fn parse_rejects_missing_meets_constraints() {
        let bad = "namespace Foo\ndef bar := 42\nend Foo\n";
        assert!(matches!(
            parse_halva_output(bad),
            Err(ParseError::NoMeetsConstraints { .. })
        ));
    }

    #[test]
    fn parse_rejects_meets_constraints_outside_selected_namespace() {
        let bad = r#"namespace Foo
def bar := True
end Foo

namespace Other
def meets_constraints := True
end Other
"#;
        assert!(matches!(
            parse_halva_output(bad),
            Err(ParseError::NoMeetsConstraints { namespace }) if namespace == "Foo"
        ));
    }

    #[test]
    fn parse_matches_outer_namespace_end() {
        let input = r#"namespace Foo
namespace Inner
def helper := True
end Inner
def meets_constraints := True
end Foo

def trailing := True
"#;
        let halva = parse_halva_output(input).unwrap();
        let lines: Vec<&str> = input.lines().collect();
        assert_eq!(lines[halva.end_line], "end Foo");
    }

    #[test]
    fn scaffold_inserts_spec_and_sorry_theorem() {
        let halva = parse_halva_output(SAMPLE_HALVA).unwrap();
        let config = SpecConfig {
            spec_body: "∀ row : ℕ, c.get_selector 0 row = 1 → \
                         ∃ k : Fin 10, (k.val : ZMod P) = c.get_advice 0 row"
                .to_string(),
            extra_imports: vec![],
        };
        let combined = scaffold_soundness(&halva, &config);

        // Should contain the spec
        assert!(combined.contains("def Spec"));
        assert!(combined.contains("Fin 10"));
        // Should contain the theorem with sorry
        assert!(combined.contains("theorem soundness"));
        assert!(combined.contains("meets_constraints c"));
        assert!(combined.contains("Spec c"));
        assert!(combined.contains("sorry"));
        // Should still close the namespace
        assert!(combined.contains("end RangeCheck"));
        // The namespace should appear exactly once at the end
        assert!(combined.ends_with("end RangeCheck\n"));
    }

    #[test]
    fn scaffold_adds_extra_imports() {
        let halva = parse_halva_output(SAMPLE_HALVA).unwrap();
        let config = SpecConfig {
            spec_body: "True".to_string(),
            extra_imports: vec!["import Mathlib.Data.Fin.Basic".to_string()],
        };
        let combined = scaffold_soundness(&halva, &config);
        assert!(combined.contains("import Mathlib.Data.Fin.Basic"));
        // Should be after existing imports
        let fin_pos = combined.find("import Mathlib.Data.Fin.Basic").unwrap();
        let zmod_pos = combined.find("import Mathlib.Data.ZMod.Basic").unwrap();
        assert!(fin_pos > zmod_pos);
    }

    #[test]
    fn scaffold_adds_import_to_file_without_existing_imports() {
        let halva =
            parse_halva_output("namespace Foo\ndef meets_constraints := True\nend Foo\n").unwrap();
        let config = SpecConfig {
            spec_body: "True".to_string(),
            extra_imports: vec!["Mathlib.Data.Fin.Basic".to_string()],
        };
        let combined = scaffold_soundness(&halva, &config);
        assert!(combined.starts_with("import Mathlib.Data.Fin.Basic\nnamespace Foo\n"));
    }

    #[test]
    fn scaffold_places_import_after_leading_block_comment() {
        let input = r#"/-
Copyright header.
-/
namespace Foo
def meets_constraints := True
end Foo
"#;
        let halva = parse_halva_output(input).unwrap();
        let config = SpecConfig {
            spec_body: "True".to_string(),
            extra_imports: vec!["Mathlib.Data.Fin.Basic".to_string()],
        };
        let combined = scaffold_soundness(&halva, &config);
        assert!(combined.starts_with(
            "/-\nCopyright header.\n-/\nimport Mathlib.Data.Fin.Basic\nnamespace Foo\n"
        ));
    }

    #[test]
    fn scaffold_preserves_content_after_namespace() {
        let input = r#"namespace Foo
def meets_constraints := True
end Foo

def trailing := True
"#;
        let halva = parse_halva_output(input).unwrap();
        let combined = scaffold_raw(&halva, "def Spec := True");
        assert!(combined.contains("end Foo\n\ndef trailing := True\n"));
    }

    #[test]
    fn scaffold_raw_inserts_verbatim_snippet() {
        let halva = parse_halva_output(SAMPLE_HALVA).unwrap();
        let snippet = r#"def MySpec (c: ValidCircuit P P_Prime): Prop := True

theorem my_thm (c: ValidCircuit P P_Prime) (h: meets_constraints c): MySpec c := by
  sorry"#;
        let combined = scaffold_raw(&halva, snippet);
        assert!(combined.contains("def MySpec"));
        assert!(combined.contains("theorem my_thm"));
        assert!(combined.ends_with("end RangeCheck\n"));
    }

    #[test]
    fn scaffold_raw_merges_snippet_imports() {
        let halva = parse_halva_output(SAMPLE_HALVA).unwrap();
        let snippet = r#"-- Extra imports for soundness proof
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

def MySpec (c: ValidCircuit P P_Prime): Prop := True

theorem soundness (c: ValidCircuit P P_Prime) (h: meets_constraints c): MySpec c := by
  sorry"#;
        let combined = scaffold_raw(&halva, snippet);
        // New imports should be merged into header
        assert!(combined.contains("import Mathlib.Algebra.Field.ZMod"));
        assert!(combined.contains("import Mathlib.Tactic.LinearCombination"));
        // Should NOT duplicate existing imports
        let count = combined.matches("import Mathlib.Data.ZMod.Basic").count();
        assert_eq!(count, 1);
        // Body should still contain the spec
        assert!(combined.contains("def MySpec"));
        assert!(combined.ends_with("end RangeCheck\n"));
        // Imports should appear before the namespace
        let import_pos = combined.find("import Mathlib.Algebra.Field.ZMod").unwrap();
        let ns_pos = combined.find("namespace RangeCheck").unwrap();
        assert!(import_pos < ns_pos);
    }

    #[test]
    fn scaffold_raw_merges_imports_separated_by_comments() {
        let halva = parse_halva_output(SAMPLE_HALVA).unwrap();
        let snippet = r#"-- first group
import Mathlib.Data.Fin.Basic

-- second group
import Mathlib.Tactic

def MySpec := True
"#;
        let combined = scaffold_raw(&halva, snippet);
        let ns_pos = combined.find("namespace RangeCheck").unwrap();
        assert!(combined.find("import Mathlib.Data.Fin.Basic").unwrap() < ns_pos);
        assert!(combined.find("import Mathlib.Tactic").unwrap() < ns_pos);
        assert!(!combined[ns_pos..].contains("\nimport "));
        assert!(combined.contains("def MySpec := True"));
    }

    #[test]
    fn scaffold_raw_moves_import_after_block_doc_comment() {
        let halva = parse_halva_output(SAMPLE_HALVA).unwrap();
        let snippet = r#"/- Imports used by the specification. -/
import Mathlib.Tactic

def MySpec := True
"#;
        let combined = scaffold_raw(&halva, snippet);
        let ns_pos = combined.find("namespace RangeCheck").unwrap();
        let doc_pos = combined.find("/- Imports used").unwrap();
        let import_pos = combined.find("import Mathlib.Tactic").unwrap();
        assert!(doc_pos < import_pos && import_pos < ns_pos);
    }
}
