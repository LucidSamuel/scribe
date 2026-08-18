//! D2 — diagnostics cite the source circuit, not generated Lean names.
//!
//! A stalled proof surfaces Lean hypothesis names like `h_c47`. An engineer
//! who has never written Lean closes the tab at that point. This module maps
//! those generated names back to the circuit constraints they encode — and,
//! when the frontend recorded `Constraint.origin` spans, to the `file:line`
//! in the user's own source.

use circuit_ir::CircuitIR;

/// One constraint's identity across all three vocabularies: the generated
/// Lean hypothesis, the IR label, and (when the frontend recorded it) the
/// source span it came from.
pub struct Citation {
    /// Generated Lean hypothesis name, e.g. `h_bit_0`.
    pub hypothesis: String,
    /// The constraint's label in the IR.
    pub label: String,
    /// Position in `circuit.constraints`.
    pub index: usize,
    /// `(file, line, span label)` from `Constraint.origin`, if recorded.
    pub origin: Option<(String, u32, Option<String>)>,
}

impl Citation {
    /// One line for a human: the source span when we have it, the constraint
    /// label and its position in the IR file when we do not.
    fn cite(&self, ir_source: &str) -> String {
        match &self.origin {
            Some((file, line, span_label)) => {
                let what = span_label.as_deref().unwrap_or(&self.label);
                format!("{file}:{line} — {what}")
            }
            None => format!(
                "constraint \"{}\" (#{} in {})",
                self.label, self.index, ir_source
            ),
        }
    }
}

/// The full hypothesis→source mapping for one circuit.
pub struct SourceCitations {
    citations: Vec<Citation>,
    /// Where the IR itself came from (shown when a constraint has no origin).
    ir_source: String,
}

impl SourceCitations {
    /// Build the mapping. `ir_source` is the path the circuit was loaded from.
    /// A circuit whose labels cannot generate hypothesis names (duplicate
    /// labels, …) yields an empty mapping rather than an error — citations
    /// are a diagnostic aid and must never mask the real failure.
    pub fn from_ir(circuit: &CircuitIR, ir_source: &str) -> Self {
        let citations = match lean_emit::constraint_hypothesis_names(circuit) {
            Ok(names) => names
                .into_iter()
                .zip(circuit.constraints.iter())
                .enumerate()
                .map(|(index, (hypothesis, c))| Citation {
                    hypothesis,
                    label: c.label.clone(),
                    index,
                    origin: c
                        .origin
                        .as_ref()
                        .map(|s| (s.file.clone(), s.line, s.label.clone())),
                })
                .collect(),
            Err(_) => Vec::new(),
        };
        SourceCitations {
            citations,
            ir_source: ir_source.to_string(),
        }
    }

    /// The constraints whose hypothesis names appear in `text` (build errors,
    /// goal states). Matches whole identifiers only, so `h_bit_1` does not
    /// implicate itself in a failure that mentions `h_bit_10`.
    pub fn implicated(&self, text: &str) -> Vec<&Citation> {
        self.citations
            .iter()
            .filter(|c| contains_ident(text, &c.hypothesis))
            .collect()
    }

    /// Terminal stall report: which circuit constraints the failing Lean
    /// hypotheses correspond to. `None` when nothing in `text` maps back.
    pub fn render_terminal(&self, text: &str) -> Option<String> {
        let hits = self.implicated(text);
        if hits.is_empty() {
            return None;
        }
        let mut out = format!(
            "the proof stalled on {} constraint(s) from your circuit:\n",
            hits.len()
        );
        for c in &hits {
            out.push_str(&format!("  {}\n", c.cite(&self.ir_source)));
        }
        out.push_str(
            "these are the circuit constraints behind the failing Lean hypotheses — \
             the proof could not get past them",
        );
        Some(out)
    }

    /// Markdown section for NOTES.md. `None` when nothing in `text` maps back.
    pub fn render_markdown(&self, text: &str) -> Option<String> {
        let hits = self.implicated(text);
        if hits.is_empty() {
            return None;
        }
        let mut out = String::from(
            "## Source constraints\n\n\
             The failing Lean hypotheses map back to these circuit constraints:\n\n",
        );
        for c in &hits {
            out.push_str(&format!(
                "- `{}` → {}\n",
                c.hypothesis,
                c.cite(&self.ir_source)
            ));
        }
        out.push('\n');
        Some(out)
    }
}

/// Whole-identifier containment: `ident` occurs in `text` with no identifier
/// character on either side.
fn contains_ident(text: &str, ident: &str) -> bool {
    let bytes = text.as_bytes();
    let is_ident_byte =
        |b: u8| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'' || !b.is_ascii();
    let mut start = 0;
    while let Some(pos) = text[start..].find(ident) {
        let at = start + pos;
        let end = at + ident.len();
        let left_ok = at == 0 || !is_ident_byte(bytes[at - 1]);
        let right_ok = end == bytes.len() || !is_ident_byte(bytes[end]);
        if left_ok && right_ok {
            return true;
        }
        start = at + 1;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuit_ir::{Constraint, SourceSpan, Term, Variable};

    fn ir_with_origins() -> CircuitIR {
        CircuitIR {
            name: "spend".into(),
            modulus: "17".into(),
            private: vec![
                Variable {
                    id: 0,
                    name: "x".into(),
                },
                Variable {
                    id: 1,
                    name: "y".into(),
                },
            ],
            constraints: vec![
                Constraint {
                    label: "nullifier-binding".into(),
                    terms: vec![Term {
                        coeff: "1".into(),
                        vars: vec![0],
                    }],
                    origin: Some(SourceSpan {
                        file: "spend.rs".into(),
                        line: 92,
                        label: Some("enforce_zero(\"nullifier binding\")".into()),
                    }),
                },
                Constraint {
                    label: "bit_1".into(),
                    terms: vec![Term {
                        coeff: "1".into(),
                        vars: vec![1],
                    }],
                    origin: None,
                },
                Constraint {
                    label: "bit_10".into(),
                    terms: vec![Term {
                        coeff: "1".into(),
                        vars: vec![1],
                    }],
                    origin: None,
                },
            ],
            ..Default::default()
        }
    }

    #[test]
    fn origin_span_is_cited_over_the_hypothesis_name() {
        let cites = SourceCitations::from_ir(&ir_with_origins(), "spend.toml");
        let report = cites
            .render_terminal("error: unsolved goals\nh_nullifier_binding : x = 0\n⊢ False")
            .unwrap();
        assert!(report.contains("spend.rs:92 — enforce_zero(\"nullifier binding\")"));
        // the engineer-facing report never leans on the generated name alone
        assert!(report.contains("stalled on 1 constraint(s)"));
    }

    #[test]
    fn originless_constraints_fall_back_to_label_and_ir_position() {
        let cites = SourceCitations::from_ir(&ir_with_origins(), "spend.toml");
        let report = cites.render_terminal("h_bit_1 is impossible").unwrap();
        assert!(report.contains("constraint \"bit_1\" (#1 in spend.toml)"));
    }

    #[test]
    fn identifier_matching_respects_boundaries() {
        let cites = SourceCitations::from_ir(&ir_with_origins(), "spend.toml");
        // h_bit_10 in the text must NOT implicate h_bit_1
        let hits = cites.implicated("only h_bit_10 appears here");
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].label, "bit_10");
        // and both match when both appear
        let hits = cites.implicated("h_bit_1 and h_bit_10");
        assert_eq!(hits.len(), 2);
    }

    #[test]
    fn no_implicated_hypotheses_means_no_report() {
        let cites = SourceCitations::from_ir(&ir_with_origins(), "spend.toml");
        assert!(cites.render_terminal("a timeout occurred").is_none());
        assert!(cites.render_markdown("a timeout occurred").is_none());
    }

    #[test]
    fn markdown_section_lists_hypothesis_to_source_mapping() {
        let cites = SourceCitations::from_ir(&ir_with_origins(), "spend.toml");
        let md = cites
            .render_markdown("h_nullifier_binding and h_bit_1 both stuck")
            .unwrap();
        assert!(md.starts_with("## Source constraints"));
        assert!(md.contains("- `h_nullifier_binding` → spend.rs:92 — enforce_zero"));
        assert!(md.contains("- `h_bit_1` → constraint \"bit_1\" (#1 in spend.toml)"));
    }

    #[test]
    fn real_lean_unsolved_goals_output_is_cited() {
        // Verbatim `lake env lean` output for a stalled 8-bit range-check
        // proof (captured 2026-08-18). The dominant stall class — "unsolved
        // goals" — prints the full context, so the hypothesis names are
        // there to map.
        let real = "ZkGadgets/Bench/StallProbe.lean:41:26: error: unsolved goals\n\
                    p : ℕ\n\
                    inst✝ : Fact (Nat.Prime p)\n\
                    x b0 b1 : ZMod p\n\
                    hp : p > 256\n\
                    h_bit_0 : b0 * b0 - b0 = 0\n\
                    h_decomposition : b0 + 2 * b1 - x = 0\n\
                    ⊢ x.val < 256";

        let ir = CircuitIR {
            name: "demo-range".into(),
            modulus: "17".into(),
            private: vec![
                Variable {
                    id: 0,
                    name: "x".into(),
                },
                Variable {
                    id: 1,
                    name: "b0".into(),
                },
                Variable {
                    id: 2,
                    name: "b1".into(),
                },
            ],
            constraints: vec![
                Constraint {
                    label: "bit_0".into(),
                    terms: vec![Term {
                        coeff: "1".into(),
                        vars: vec![1, 1],
                    }],
                    origin: Some(SourceSpan {
                        file: "range.rs".into(),
                        line: 37,
                        label: Some("assert_boolean(b0)".into()),
                    }),
                },
                Constraint {
                    label: "decomposition".into(),
                    terms: vec![Term {
                        coeff: "1".into(),
                        vars: vec![1],
                    }],
                    origin: Some(SourceSpan {
                        file: "range.rs".into(),
                        line: 41,
                        label: Some("decompose_bits(x, 8)".into()),
                    }),
                },
            ],
            ..Default::default()
        };

        let cites = SourceCitations::from_ir(&ir, "demo-range.toml");
        let report = cites.render_terminal(real).unwrap();
        assert!(report.contains("stalled on 2 constraint(s)"));
        assert!(report.contains("range.rs:37 — assert_boolean(b0)"));
        assert!(report.contains("range.rs:41 — decompose_bits(x, 8)"));
    }

    #[test]
    fn definition_bearing_circuits_are_citable() {
        // Every extracted ragu IR carries definitions (roadmap follow-up F1),
        // so the defs emission path MUST keep h_<label> names visible: since
        // 2026-08-18 the defs-case constraints emit as named antecedent
        // binders `(h_<label> : …) →`, which goal displays and `intro`
        // preserve. This test pins the whole chain: emit → name → citation.
        use circuit_ir::Definition;
        let ir = CircuitIR {
            name: "with-def".into(),
            modulus: "17".into(),
            private: vec![
                Variable {
                    id: 0,
                    name: "x".into(),
                },
                Variable {
                    id: 1,
                    name: "z".into(),
                },
            ],
            definitions: vec![Definition {
                id: 2,
                name: "s".into(),
                terms: vec![Term {
                    coeff: "2".into(),
                    vars: vec![0],
                }],
            }],
            constraints: vec![Constraint {
                label: "uses_s".into(),
                terms: vec![
                    Term {
                        coeff: "1".into(),
                        vars: vec![2],
                    },
                    Term {
                        coeff: "-1".into(),
                        vars: vec![1],
                    },
                ],
                origin: Some(SourceSpan {
                    file: "wires.rs".into(),
                    line: 17,
                    label: Some("add(s, [x, x])".into()),
                }),
            }],
            soundness_spec: Some("z = 2 * x".into()),
            ..Default::default()
        };

        // the scaffold really does emit the named binder for this circuit
        let scaffold = lean_emit::emit_lean(&ir).unwrap();
        assert!(scaffold.contains("(h_uses_s : s - z = 0) →"));

        // goal-state shape after `intro s h_uses_s` on a stalled proof
        let stall = "error: unsolved goals\nx z : ZMod 17\ns : ZMod 17\n\
                     h_uses_s : s - z = 0\n⊢ z = 2 * x";
        let cites = SourceCitations::from_ir(&ir, "with-def.toml");
        let report = cites.render_terminal(stall).unwrap();
        assert!(report.contains("wires.rs:17 — add(s, [x, x])"));
    }

    #[test]
    fn unciteable_circuits_degrade_to_empty_not_error() {
        // duplicate labels make hypothesis-name generation fail; the mapping
        // must degrade silently — citations never mask the real failure
        let mut ir = ir_with_origins();
        ir.constraints[2].label = "bit_1".into();
        let cites = SourceCitations::from_ir(&ir, "spend.toml");
        assert!(cites.render_terminal("h_bit_1 stuck").is_none());
    }
}
