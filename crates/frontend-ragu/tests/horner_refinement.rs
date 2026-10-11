//! Binding checks for a conditional circuit-model refinement, not Rust semantics.
use circuit_ir::CircuitIR;
use frontend_ragu::{extract_circuit, horner::HornerThree, ExtractOptions};
use std::path::PathBuf;

const PROOF: &str = "  dsimp only\n  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15\n  have ha : w14 = w4 * w11 := by\n    linear_combination -h6 + w13 * h8 + w4 * h9\n  have hb : w19 = (w14 + w7) * w11 := by\n    linear_combination -h10 + w18 * h12 + (w14 + w7) * h13\n  linear_combination -h14 + hb + w11 * ha";

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn extract() -> CircuitIR {
    extract_circuit::<ragu_pasta::Fp, _>(
        &HornerThree,
        &ExtractOptions {
            name: "ragu_horner_three".into(),
            // Standard allocator places a₂, a₁, a₀, x on these wires. The complete
            // IR snapshot below binds this mapping to this concrete extraction.
            soundness_spec: Some("out0 = w4 * w11 ^ 2 + w7 * w11 + w8".into()),
            source: "frontend-ragu::horner::HornerThree".into(),
            hypotheses: vec![],
        },
    )
    .unwrap()
}

fn rendered_proof(ir: &CircuitIR) -> String {
    lean_emit::emit_lean(ir)
        .unwrap()
        .replace(
            "theorem ragu_horner_three_sound",
            "set_option linter.unusedVariables false\n\ntheorem ragu_horner_three_sound",
        )
        .replace("  sorry", PROOF)
}

#[test]
fn fresh_ragu_horner_extraction_matches_committed_ir_and_entire_proof() {
    let ir = extract();
    let committed =
        std::fs::read_to_string(root().join("corpus/refinement/ragu-horner-three.json")).unwrap();
    assert_eq!(
        CircuitIR::from_json(&committed).unwrap(),
        ir,
        "Ragu extraction changed: review the model and reprove before accepting drift"
    );
    let proof =
        std::fs::read_to_string(root().join("lean/ZkGadgets/Refinement/RaguHorner.lean")).unwrap();
    assert_eq!(
        proof,
        rendered_proof(&ir),
        "the checked proof must bind the whole emitted context, not a matching substring"
    );
}

#[test]
fn binding_rejects_planted_spec_and_constraint_drift() {
    let good = extract();
    let accepted = rendered_proof(&good);
    let mut wrong_order = good.clone();
    wrong_order.soundness_spec = Some("out0 = w8 * w11 ^ 2 + w7 * w11 + w4".into());
    assert_ne!(rendered_proof(&wrong_order), accepted);
    let mut missing_gate = good;
    missing_gate.constraints.retain(|c| c.label != "g4_mul");
    assert_ne!(rendered_proof(&missing_gate), accepted);
}
