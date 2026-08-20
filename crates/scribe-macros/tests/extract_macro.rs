//! The worked example the D1 acceptance asks for: `extract!` on a real ragu
//! circuit, from a plain `cargo test`, producing schema-valid CircuitIR JSON.

use frontend_ragu::circuits::BooleanBit;
use ragu_pasta::Fp;
use scribe_macros as scribe;

// One line per circuit — this is the entire integration a user writes.
scribe::extract!(
    ragu_boolean_bit,
    Fp,
    BooleanBit,
    spec = "out0 = 0 ∨ out0 = 1"
);

/// Runs after the macro-generated test in the same process would be flaky
/// (test order is not guaranteed), so this test re-runs the extraction
/// itself and checks the artifact end-to-end: written where documented,
/// version-gated on the way back in, spec carried, sources cited.
#[test]
fn extracted_json_round_trips() {
    ragu_boolean_bit(); // deterministic: same extraction, same bytes

    let path = scribe::scribe_out_dir(env!("CARGO_MANIFEST_DIR")).join("ragu_boolean_bit.json");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("extract! artifact missing at {}: {e}", path.display()));

    // from_json enforces ir_version — the artifact is interchange-grade.
    let ir = circuit_ir::CircuitIR::from_json(&text).unwrap();
    assert_eq!(ir.name, "ragu-boolean-bit");
    assert_eq!(ir.soundness_spec.as_deref(), Some("out0 = 0 ∨ out0 = 1"));
    assert_eq!(ir.public.len(), 1, "instance-derived public surface");
    assert!(ir.provenance.source.contains("extract_macro.rs"));
    assert_eq!(
        ir.provenance.source_rev.as_deref(),
        Some(frontend_ragu::RAGU_REV)
    );

    // F3: gadget-emitted constraints carry real source spans.
    assert!(ir.constraints.iter().any(|c| c
        .origin
        .as_ref()
        .is_some_and(|o| o.file.ends_with("boolean.rs"))));
}
