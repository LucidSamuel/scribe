use std::sync::atomic::{AtomicU32, Ordering};

use ragu_circuits::{Circuit, WithAux};
use ragu_core::{
    drivers::{Driver, DriverValue, LinearExpression},
    gadgets::{Bound, Kind},
    Result as RaguResult,
};
use ragu_pasta::Fp;
use ragu_primitives::{allocator::Standard, Element};

use super::circuits::{BooleanBit, SquareChain, SumThenSquare};
use super::*;

fn opts(name: &str) -> ExtractOptions {
    ExtractOptions {
        name: name.to_string(),
        soundness_spec: None,
        hypotheses: vec![],
        source: format!("frontend-ragu::circuits::{name}"),
    }
}

/// Extraction totals must be a pure function of ragu's own accounting:
/// `constraints = 2·gates + lc-constraints` — the `2·gates` term is the
/// `A·B − C = 0` **and** `C·D = 0` pair. If this identity breaks, a gate
/// constraint was dropped.
fn assert_counts(ir: &CircuitIR, gates: usize, lc: usize) {
    assert_eq!(
        ir.constraints.len(),
        2 * gates + lc,
        "{}: constraint total must be 2·gates + lc-constraints",
        ir.name
    );
    assert_eq!(
        ir.constraints
            .iter()
            .filter(|c| c.label.ends_with("_aux"))
            .count(),
        gates,
        "{}: every gate must carry its C·D = 0 constraint",
        ir.name
    );
}

#[test]
fn modulus_decimal_is_pallas_base_field() {
    // Pallas base field: p = 2^254 + 45560315531419706090280762371685220353.
    // Also pins the little-endian `to_repr` assumption in `signed_decimal`.
    assert_eq!(
        modulus_decimal::<Fp>(),
        "28948022309329048855892746252171976963363056481941560715954676764349967630337"
    );
}

#[test]
fn signed_decimal_renders_small_negatives() {
    assert_eq!(signed_decimal(Fp::from(5)), "5");
    assert_eq!(signed_decimal(-Fp::from(3)), "-3");
    assert_eq!(signed_decimal(Fp::from(0)), "0");
    assert_eq!(
        coeff_decimal(&Coeff::Arbitrary(-Fp::from(7))),
        Some("-7".to_string())
    );
    assert_eq!(
        coeff_decimal(&Coeff::NegativeArbitrary(Fp::from(7))),
        Some("-7".to_string())
    );
    assert_eq!(coeff_decimal(&Coeff::<Fp>::Zero), None);
    assert_eq!(coeff_decimal(&Coeff::Arbitrary(Fp::from(0))), None);
}

#[test]
fn cargo_manifest_pins_the_recorded_ragu_rev() {
    let manifest = include_str!("../Cargo.toml");
    assert!(
        manifest.contains(&format!("rev = \"{RAGU_REV}\"")),
        "Cargo.toml ragu pins must match RAGU_REV ({RAGU_REV})"
    );
    // and nothing else is pinned: every ragu dep uses the same rev
    assert_eq!(
        manifest.matches("tachyon-zcash/ragu").count(),
        manifest.matches(RAGU_REV).count(),
        "every ragu git dependency must carry the recorded rev"
    );
}

#[test]
fn boolean_bit_extracts_faithfully() {
    let ir = extract_circuit::<Fp, _>(&BooleanBit, &opts("boolean")).unwrap();

    // SYSTEM gate + Boolean::alloc gate; c = 0, a + b = 1, the public
    // binding, and the ONE constraint.
    assert_counts(&ir, 2, 4);
    assert_eq!(ir.constraints.len(), 8);

    // Visibility: the bit is the instance, not a private wire.
    assert_eq!(ir.public.len(), 1);
    assert_eq!(ir.public[0].name, "out0");
    // one + 2 gates × (a, b, c) + the alloc gate's d wire
    assert_eq!(ir.private.len(), 8);
    assert_eq!(ir.private[0].name, "one");
    assert!(
        ir.definitions.is_empty(),
        "Boolean::alloc never calls add()"
    );

    // The hidden D-wire constraint of the boolean gate is present and refers
    // to the gate's own (fresh) d wire, while the SYSTEM gate's aux
    // constraint refers to `one` (id 0) — ragu's d₀ *is* the ONE wire.
    let aux0 = ir.constraints.iter().find(|c| c.label == "g0_aux").unwrap();
    assert_eq!(aux0.terms[0].vars[1], 0);
    let aux1 = ir.constraints.iter().find(|c| c.label == "g1_aux").unwrap();
    assert_ne!(aux1.terms[0].vars[1], 0);

    // Provenance pins the ragu revision.
    assert_eq!(ir.provenance.frontend, "frontend-ragu");
    assert_eq!(ir.provenance.source_rev.as_deref(), Some(RAGU_REV));

    // The IR emits as Lean without error.
    let lean = lean_emit::emit_lean(&ir).unwrap();
    assert!(lean.contains("(out0 : ZMod p)"));
    assert!(lean.contains("h_g1_aux"));
}

#[test]
fn counts_match_host_metrics_across_circuit_shapes() {
    // extract_circuit() self-validates against ragu_circuits::metrics on
    // every call and returns SelfValidation on disagreement, so a successful
    // extraction *is* the count assertion. Cover several shapes.
    extract_circuit::<Fp, _>(&BooleanBit, &opts("boolean")).unwrap();
    extract_circuit::<Fp, _>(&SumThenSquare, &opts("sum-then-square")).unwrap();
    for times in [0, 1, 5, 16] {
        extract_circuit::<Fp, _>(&SquareChain { times }, &opts("square-chain")).unwrap();
    }
}

#[test]
fn square_chain_scales_one_gate_per_square() {
    let base = extract_circuit::<Fp, _>(&SquareChain { times: 0 }, &opts("sq0")).unwrap();
    let five = extract_circuit::<Fp, _>(&SquareChain { times: 5 }, &opts("sq5")).unwrap();
    // Each square is one gate (two constraints) plus its enforce_equal
    // linear constraint(s); the delta must be uniform.
    let delta = five.constraints.len() - base.constraints.len();
    assert_eq!(delta % 5, 0);
    assert!(five.public.len() == 1 && base.public.len() == 1);
}

#[test]
fn add_becomes_definition_not_constraint() {
    let ir = extract_circuit::<Fp, _>(&SumThenSquare, &opts("sum-then-square")).unwrap();
    assert!(
        !ir.definitions.is_empty(),
        "Driver::add must record a Definition"
    );
    let def = &ir.definitions[0];
    // x + y: two unit-coefficient terms over allocated wires.
    assert_eq!(def.terms.len(), 2);
    assert!(def
        .terms
        .iter()
        .all(|t| t.coeff == "1" && t.vars.len() == 1));
    // The definition id is referenced from at least one constraint (the
    // square gate's equality with the virtual sum wire).
    assert!(
        ir.constraints
            .iter()
            .flat_map(|c| &c.terms)
            .any(|t| t.vars.contains(&def.id)),
        "definition must be referenced by id from a constraint"
    );
    // And the IR emits as Lean with a let-binding.
    let lean = lean_emit::emit_lean(&ir).unwrap();
    assert!(lean.contains(&format!("let {} :=", def.name)));
}

/// Phase A follow-up F1, closed: lean-emit's decomposed mode used to fall
/// back to the plain scaffold whenever definitions were present — which hit
/// every ragu gadget using `add()` (most do). Each helper lemma now restates
/// the definitions its constraint transitively reaches as a `let` prefix, so
/// definition-bearing extracted IR gets a real decomposed scaffold.
#[test]
fn decomposed_mode_emits_helpers_on_definition_bearing_ragu_ir() {
    let mut with_defs = 0;
    let mut total = 0;

    let irs = [
        extract_circuit::<Fp, _>(&BooleanBit, &opts("boolean")).unwrap(),
        extract_circuit::<Fp, _>(&SumThenSquare, &opts("sum-then-square")).unwrap(),
        extract_circuit::<Fp, _>(&SquareChain { times: 3 }, &opts("sq3")).unwrap(),
    ];
    for mut ir in irs {
        ir.soundness_spec = Some("True".to_string());
        total += 1;
        if !ir.definitions.is_empty() {
            with_defs += 1;
            // decomposed output is a real decomposed scaffold: per-constraint
            // helper lemmas, distinct from the plain single-theorem scaffold,
            // with the reached definition restated as a `let` prefix on at
            // least one helper (the definition is referenced by a constraint,
            // asserted by add_becomes_definition_not_constraint).
            let decomposed = lean_emit::emit_lean_decomposed(&ir).unwrap();
            let plain = lean_emit::emit_lean(&ir).unwrap();
            assert_ne!(
                decomposed, plain,
                "decomposed mode must not fall back on definitions (F1 closed)"
            );
            assert!(
                decomposed.contains("lemma") && decomposed.contains("_extract_"),
                "decomposed scaffold lacks helper lemmas for {}",
                ir.name
            );
            let def_let = format!("let {} :=", ir.definitions[0].name);
            // helper lemmas live between the doc header and the main theorem
            // (`\ntheorem ` only matches the real declaration line)
            let helpers = &decomposed[..decomposed.find("\ntheorem ").unwrap()];
            assert!(
                helpers.contains(&def_let),
                "no helper lemma restates `{def_let}` for {}",
                ir.name
            );
        }
    }
    // 1 of 3 here; on real gadget libraries the ratio only goes up, because
    // linear combinations are ragu's free primitive.
    assert_eq!((with_defs, total), (1, 3));
}

// ─── Self-validation: the extractor is checked, not trusted ─────────────────

/// A circuit that violates ragu's determinism contract: the second `witness`
/// call emits one extra constraint. `extract_circuit` runs `witness` once and
/// then hands the circuit to ragu's own metrics pass, which runs it again —
/// so the counts disagree and extraction must refuse to emit IR.
struct FlakyCircuit {
    witness_calls: AtomicU32,
}

impl Circuit<Fp> for FlakyCircuit {
    type Instance<'source> = Fp;
    type Witness<'source> = Fp;
    type Output = Kind![Fp; Element<'_, _>];
    type Aux<'source> = ();

    fn instance<'dr, 'source: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        instance: DriverValue<D, Fp>,
    ) -> RaguResult<Bound<'dr, D, Self::Output>> {
        let allocator = &mut Standard::new();
        Element::alloc(dr, allocator, instance)
    }

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Fp>,
    ) -> RaguResult<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, ()>>> {
        let allocator = &mut Standard::new();
        let x = Element::alloc(dr, allocator, witness)?;
        if self.witness_calls.fetch_add(1, Ordering::SeqCst) > 0 {
            dr.enforce_zero(|lc| lc.add(x.wire()))?;
        }
        Ok(WithAux::new(x, D::unit()))
    }
}

#[test]
fn nondeterministic_constraint_emission_fails_self_validation() {
    let circuit = FlakyCircuit {
        witness_calls: AtomicU32::new(0),
    };
    let err = extract_circuit::<Fp, _>(&circuit, &opts("flaky")).unwrap_err();
    match err {
        FrontendError::SelfValidation { message } => {
            assert!(message.contains("ragu_circuits::metrics"), "{message}");
        }
        other => panic!("expected SelfValidation, got {other:?}"),
    }
}

// ─── Frontend trait plumbing ────────────────────────────────────────────────

#[test]
fn frontend_trait_reaches_the_same_extraction() {
    let frontend = RaguFrontend::<Fp, _>::new(BooleanBit);
    assert_eq!(frontend.name(), "ragu");
    let ir = frontend.extract(&opts("boolean")).unwrap();
    assert_eq!(
        ir,
        extract_circuit::<Fp, _>(&BooleanBit, &opts("boolean")).unwrap()
    );
}

// ─── Golden artifact: the Phase B proof target ──────────────────────────────

fn corpus_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("corpus/circuits/ragu-boolean.json")
}

fn schema_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("schema/circuit-ir-v1.json")
}

/// The committed corpus artifact must be exactly what extraction produces
/// today. Regenerate with `BLESS_RAGU_IR=1 cargo test -p frontend-ragu`.
#[test]
fn committed_boolean_ir_matches_fresh_extraction() {
    let ir = boolean_bit_ir().unwrap();
    let json = ir.to_json().unwrap();

    if std::env::var("BLESS_RAGU_IR").is_ok() {
        std::fs::write(corpus_path(), format!("{json}\n")).unwrap();
    }

    let committed = std::fs::read_to_string(corpus_path())
        .expect("corpus/circuits/ragu-boolean.json missing — run with BLESS_RAGU_IR=1");
    let committed_ir = CircuitIR::from_json(&committed).unwrap();
    assert_eq!(
        committed_ir, ir,
        "committed ragu-boolean.json is stale — regenerate with BLESS_RAGU_IR=1"
    );
}

/// The committed kernel-checked proof must prove *exactly* the statement
/// lean-emit regenerates from the extracted IR — same binders, same
/// constraint hypotheses, same spec. Anything else and the artifact proves
/// "some theorem that builds green", not this circuit.
#[test]
fn committed_lean_proof_carries_the_emitted_statement() {
    let ir = boolean_bit_ir().unwrap();
    let scaffold = lean_emit::emit_lean(&ir).unwrap();
    // Anchor on the declaration itself, at line start — the doc comment also
    // contains the phrase "theorem statement".
    let start = scaffold
        .find("\ntheorem ")
        .expect("scaffold declares a theorem")
        + 1;
    let end = scaffold
        .find(" := by\n")
        .expect("scaffold ends in a proof hole");
    let statement = &scaffold[start..end];

    if std::env::var("BLESS_RAGU_IR").is_ok() {
        // Convenience: dump the fresh scaffold to the temp dir for manual
        // (re)proving when the extraction changes.
        let out = std::env::temp_dir().join("RaguBoolean.scaffold.lean");
        std::fs::write(out, &scaffold).unwrap();
    }

    let proof = std::fs::read_to_string(proof_path())
        .expect("lean/ZkGadgets/RaguBoolean.lean missing — the Phase B proof target");
    assert!(
        proof.contains(statement),
        "RaguBoolean.lean no longer states the theorem the IR regenerates:\n{statement}"
    );
    // The binder context must match too, or the statement means something else.
    assert!(proof.contains("variable (p : ℕ) [Fact (Nat.Prime p)]"));
    assert!(!proof.contains("sorry"));
    assert!(proof.contains("#audit_axioms ragu_boolean_sound"));
}

fn proof_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("lean/ZkGadgets/RaguBoolean.lean")
}

#[test]
fn extracted_ir_validates_against_the_schema() {
    let schema: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(schema_path()).unwrap()).unwrap();
    let validator = jsonschema::validator_for(&schema).unwrap();
    let value: serde_json::Value =
        serde_json::from_str(&boolean_bit_ir().unwrap().to_json().unwrap()).unwrap();
    let errors: Vec<String> = validator
        .iter_errors(&value)
        .map(|e| e.to_string())
        .collect();
    assert!(errors.is_empty(), "schema violations: {errors:?}");
}

#[test]
fn constraints_carry_gadget_source_spans() {
    // Follow-up F3: `#[track_caller]` on the extractor's `enforce_zero` and
    // `gate` impls captures the GADGET source line each constraint came from
    // — the immediate caller is ragu_primitives' gadget code, not ragu
    // internals — so D2 diagnostics can cite `boolean.rs:NN` instead of a
    // generated hypothesis name.
    let ir = boolean_bit_ir().unwrap();

    let origin_of = |label: &str| {
        ir.constraints
            .iter()
            .find(|c| c.label == label)
            .unwrap_or_else(|| panic!("no constraint {label}"))
            .origin
            .clone()
    };

    // Gadget-emitted constraints cite ragu_primitives' boolean gadget.
    for label in ["lc0", "lc1", "g1_mul", "g1_aux"] {
        let origin = origin_of(label).unwrap_or_else(|| panic!("{label} lost its origin"));
        assert!(
            origin.file.contains("ragu_primitives") && origin.file.ends_with("boolean.rs"),
            "{label} cites {}:{} — expected the boolean gadget source",
            origin.file,
            origin.line
        );
        assert!(origin.line > 0);
    }
    // The gate pair shares one call site; the two enforce_zero lines differ.
    assert_eq!(origin_of("g1_mul"), origin_of("g1_aux"));
    assert_ne!(origin_of("lc0"), origin_of("lc1"));

    // Extractor-emitted bookkeeping (SYSTEM gate, output binding, the ONE
    // constraint) has no user source line and must stay origin-free rather
    // than citing scribe's own internals.
    for label in ["g0_mul", "g0_aux", "out0_bind", "one_is_1"] {
        assert!(origin_of(label).is_none(), "{label} should carry no origin");
    }
}
