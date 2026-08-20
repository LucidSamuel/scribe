//! frontend-ragu — extract [`CircuitIR`] from ragu circuits through the
//! `Driver` trait (roadmap v2.1, Phase B).
//!
//! Ragu circuits never talk to a prover; they talk to a [`Driver`]. This crate
//! implements a **structure-only** driver (`MaybeKind = Empty`, so witness
//! closures are never called and are dead-code eliminated) that records every
//! gate, definition, and constraint a circuit emits into a [`CircuitIR`].
//! One driver reaches every circuit written against ragu's API — there is no
//! per-circuit adapter (G3).
//!
//! ## Faithfulness rules
//!
//! - `gate()` imposes **two** constraints: `A·B − C = 0` **and** `C·D = 0`.
//!   `Driver::mul` hides the `D` wire, which makes the second constraint the
//!   natural thing to drop — and dropping it yields an IR *weaker* than the
//!   circuit, making any soundness proof against it prove the wrong thing.
//!   (Ragu's own `qa/crates/lean_extraction` driver deliberately under-models
//!   this; scribe's does not.) Both constraints are recorded per gate.
//! - `add(lc)` is a virtual wire: it becomes a [`Definition`] in the shared
//!   variable id space, never an inlined expression and never a constraint.
//! - Visibility is extracted, not defaulted: `Circuit::instance()` determines
//!   the verifier-visible surface, `Circuit::witness()` the constraint set,
//!   and the two are cross-checked. See [`extract_circuit`].
//!
//! ## Self-validation (locked decision 6)
//!
//! Every extraction re-runs the same circuit through ragu's own
//! `ragu_circuits::metrics` pass (via `testing::synthesis_counts`) and fails
//! hard — [`FrontendError::SelfValidation`] — if gate or constraint counts
//! disagree. The extractor is checked, not trusted.

use std::collections::HashMap;
use std::marker::PhantomData;

use circuit_ir::{CircuitIR, Constraint, Definition, Hypothesis, Provenance, Term, Variable};
use num_bigint::BigUint;
use ragu_arithmetic::{
    ff::{FromUniformBytes, PrimeField},
    Coeff,
};
use ragu_circuits::{testing::synthesis_counts, Circuit};
use ragu_core::{
    drivers::{Driver, DriverTypes, LinearExpression},
    gadgets::Bound,
    maybe::Empty,
};
use ragu_primitives::{io::Write, Element};
use scribe_frontend::{Frontend, FrontendError};

pub mod circuits;

/// The ragu revision this extractor is built and validated against. Must match
/// the `rev =` pins in this crate's `Cargo.toml` (a test enforces this) and is
/// stamped into every extracted IR's provenance.
pub const RAGU_REV: &str = "fc61822cf8c248d36b950c89817bf170d533a7f3";

// ─── Source spans (Phase A follow-up F3) ─────────────────────────────────────

/// The caller's source span, trimmed for diagnostics: cargo's git-checkout
/// paths are long, so keep the portion from the last `crates/` component when
/// present (`crates/ragu_primitives/src/boolean.rs`), else the last two path
/// components.
fn caller_span(loc: &'static std::panic::Location<'static>) -> Option<circuit_ir::SourceSpan> {
    let file = loc.file();
    let trimmed = match file.rfind("crates/") {
        Some(i) => &file[i..],
        None => {
            let mut parts: Vec<&str> = file.rsplitn(3, '/').collect();
            parts.truncate(2);
            parts.reverse();
            return Some(circuit_ir::SourceSpan {
                file: parts.join("/"),
                line: loc.line(),
                label: None,
            });
        }
    };
    Some(circuit_ir::SourceSpan {
        file: trimmed.to_string(),
        line: loc.line(),
        label: None,
    })
}

// ─── Linear-combination recorder ─────────────────────────────────────────────

/// A [`LinearExpression`] that records terms symbolically instead of
/// evaluating them. Wire type is the extractor's wire id (`usize`).
///
/// Ragu's gain discipline is honored: every term is scaled by the gain at the
/// moment it is added, and `gain()` composes multiplicatively.
pub struct RecordedLc<F: PrimeField> {
    terms: Vec<(usize, Coeff<F>)>,
    gain: Coeff<F>,
}

impl<F: PrimeField> Default for RecordedLc<F> {
    fn default() -> Self {
        RecordedLc {
            terms: Vec::new(),
            gain: Coeff::One,
        }
    }
}

impl<F: PrimeField> LinearExpression<usize, F> for RecordedLc<F> {
    fn add_term(mut self, wire: &usize, coeff: Coeff<F>) -> Self {
        let effective = coeff * self.gain;
        if !effective.is_zero() {
            self.terms.push((*wire, effective));
        }
        self
    }

    fn gain(mut self, coeff: Coeff<F>) -> Self {
        self.gain = self.gain * coeff;
        self
    }
}

impl<F: PrimeField> RecordedLc<F> {
    /// Collapse the recorded terms into IR terms: coefficients of the same
    /// wire are summed (first-appearance order preserved), zero sums dropped.
    fn into_terms(self) -> Vec<Term> {
        let mut order: Vec<usize> = Vec::new();
        let mut acc: HashMap<usize, Coeff<F>> = HashMap::new();
        for (wire, coeff) in self.terms {
            match acc.get_mut(&wire) {
                Some(existing) => *existing = *existing + coeff,
                None => {
                    order.push(wire);
                    acc.insert(wire, coeff);
                }
            }
        }
        order
            .into_iter()
            .filter_map(|wire| {
                coeff_decimal(&acc[&wire]).map(|coeff| Term {
                    coeff,
                    vars: vec![wire],
                })
            })
            .collect()
    }
}

// ─── Field-element rendering ─────────────────────────────────────────────────

/// The field modulus as a decimal string. `PrimeField::MODULUS` is
/// hexadecimal (with or without a `0x` prefix); a test pins the known Pallas
/// value so a format change upstream fails loudly.
pub fn modulus_decimal<F: PrimeField>() -> String {
    modulus_biguint::<F>().to_string()
}

fn modulus_biguint<F: PrimeField>() -> BigUint {
    let s = F::MODULUS.trim_start_matches("0x").trim_start_matches("0X");
    BigUint::parse_bytes(s.as_bytes(), 16)
        .or_else(|| BigUint::parse_bytes(s.as_bytes(), 10))
        .expect("PrimeField::MODULUS must be a hex or decimal string")
}

/// A field element as a signed decimal string: elements above `p/2` render as
/// their (small) negative representative, so `-ONE` is `"-1"` rather than a
/// 77-digit constant. Assumes the little-endian `to_repr` layout shared by
/// the pasta fields (pinned by a test).
fn signed_decimal<F: PrimeField>(value: F) -> String {
    let n = BigUint::from_bytes_le(value.to_repr().as_ref());
    let p = modulus_biguint::<F>();
    if n.clone() * 2u8 > p {
        format!("-{}", p - n)
    } else {
        n.to_string()
    }
}

/// Render a coefficient as the IR's decimal string. `None` means the term is
/// zero and should be dropped.
fn coeff_decimal<F: PrimeField>(coeff: &Coeff<F>) -> Option<String> {
    match coeff {
        Coeff::Zero => None,
        Coeff::One => Some("1".to_string()),
        Coeff::Two => Some("2".to_string()),
        Coeff::NegativeOne => Some("-1".to_string()),
        Coeff::Arbitrary(_) | Coeff::NegativeArbitrary(_) => {
            if coeff.is_zero() {
                None
            } else {
                Some(signed_decimal(coeff.value()))
            }
        }
    }
}

// ─── The extraction driver ───────────────────────────────────────────────────

/// Structure-only ragu driver that records gates, definitions, and
/// constraints. Wires are `usize` ids in a single namespace shared by
/// variables and definitions (`Term.vars` holds ids, so definitions must be
/// referenceable exactly like variables).
///
/// Id 0 is reserved for the `one` wire ([`Driver::ONE`]); in ragu that wire
/// *is* the SYSTEM gate's `D` wire, and [`Extractor::system_gate`] preserves
/// that identification.
pub struct Extractor<F: PrimeField> {
    next_id: usize,
    num_gates: usize,
    /// `enforce_zero`-shaped constraints only (the count ragu's metrics pass
    /// reports as `num_constraints`). Gate constraints are counted via
    /// `num_gates`, two per gate.
    num_lc_constraints: usize,
    variables: Vec<Variable>,
    definitions: Vec<Definition>,
    constraints: Vec<Constraint>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Extractor<F> {
    pub fn new() -> Self {
        Extractor {
            next_id: 1,
            num_gates: 0,
            num_lc_constraints: 0,
            variables: vec![Variable {
                id: 0,
                name: "one".to_string(),
            }],
            definitions: Vec::new(),
            constraints: Vec::new(),
            _marker: PhantomData,
        }
    }

    fn fresh_var(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.variables.push(Variable {
            id,
            name: format!("w{id}"),
        });
        id
    }

    fn push_gate_constraints(
        &mut self,
        gate: usize,
        a: usize,
        b: usize,
        c: usize,
        d: usize,
        origin: Option<circuit_ir::SourceSpan>,
    ) {
        // A·B − C = 0
        self.constraints.push(Constraint {
            label: format!("g{gate}_mul"),
            terms: vec![
                Term {
                    coeff: "1".to_string(),
                    vars: vec![a, b],
                },
                Term {
                    coeff: "-1".to_string(),
                    vars: vec![c],
                },
            ],
            origin: origin.clone(),
        });
        // C·D = 0 — the constraint `Driver::mul` hides. Never drop it.
        self.constraints.push(Constraint {
            label: format!("g{gate}_aux"),
            terms: vec![Term {
                coeff: "1".to_string(),
                vars: vec![c, d],
            }],
            origin,
        });
    }

    /// Allocate the SYSTEM gate (gate 0), mirroring ragu's orchestration.
    /// Its `D` wire is *the* `one` wire (id 0) — ragu assigns `d₀ = 1` at
    /// trace assembly and `Driver::ONE` refers to it by convention — so the
    /// SYSTEM gate's `C·D = 0` constraint correctly reads `c·one = 0`.
    fn system_gate(&mut self) {
        let gate = self.num_gates;
        let a = self.fresh_var();
        let b = self.fresh_var();
        let c = self.fresh_var();
        self.push_gate_constraints(gate, a, b, c, 0, None);
        self.num_gates += 1;
    }

    /// Bind the `i`-th written public output wire to a fresh **public**
    /// variable `out{i}` (a coefficient slot of the instance polynomial
    /// `k(Y)`). Mirrors orchestration's `enforce_zero(lc.add(output.wire()))`,
    /// where the `k(Y)` side is implicit in the constraint's `Y`-position.
    fn bind_output(&mut self, index: usize, wire: usize) -> Variable {
        let id = self.next_id;
        self.next_id += 1;
        let variable = Variable {
            id,
            name: format!("out{index}"),
        };
        self.constraints.push(Constraint {
            label: format!("out{index}_bind"),
            terms: vec![
                Term {
                    coeff: "1".to_string(),
                    vars: vec![wire],
                },
                Term {
                    coeff: "-1".to_string(),
                    vars: vec![id],
                },
            ],
            origin: None,
        });
        self.num_lc_constraints += 1;
        variable
    }

    /// The final ONE constraint: `one` is enforced against the constant term
    /// of `k(Y)`, which the verifier fixes to 1 (`k(0) = 1`), i.e. `one − 1 = 0`.
    fn enforce_one(&mut self) {
        self.constraints.push(Constraint {
            label: "one_is_1".to_string(),
            terms: vec![
                Term {
                    coeff: "1".to_string(),
                    vars: vec![0],
                },
                Term {
                    coeff: "-1".to_string(),
                    vars: vec![],
                },
            ],
            origin: None,
        });
        self.num_lc_constraints += 1;
    }
}

impl<F: PrimeField> Default for Extractor<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: PrimeField> DriverTypes for Extractor<F> {
    type ImplField = F;
    type ImplWire = usize;
    type MaybeKind = Empty;
    type LCadd = RecordedLc<F>;
    type LCenforce = RecordedLc<F>;
    /// The `D` wire's id. Returned by `gate` and consumed by `assign_extra`;
    /// the wire is allocated (and its `C·D = 0` constraint recorded) at gate
    /// time, so redeeming the token later never changes the constraint set.
    type Extra = usize;

    #[track_caller]
    fn gate(
        &mut self,
        _values: impl Fn() -> ragu_core::Result<(Coeff<F>, Coeff<F>, Coeff<F>)>,
    ) -> ragu_core::Result<(usize, usize, usize, usize)> {
        let origin = caller_span(std::panic::Location::caller());
        let gate = self.num_gates;
        let a = self.fresh_var();
        let b = self.fresh_var();
        let c = self.fresh_var();
        let d = self.fresh_var();
        self.push_gate_constraints(gate, a, b, c, d, origin);
        self.num_gates += 1;
        Ok((a, b, c, d))
    }

    fn assign_extra(
        &mut self,
        extra: usize,
        _value: impl Fn() -> ragu_core::Result<Coeff<F>>,
    ) -> ragu_core::Result<usize> {
        Ok(extra)
    }
}

impl<'dr, F: PrimeField> Driver<'dr> for Extractor<F> {
    type F = F;
    type Wire = usize;

    const ONE: usize = 0;

    /// A virtual wire: a fresh id defined as a linear form over existing
    /// wires. No constraint is emitted — unlimited fan-in addition is free in
    /// ragu's circuit model — so this becomes a [`Definition`], not a
    /// [`Constraint`].
    fn add(&mut self, lc: impl Fn(RecordedLc<F>) -> RecordedLc<F>) -> usize {
        let terms = lc(RecordedLc::default()).into_terms();
        let id = self.next_id;
        self.next_id += 1;
        self.definitions.push(Definition {
            id,
            name: format!("v{id}"),
            terms,
        });
        id
    }

    /// `#[track_caller]`: the immediate caller of `enforce_zero` is gadget
    /// code (e.g. `ragu_primitives/src/boolean.rs`), so the captured span is
    /// the source line the constraint came from — what D2's diagnostics cite
    /// instead of a generated hypothesis name (follow-up F3).
    #[track_caller]
    fn enforce_zero(
        &mut self,
        lc: impl Fn(RecordedLc<F>) -> RecordedLc<F>,
    ) -> ragu_core::Result<()> {
        let origin = caller_span(std::panic::Location::caller());
        let terms = lc(RecordedLc::default()).into_terms();
        self.constraints.push(Constraint {
            label: format!("lc{}", self.num_lc_constraints),
            terms,
            origin,
        });
        self.num_lc_constraints += 1;
        Ok(())
    }
}

// ─── Extraction ──────────────────────────────────────────────────────────────

/// What the extractor cannot learn from the driver stream: a name, the spec,
/// and any extra hypotheses (e.g. field-size bounds) the spec needs.
#[derive(Debug, Clone, Default)]
pub struct ExtractOptions {
    /// IR name (becomes the Lean theorem name after sanitization).
    pub name: String,
    /// Raw Lean proposition over the IR's variable names (v2.1 keeps specs
    /// unstructured by design).
    pub soundness_spec: Option<String>,
    /// Extra theorem hypotheses.
    pub hypotheses: Vec<Hypothesis>,
    /// Human-readable origin of the circuit (stamped into provenance).
    pub source: String,
}

/// Write a circuit output gadget and return the written wire ids, mirroring
/// ragu's orchestration step 3.
fn written_wires<'dr, F, D, K>(
    dr: &mut D,
    output: &Bound<'dr, D, K>,
) -> ragu_core::Result<Vec<usize>>
where
    F: PrimeField,
    D: Driver<'dr, F = F, Wire = usize>,
    K: Write<F>,
{
    let mut sink: Vec<Element<'dr, D>> = Vec::new();
    K::write_gadget(output, dr, &mut sink)?;
    Ok(sink.iter().map(|element| *element.wire()).collect())
}

fn ragu_error(context: &str, e: impl std::fmt::Debug) -> FrontendError {
    FrontendError::Parse {
        source: context.to_string(),
        message: format!("{e:?}"),
    }
}

/// Extract a ragu circuit into [`CircuitIR`].
///
/// Replicates ragu's constraint-emission orchestration exactly:
///
/// 1. SYSTEM gate (gate 0, `D` wire = `one`),
/// 2. `Circuit::witness` (the circuit body),
/// 3. write public outputs, binding each written wire to a public `out{i}`
///    variable (the `k(Y)` coefficient the verifier checks),
/// 4. the ONE constraint (`one = 1`, i.e. `k(0) = 1`).
///
/// Visibility is cross-checked rather than trusted: `Circuit::instance()` is
/// run on a scratch driver to independently determine the verifier-visible
/// arity, which must equal the number of wires `witness()`'s output writes,
/// and every written wire must have been allocated or defined by the run.
/// Gate/constraint counts are then compared against ragu's own metrics pass
/// and any disagreement is a hard [`FrontendError::SelfValidation`] error.
pub fn extract_circuit<F, C>(circuit: &C, opts: &ExtractOptions) -> Result<CircuitIR, FrontendError>
where
    F: PrimeField + FromUniformBytes<64>,
    C: Circuit<F>,
{
    // 1b (visibility). Verifier-visible surface, independent of the witness
    // pass: instance() needs no witness data and returns the same Output
    // gadget kind the verifier's k(Y) serializes.
    let instance_arity = {
        let mut dr = Extractor::<F>::new();
        dr.system_gate();
        let output = circuit
            .instance(&mut dr, Empty)
            .map_err(|e| ragu_error(&opts.name, e))?;
        written_wires::<F, _, C::Output>(&mut dr, &output)
            .map_err(|e| ragu_error(&opts.name, e))?
            .len()
    };

    // 1–2. SYSTEM gate + circuit body.
    let mut dr = Extractor::<F>::new();
    dr.system_gate();
    let output = circuit
        .witness(&mut dr, Empty)
        .map_err(|e| ragu_error(&opts.name, e))?
        .into_output();

    // 3. Public outputs.
    let wires = written_wires::<F, _, C::Output>(&mut dr, &output)
        .map_err(|e| ragu_error(&opts.name, e))?;
    if wires.len() != instance_arity {
        return Err(FrontendError::SelfValidation {
            message: format!(
                "witness() wrote {} public output wire(s) but instance() describes {}",
                wires.len(),
                instance_arity
            ),
        });
    }
    let allocated = dr.next_id;
    if let Some(bad) = wires.iter().find(|w| **w >= allocated) {
        return Err(FrontendError::SelfValidation {
            message: format!("public output wire id {bad} was never allocated by the witness run"),
        });
    }
    let public: Vec<Variable> = wires
        .iter()
        .enumerate()
        .map(|(index, wire)| dr.bind_output(index, *wire))
        .collect();

    // 4. ONE constraint.
    dr.enforce_one();

    // Self-validation against the host framework (locked decision 6): ragu's
    // own metrics pass over the same circuit must report exactly the gate and
    // constraint counts we recorded.
    let counts = synthesis_counts::<F, C>(circuit).map_err(|e| ragu_error(&opts.name, e))?;
    if counts.num_gates != dr.num_gates || counts.num_constraints != dr.num_lc_constraints {
        return Err(FrontendError::SelfValidation {
            message: format!(
                "extracted {} gate(s) / {} linear constraint(s), but ragu_circuits::metrics \
                 reports {} / {}",
                dr.num_gates, dr.num_lc_constraints, counts.num_gates, counts.num_constraints
            ),
        });
    }

    Ok(CircuitIR {
        name: opts.name.clone(),
        modulus: modulus_decimal::<F>(),
        provenance: Provenance {
            frontend: "frontend-ragu".to_string(),
            frontend_version: env!("CARGO_PKG_VERSION").to_string(),
            source: opts.source.clone(),
            source_rev: Some(RAGU_REV.to_string()),
        },
        public,
        private: dr.variables,
        definitions: dr.definitions,
        constraints: dr.constraints,
        hypotheses: opts.hypotheses.clone(),
        soundness_spec: opts.soundness_spec.clone(),
        ..CircuitIR::default()
    })
}

/// The Phase B proof target: [`circuits::BooleanBit`] over the Pallas base
/// field, with its canonical name and soundness spec. The committed corpus
/// artifact `corpus/circuits/ragu-boolean.json` is exactly this IR (a test
/// enforces it), and `lean/ZkGadgets/RaguBoolean.lean` proves it.
pub fn boolean_bit_ir() -> Result<CircuitIR, FrontendError> {
    extract_circuit::<ragu_pasta::Fp, _>(
        &circuits::BooleanBit,
        &ExtractOptions {
            name: "ragu-boolean".to_string(),
            soundness_spec: Some("out0 = 0 ∨ out0 = 1".to_string()),
            hypotheses: vec![],
            source: "frontend-ragu::circuits::BooleanBit (ragu_primitives::Boolean::alloc)"
                .to_string(),
        },
    )
}

// ─── Frontend impl ───────────────────────────────────────────────────────────

/// [`Frontend`] adapter around [`extract_circuit`] for a fixed circuit value.
///
/// The circuit is data of the frontend rather than of the config because a
/// ragu circuit is an arbitrary Rust value, not a file path; the config
/// carries the claim-side inputs (name, spec, hypotheses).
pub struct RaguFrontend<F, C> {
    circuit: C,
    _marker: PhantomData<F>,
}

impl<F, C> RaguFrontend<F, C>
where
    F: PrimeField + FromUniformBytes<64>,
    C: Circuit<F>,
{
    pub fn new(circuit: C) -> Self {
        RaguFrontend {
            circuit,
            _marker: PhantomData,
        }
    }
}

impl<F, C> Frontend for RaguFrontend<F, C>
where
    F: PrimeField + FromUniformBytes<64>,
    C: Circuit<F>,
{
    type Config = ExtractOptions;

    fn name(&self) -> &str {
        "ragu"
    }

    fn version(&self) -> &str {
        env!("CARGO_PKG_VERSION")
    }

    fn extract(&self, cfg: &ExtractOptions) -> Result<CircuitIR, FrontendError> {
        extract_circuit(&self.circuit, cfg)
    }
}

#[cfg(test)]
mod tests;
