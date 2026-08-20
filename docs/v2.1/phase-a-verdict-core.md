# Phase A — Verdict core

**Owns:** `crates/scribe-core/*` (new), `crates/circuit-ir/*` (new),
`crates/scribe-frontend/*` (new), `crates/frontend-toml/*` (new),
`crates/gadget-ir/src/lib.rs` (shim only), `crates/lean-emit/*`,
root `Cargo.toml`, `schema/circuit-ir-v1.json` (new).

**Blocks:** everything. Land green before B/C/D start.

## Why

Scribe's differentiated machinery — `#audit_axioms`, C1–C3, `scribe refute`, the
negative corpus — is domain-independent in concept and Lean-locked in code. Two
symptoms:

- `scribe refute` and `scribe judge` take *"Gadget IR file (TOML)"*, so the
  verdict engine reaches only hand-written toy gadgets.
- `proof-pilot` hardcodes lake-build-and-parse-Lean-errors, so no other
  acceptance procedure can exist.

Phase A extracts the concept from the implementation. After it, "Lean proves a
circuit" is one instance of a general shape, and a differential-equivalence check
over prover implementations (Phase C) is another.

## Scope

### 1. `crates/scribe-core` — the four traits

Signatures are in `roadmap-v2.1.md`'s architecture contract. Implement them
exactly; they are the contract B and C are being written against in parallel.

Design notes that matter:

- **`Claim::Subject` is an associated type, not a shared struct.** This is the
  whole reason the core generalizes. A circuit claim's subject is a `CircuitIR`;
  an equivalence claim's subject is `(reference, candidate, seeds)`. Do not
  invent a universal subject enum — that would drag every domain's payload into
  core and reproduce the problem we are fixing.
- **`Outcome` is three-valued.** `Accept` / `Reject` / `Undetermined`. Budget
  exhaustion is not rejection, and conflating them is how a tool starts lying.
- **`Corpus` carries `positives()` too.** An oracle that rejects everything has
  perfect negative discrimination and is useless. Both directions are measured.

### 2. The unconstructible `Verdict` (locked decision 2)

```rust
pub enum Discrimination {
    Measured(DiscriminationReport),
    Unmeasured { reason: UnmeasuredReason },
}

/// Closed set. A free-form String readmits `reason: "TODO"`, which is exactly
/// the erosion this decision exists to block.
pub enum UnmeasuredReason { NoCorpusDefined, CorpusEmpty, ValidationSkipped }

pub struct Verdict { /* private */ }

impl Verdict {
    pub fn new(outcome: Outcome, discrimination: Discrimination) -> Self;
}
```

All fields private, one constructor, no `Default`, no `From<Outcome>`, no
builder that defaults the discrimination.

The invariant is **not** "every Verdict carries a measurement" — `Unmeasured`
has to be legal or nothing bootstraps. It is: **no Verdict exists without an
explicit statement of measurement status.** If someone can produce a `Verdict`
without stating whether the oracle was measured, this phase has failed.

Ship a **compile-fail test** (`trybuild` or equivalent) proving it. That test is
the executable form of the product thesis and it should be the first thing a new
contributor reads.

An oracle with no corpus reports `Discrimination::Unmeasured { reason }`. That
is a legal state — it must be, or nothing could bootstrap — but the CLI renders
it as prominently as the outcome. `ACCEPT (oracle unmeasured)` is the honest
rendering, and it should look uncomfortable.

### 3. `validate(oracle, corpus) -> DiscriminationReport`

Runs the oracle over every corpus instance. Report caught/total in both
directions and the ids of any **escapes** — negatives the oracle wrongly
accepted.

An escape is the loudest signal the system can produce: the oracle accepted
something known to be wrong, so every verdict it has ever issued is suspect. Do
not bury it in a summary line.

### 4. `crates/circuit-ir` — demoted from spine to plugin subject

Grown from `gadget-ir`. Keep `Term` exactly as it is (`coeff` decimal string,
`vars: Vec<usize>` as a monomial) — it already expresses what ragu needs. Add:

```rust
pub struct CircuitIR {
    pub ir_version: String,
    pub name: String,
    pub modulus: String,
    pub provenance: Provenance,
    pub public: Vec<Variable>,      // was: flat `witnesses`
    pub private: Vec<Variable>,     // was: flat `witnesses`
    pub definitions: Vec<Definition>,
    pub constraints: Vec<Constraint>,
    pub hypotheses: Vec<Hypothesis>,
    pub soundness_spec: Option<String>,
}

pub struct Provenance { pub frontend: String, pub frontend_version: String,
                        pub source: String, pub source_rev: Option<String> }
pub struct Definition { pub id: usize, pub name: String, pub terms: Vec<Term> }  // LINEAR only
pub struct SourceSpan { pub file: String, pub line: u32, pub label: Option<String> }
```

and `Constraint` gains `origin: Option<SourceSpan>`.

- `public`/`private` is a **correctness fix**, not ergonomics. A soundness
  theorem is meaningless without knowing what the verifier sees; today the
  distinction lives implicitly in a spec string.
- `definitions` carry an `id` in the **same id space as variables**, because
  `Term.vars` holds ids — a definition without one could never be referenced
  from a constraint, defeating its purpose.
- `definitions` exist because ragu's `Driver::add` is free unlimited-fan-in.
  A virtual wire can combine hundreds of others; inlining it into every
  constraint that mentions it explodes the emitted Lean. Emit as `let` bindings.
- `origin` powers Phase D's source-cited diagnostics.

Accept `witnesses` as a deprecated alias deserializing into `private`, so the
existing `examples/*/gadget.toml` keep working and the snapshot tests stay honest.

### 5. `crates/scribe-frontend`, `crates/frontend-toml`

```rust
pub trait Frontend {
    type Config;
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn extract(&self, cfg: &Self::Config) -> Result<CircuitIR, FrontendError>;
}
```

Keep it this small. `frontend-toml` ports today's TOML path and is the
regression anchor: byte-identical Lean for every gadget in `examples/`.

### 6. `lean-emit` updated + schema + shim

`emit_lean`, `emit_lean_decomposed`, `emit_refutation`, `refutation_prime` take
`&CircuitIR`. Emit `definitions` as `let` bindings ahead of constraint
hypotheses; emit `public` and `private` as distinct binder groups.

Commit `schema/circuit-ir-v1.json` with:

- a round-trip test (`CircuitIR → JSON → CircuitIR` is identity),
- **`ir_version` enforcement in `from_json`** — reject unknown majors at parse
  time, not by convention. Locked decision 6 is worthless if the field is
  decorative,
- **instance validation against the schema**, not just a comparison of top-level
  property names. Add negative tests: an invalid `ir_version`, and a malformed
  `SourceSpan`. Phase D's caching and G5's third-party adapters both depend on
  "validates against the schema" meaning something.

Make `crates/gadget-ir/src/lib.rs` a `#[deprecated]` re-export shim; do not
delete it. Its `Cargo.toml` needs a dependency swap too — that is in scope.

## Acceptance

- `cargo test --workspace` green, test count preserved or higher.
- Compile-fail tests prove `Verdict` is unconstructible without an explicit
  `Discrimination`, and that `Unmeasured` cannot take a free-form reason.
- `validate()` reports escapes distinctly from ordinary failures.
- `frontend-toml` produces byte-identical Lean to today for every `examples/`
  gadget (snapshot test per gadget).
- JSON round-trip passes; schema committed.
- `cd lean && lake build` exits 0 with no warnings.
- `scribe refute` / `scribe judge` still work on `examples/range-check/gadget.toml`.

## Pitfalls

- **Do not invent a universal `Subject` type.** Associated type or the design
  fails.
- **Do not let `CircuitIR` concepts leak into `scribe-core`.** The gate is on
  **types, dependencies, and API names** — core must compile with `circuit-ir`
  absent from its dependency list, and no public type or method may name a
  circuit concept. Doc comments *may* use circuits illustratively, but only if
  at least one non-circuit domain appears alongside (e.g. "a circuit's soundness,
  or two implementations' equivalence"). A doc block that presupposes circuits is
  a layering smell even when the types are clean.
- **Do not give `Verdict` a convenience constructor.** Every escape hatch added
  here will be used, and the thesis dies quietly.
- **Do not touch `crates/halva-bridge`** (locked decision 8).
- **Do not restructure `soundness_spec`.** Raw Lean string in v2.1.

## Agent prompt

```
Read roadmap-v2.1.md and docs/v2.1/README.md, then docs/v2.1/phase-a-verdict-core.md.

Implement Phase A of the scribe v2.1 roadmap: the verdict core.

You own exactly these paths, and must not edit any other file:
  crates/scribe-core/*        (new)
  crates/circuit-ir/*         (new)
  crates/scribe-frontend/*    (new)
  crates/frontend-toml/*      (new)
  crates/gadget-ir/src/lib.rs (deprecation shim only)
  crates/lean-emit/*
  Cargo.toml                  (workspace members)
  schema/circuit-ir-v1.json   (new)

Do NOT edit crates/halva-bridge — it is frozen (locked decision 8).

The central requirement: scribe-core must be domain-independent. Claim::Subject
is an ASSOCIATED TYPE, not a shared enum — a circuit claim's subject is a
CircuitIR, an equivalence claim's subject is (reference, candidate, seeds).
scribe-core must compile with circuit-ir removed from its dependencies. If core
mentions constraints, fields, or polynomials anywhere, the layering is wrong.

The second central requirement: Verdict has private fields and exactly one
constructor, taking a Discrimination — Measured(DiscriminationReport) or
Unmeasured with a reason from the closed UnmeasuredReason enum. No Default, no
From<Outcome>, no builder that defaults it, no free-form unmeasured reason.
Ship compile-fail tests (trybuild) proving a Verdict cannot be constructed
without an explicit measurement status. This is the product thesis expressed
as a type — do not add convenience escape hatches.

Phases B and C are being written against these signatures in parallel, so treat
the trait definitions in roadmap-v2.1.md as a contract.

Before reporting done, run in this order and paste results:
  cargo fmt --all
  cargo clippy --workspace --all-targets -- -D warnings
  cargo test --workspace
  cd lean && lake build

Report: what you built (2 sentences), test count delta, confirmation that
scribe-core compiles without circuit-ir, and anything that contradicted the brief.
```
