# Phase B — Instance 1: circuits via Lean

**Owns:** `crates/frontend-ragu/*` (new), `crates/oracle-lean/*` (new),
`corpus/circuits/*` (new), `docs/v2.1/ragu-notes.md` (new).

**Depends on:** Phase A green. **Runs in the same cycle as Phase C** — together
they determine whether `scribe-core` is real (locked decision 3).

## Why ragu is the cheap ecosystem

Ragu already built the extraction seam.

`ragu_core::drivers::Driver` is the constraint-authoring API. Circuits never talk
to a prover — they talk to a driver:

- `DriverTypes::gate(values)` allocates `(A, B, C)` with `A · B = C`, **and also
  imposes `C · D = 0`** on an auxiliary `D` wire.
- `Driver::add(lc)` creates a virtual wire from a linear combination. Unlimited
  fan-in, free, emits **no** constraint.
- `Driver::enforce_zero(lc)` records a constraint.
- `Driver::mul(values)` wraps `gate` and drops the `D` wire.

Three facts make extraction straightforward:

1. **Every circuit is generic over the driver** — `ragu_circuits/src/lib.rs`:
   `fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = F>>(&self, dr: &mut D, ...)`.
   One driver reaches every ragu *and* tachyon circuit, no per-circuit adapter.
2. **Structure-only drivers are supported.** `MaybeKind = Empty`;
   `ragu_circuits::metrics` already "simulates circuit execution without
   computing assignment values", with `phantom.rs` / `trace.rs` as precedents.
3. **The constraint set is documented as witness-independent.** The `Circuit`
   trait states implementations must emit constraints deterministically from
   types, constants, and lengths — witness values "may determine witness
   generation and auxiliary data, but not which constraints are emitted." That
   is a trait-level guarantee a structure-only driver sees the complete
   constraint set.

## Scope

### 1. `frontend-ragu` — the extraction driver

`DriverTypes` + `Driver<'dr>` with `MaybeKind = Empty`, recording:

| driver call | IR effect |
|---|---|
| `gate()` | fresh `A`,`B`,`C`,`D`; constraints `A·B − C = 0` **and** `C·D = 0` |
| `add(lc)` | a `Definition` (linear form); **no** constraint |
| `enforce_zero(lc)` | a `Constraint` |
| `constant(v)` | a definition over the fixed `ONE` wire |

**Do not drop `C · D = 0`.** `Driver::mul` hides the `D` wire, so it is the
natural thing to miss, and omitting it yields an IR *weaker* than the circuit —
which makes any soundness proof against it prove the wrong thing. This is the
highest-risk detail in the phase.

`add` maps to `Definition`, never to inlining. `Definition` carries an `id` in
the same id space as variables — `Term.vars` holds ids, so definitions must be
referenceable from constraints.

### 1b. Visibility extraction — do not skip this

Constraint extraction alone puts every wire in `CircuitIR.private`, which makes
the `public`/`private` split dead weight and the emitted soundness theorem
subtly wrong: a soundness statement is meaningless without knowing what the
verifier actually sees.

Ragu gives you the hook. `Circuit::Output` is documented as "the circuit's public
instance, serialized into the $k(Y)$ instance polynomial that the verifier
checks", and `Circuit::instance()` returns exactly that `Bound<'dr, D, Output>`
*without* requiring witness data. So:

- run `instance()` to determine the verifier-visible surface → `public`,
- run `witness()` for the full constraint set → everything else → `private`,
- assert the public wires are a subset of what `witness()` allocated.

Document the mapping you settle on in `ragu-notes.md`. Getting this wrong is a
silent correctness bug, not a loud failure.

### 2. Self-validation against `metrics` (locked decision 6)

Run the same circuit through `ragu_circuits::metrics` and compare gate and
constraint counts. Disagreement is a hard error.

Cheap to build, and the most valuable test in the phase: an independent oracle
from the host framework itself, in exactly the spirit of the corpus one layer up.

### 3. `crates/oracle-lean` — `Oracle<CircuitClaim>`

Wrap the existing lake-build + `#audit_axioms` check from `proof-pilot` behind
the Phase A trait. Behavior should not change; only its shape.

Map Lean's three real states onto `Outcome` honestly: kernel accepted →
`Accept`, kernel-checked refutation found → `Reject`, budget exhausted →
`Undetermined`. Do not collapse the third into the second.

### 4. `corpus/circuits` — the negative corpus, promoted

`benchmark/suite.toml`'s five `kind = "negative"` gadgets become a real
`Corpus<CircuitClaim>`: versioned, with positives as well as negatives, and an
id per instance so escapes are reportable.

Run `validate(LeanOracle, CircuitCorpus)` and record the `DiscriminationReport`.
All five negatives must be caught. If any escapes, that is a finding — report it
loudly rather than tuning the corpus until it passes.

### 5. First proof target

Extract one `ragu_primitives` gadget (`boolean.rs` suggested — small, stable,
semantically obvious), emit Lean, drive to a kernel-accepted proof.

Do **not** write specs for tachyon relations. `stamp/proof/*` is being rewritten
upstream; extraction is churn-safe but specs would be wasted. A tachyon
extraction *smoke test* (does it extract without error) is in scope and valuable.

### 6. `docs/v2.1/ragu-notes.md`

Record what you learned about the driver API: which `LinearExpression` methods
you needed, how `Bound`/`DriverValue` behaved under `Empty`, anything surprising.
The next ecosystem adapter reads this.

## Acceptance

- A `ragu_primitives` gadget extracts to `CircuitIR`, with `public` populated
  from `Circuit::instance()` rather than everything landing in `private`.
- Extracted gate/constraint counts match `ragu_circuits::metrics` exactly, asserted
  by a test.
- One kernel-accepted soundness proof of an extracted ragu gadget, `#audit_axioms`
  showing only `propext` / `Classical.choice` / `Quot.sound`.
- `validate(LeanOracle, CircuitCorpus)` catches 5/5 negatives, and the report is
  committed.
- ~~At least one tachyon circuit extracts without error (smoke test).~~
  **Waived 2026-08-20** — not skipped, found impossible: tachyon contains no
  `Circuit`/`Driver`-generic code at any available revision (its in-circuit
  side targets ragu's mock PCD facade, `StepCtx`, over native `Fp`), so there
  is nothing for a `Driver` implementation to extract. Investigation recorded
  in [`ragu-notes.md`](ragu-notes.md). Replacement criterion, already met:
  `extract_circuit` is generic over any `C: Circuit<F>`, so tachyon works with
  zero new code the day it adopts real ragu circuits.
- No special-casing added to `scribe-core` for this domain.

## Pitfalls

- **`C · D = 0`.** Named twice on purpose.
- **Pin the ragu revision** in `Provenance` and in `ragu-notes.md`. Ragu moves
  fast; an extractor validated against an unrecorded revision is not reproducible.
- **No ragu vocabulary in the IR** — no `routine`, `Bound`, `s(X,Y)`, floor
  planning (locked decision 7).
- **`ragu_pcd` is out of scope** (locked decision 9). If a circuit drags in the
  PCD layer, pick a different circuit.
- **If you need to change `scribe-core`, stop and report it.** A core change
  requested by one domain is a Phase A defect, and Phase C is watching the same
  contract.

## Agent prompt

```
Read roadmap-v2.1.md and docs/v2.1/README.md, then docs/v2.1/phase-b-instance-circuits.md.

Implement Phase B: the first instance of scribe's verdict core — circuit
soundness adjudicated by the Lean kernel, over circuits extracted from ragu.

You own exactly:
  crates/frontend-ragu/*   (new)
  crates/oracle-lean/*     (new)
  corpus/circuits/*        (new)
  docs/v2.1/ragu-notes.md  (new)

Phase A must be green. Phase C is being built in parallel against the same
scribe-core contract. If you find yourself needing to change scribe-core, STOP
and report it — that is a Phase A defect, not something to work around locally.

Approach: implement ragu's Driver trait with MaybeKind = Empty, recording
gates/definitions/constraints into a CircuitIR. Read ragu's
crates/ragu_core/src/drivers.rs and crates/ragu_circuits/src/metrics.rs first —
metrics.rs is a working precedent for a structure-only driver.

CRITICAL: gate() imposes TWO constraints, A·B = C and C·D = 0. Driver::mul hides
the D wire. Dropping C·D = 0 yields an IR weaker than the circuit and makes any
soundness proof against it meaningless. Validate your extraction by comparing
gate and constraint counts against ragu_circuits::metrics on the same circuit,
and fail hard on disagreement.

Also promote benchmark/suite.toml's five negative gadgets into a real
Corpus<CircuitClaim> and run validate(LeanOracle, corpus). All five must be
caught. If one escapes, report it loudly — do not tune the corpus until it passes.

Target one ragu_primitives gadget (boolean.rs suggested) through to a
kernel-accepted proof. Do NOT write specs for tachyon relations — that code is
being rewritten upstream. A tachyon extraction smoke test is in scope.

Before reporting done, run and paste:
  cargo fmt --all
  cargo clippy --workspace --all-targets -- -D warnings
  cargo test --workspace
  cd lean && lake build

Report: what you built, test count delta, the ragu revision you pinned, the
DiscriminationReport, and anything in ragu's driver API that did not match this
brief.
```
