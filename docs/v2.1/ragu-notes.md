# ragu extraction notes (Phase B)

What frontend-ragu learned about ragu's driver API while building the
structure-only extraction driver. The next ecosystem adapter should read this
first; so should anyone re-pinning the ragu revision.

## Pinned revision

`fc61822cf8c248d36b950c89817bf170d533a7f3` — `tachyon-zcash/ragu` `origin/main`
as of 2026-08-16 ("Merge pull request #835 from TalDerei/fuzz-oracle-correctness"),
the same revision Phase C's red-team audit used. Recorded in three places that
are cross-checked by tests: `frontend_ragu::RAGU_REV`, the `rev =` pins in
`crates/frontend-ragu/Cargo.toml`, and the `provenance.source_rev` of every
extracted IR.

Do **not** trust a local `~/ragu` checkout: at the time of writing it sat on a
docs branch whose merge-base was ~78 changed files behind `origin/main`. The
git-pinned dependency builds from the recorded rev regardless of local state.

Ragu's MSRV at this rev is **rustc 1.97** (edition 2024), which forced the
scribe workspace toolchain bump from 1.90.0 to 1.97.1 in `rust-toolchain.toml`.

## Driver call → IR mapping

| driver call | IR effect |
|---|---|
| `DriverTypes::gate()` | 4 fresh variables `a,b,c,d`; constraints `g{i}_mul: a·b − c = 0` **and** `g{i}_aux: c·d = 0` |
| `Driver::mul()` | delegates to `gate()`, discards the `Extra` token — the `d` variable and its `c·d = 0` constraint stay |
| `Driver::add(lc)` | a `Definition` (`v{id}`, linear form over existing ids); **no** constraint |
| `Driver::constant(v)` | default impl routes through `add`: definition `v{id} := v·one` |
| `Driver::enforce_zero(lc)` | constraint `lc{n}: Σ terms = 0` |
| `DriverTypes::assign_extra(tok)` | returns the already-allocated `d` id; no new variable, no new constraint |
| `Driver::ONE` | reserved id 0, name `one` |

Orchestration (replicated from `ragu_circuits::raw::orchestrate`, which is
`pub(crate)` and therefore had to be mirrored, not called):

1. **SYSTEM gate** (gate 0). Its `D` wire *is* the `one` wire — ragu assigns
   `d₀ = 1` at trace assembly and `Driver::ONE` refers to it by convention —
   so `g0_aux` reads `c·one = 0`. (`ragu_circuits::metrics::Counter` does not
   bother identifying the two; for counting it is irrelevant. For a soundness
   statement it is not: they are the same wire in `s(X,Y)`.)
2. `Circuit::witness()` — the body.
3. Each written output wire `w` is bound to a fresh **public** variable:
   `out{i}_bind: w − out{i} = 0`. In ragu the driver-side constraint is just
   `enforce_zero(lc.add(w))`; the `k(Y)` coefficient it is checked against is
   implicit in the constraint's `Y`-position. The IR makes that explicit:
   `out{i}` *is* the `k(Y)` coefficient the verifier supplies.
4. **ONE constraint**: `one_is_1: one − 1 = 0` (the verifier fixes `k(0) = 1`).

## Visibility mapping (public vs private)

- `Circuit::Output` is documented as "the circuit's public instance,
  serialized into the k(Y) instance polynomial that the verifier checks", and
  `Circuit::instance()` produces it **without witness data**.
- Extraction runs `instance()` on a scratch driver purely to measure the
  verifier-visible arity (number of `Element`s the output gadget writes),
  then runs `witness()` for the constraint set, writes its output gadget, and
  asserts (a) the two arities agree and (b) every written wire id was
  allocated or defined by the witness run. Violations are
  `FrontendError::SelfValidation` — extraction refuses to emit IR.
- `CircuitIR.public` is exactly the `out{i}` binding variables (the instance
  vector); every driver-allocated wire, including `one`, is private. Nothing
  defaults into `private` by omission.
- Caveat: `instance()` may itself allocate gates (e.g. `Element::alloc` in
  ragu's own fixtures), so it runs on a throwaway driver whose gates and
  constraints are discarded — only the written arity is kept.

## Count reconciliation with `ragu_circuits::metrics`

`metrics` (exposed as `testing::synthesis_counts` behind the `test-utils`
feature — the module itself is private) counts:

- `num_gates` = `gate()` calls, including the SYSTEM gate;
- `num_constraints` = `enforce_zero()` calls **only** — including the
  public-output bindings and the ONE constraint, excluding the per-gate
  `a·b = c` / `c·d = 0` pair.

So the extractor tracks the same two numbers and the invariant is
`ir.constraints.len() == 2·num_gates + num_constraints`. Every
`extract_circuit` call re-runs `synthesis_counts` on the same circuit and
hard-fails on disagreement (locked decision 6). This caught nothing yet — but
the `FlakyCircuit` test proves it *would*: a circuit that violates ragu's
"constraints are deterministic" contract is refused.

## Things that surprised us

- **`Extra` / the D wire.** `gate()` returns an opaque `Extra` token for `D`;
  `assign_extra` redeems it (allocators like `Standard` pool donated tokens to
  pack two allocations into one gate). The extractor allocates `d` and its
  `c·d = 0` constraint at gate time, so `Extra = usize` (the id) and
  `assign_extra` is the identity — token redemption can never change the
  constraint set, which is exactly the semantics ragu documents.
- **Ragu already has a Lean extraction driver**: `qa/crates/lean_extraction`
  ("Extracts Ragu circuit instances for formal verification in Lean"), per-
  gadget instance files included. Its driver *deliberately under-models the D
  wire* — `Extra = ()`, no fourth wire, no `C·D = 0` — documented as a shim to
  keep old traces stable. That is precisely the weakening our brief flags as
  the highest-risk mistake; scribe's extractor models it fully. Worth an
  upstream conversation (ask before filing anything external).
- **`LinearExpression` gain discipline.** Expressions cannot be scaled
  directly; a "gain" multiplies every *subsequently added* term. The recorder
  must apply `coeff * gain` per term at add time, not scale at the end.
  Duplicate wires in one LC are legal (`lc.add(a).sub(a)`) and must be summed.
- **`Maybe`/`Empty` really is free.** With `MaybeKind = Empty` every witness
  closure is statically dead code (`Empty::take()` is a compile-time panic in
  a `const` block, so calling it anywhere fails the build). `Bound<'dr, D, K>`
  works unchanged; gadgets carry `Empty` where witness data would live.
  Nothing needed special-casing.
- **Coefficients are field elements, rendered as signed decimals.** `Coeff`'s
  `One/Two/NegativeOne` variants map directly; `Arbitrary(f)` renders as the
  small negative representative when `f > p/2` (so `-1`, not a 77-digit
  constant). The emitted theorem is generic over `p`, so circuits whose
  constants only make sense at the concrete modulus would need a `p = ...`
  hypothesis; none of the extracted circuits hit this.
- **Modulus strings.** `PrimeField::MODULUS` is hex with `0x` prefix;
  `to_repr` is little-endian for the pasta fields. Both assumptions are
  pinned by a test against the known Pallas decimal modulus.

## The tachyon smoke test — reported, not worked around

The brief's premise ("frontend-ragu reaches every ragu **and tachyon**
circuit through the Driver trait") is true in principle and void in practice
at every available tachyon revision:

- `zcash_tachyon` (both `origin/main` 5d6977cb and the local working branch)
  contains **no `ragu_circuits::Circuit` implementations and no
  Driver-generic code at all**. Its in-circuit side is written against ragu's
  `mock` facade (`ragu::Application` / `Step` / `StepCtx` — native `Fp`
  functions like `enforce_poly_query`), pending the real-circuit migration —
  the same `stamp/proof/*` rewrite that put tachyon specs out of scope.
- Tachyon also pins **different, older ragu sources** (`origin/main` pins
  `tachyon-zcash/ragu @ 2f926fdc`; the local branch a `turbocrime/ragu` fork
  @ `eda37343`), which are different crate identities: a `Driver` impl
  against `fc61822c` cannot serve circuits compiled against those pins even
  if they existed.

So there is nothing to smoke-test yet: not an API mismatch in the extractor,
but an upstream state of the world. The honest statement of readiness is:
`extract_circuit` is generic over any `C: Circuit<F>`, and the day tachyon
gains real ragu circuits on a compatible pin, they extract with zero new
code. Until then the breadth evidence is the extracted shapes in
`crates/frontend-ragu/src/circuits.rs` (boolean gadget, definition-bearing
sum-then-square, parameterized square chains).

## Decomposed-mode fallback (Phase A follow-up), measured

`lean-emit`'s decomposed mode falls back to the plain scaffold whenever
`definitions` is non-empty. `Driver::add` is ragu's free primitive, so any
circuit that touches `Element::add/sub/scale`, `Boolean::not`, `constant()`,
… carries definitions — of the three extracted shapes, one (SumThenSquare)
already trips it, and the ratio only rises with real gadget libraries
(poseidon is `add`-heavy). Measured and asserted in
`decomposed_mode_silently_disables_on_definition_bearing_ragu_ir`. Filed as a
Phase A follow-up; do not work around it in the frontend.

## What the oracle side pinned down (oracle-lean)

- Lean's three real states map onto `Outcome` with no collapsing:
  kernel-accepted proof → `Accept`; kernel-checked refutation → `Reject`;
  budget exhausted **or any infrastructure failure** → `Undetermined`.
- The corpus (`corpus/circuits/`) is self-contained: manifest + IR files,
  gadget names deliberately neutral so the theorem name leaks nothing to the
  model; only the manifest (which the model never sees) marks an instance
  negative.
- The committed `discrimination-report.json` is regenerated by the ignored
  `validate_lean_oracle_against_corpus` test (live LLM + kernel); a
  non-ignored test pins the committed report to the current corpus shape and
  fails the build on any escape.
