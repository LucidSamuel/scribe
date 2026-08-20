# Binding inventory — do our own proofs prove our own statements?

2026-08-18, run with `scribe check --record` (the kernel-checked binding probe
from Phase D4) across every IR-backed gadget in `examples/` and its committed
proof in `lean/ZkGadgets/`. Re-run 2026-08-20 under the rustc 1.97.1 /
post-Phase-B tree: identical result, cache records refreshed against the
current proof-environment fingerprint. The probe demands that the committed theorem's type
be **definitionally equal** to the statement regenerated from the gadget's IR
(`lean_emit::soundness_statement`), then re-audits its axioms — "builds green"
is not accepted as evidence of anything.

## The number

**3 of 5 committed proofs bind. 2 do not.** Both failures are proofs of
*plausibly-equivalent restatements* whose equivalence to the IR statement was
never checked by anything — which is precisely where soundness bugs live, and
precisely the gap the binding probe exists to close. This finding is scribe's
own thesis firing on scribe's own repo, on its showpiece gadget.

| gadget | committed proof | binds? | fingerprint |
|---|---|---|---|
| range-check | `RangeCheck.lean` | **✗** | — |
| conditional-select | `ConditionalSelect.lean` | **✗** | — |
| poseidon-sbox | `PoseidonSbox.lean` | ✓ | `a814c13d88d3…` |
| nonzero-check | `NonzeroCheck.lean` | ✓ | `a03c1cff39b5…` |
| edwards-addition | `EdwardsAddition.lean` | ✓ | `737c4bf784e0…` |

Notably, Edwards addition — the proof that required human-guided algebraic
decomposition, and therefore the prior suspect for restatement drift — binds
exactly. The two that drifted are the *simple* gadgets, where a restatement
looks harmless enough that nobody re-checks it.

## The two failures, precisely

They are not the same severity, and the precise version matters more than the
alarming one. Neither proof is *wrong*; in both cases the theorem proved is
plausibly equivalent to the IR statement. The defect is that the equivalence
was asserted by resemblance, never established by anything.

### range-check — structural restatement (higher risk)

IR statement: 9 flat witnesses `x b0 … b7`, eight individual boolean
constraints, one flat weighted decomposition sum.
Committed theorem: `(bits : Fin 8 → ZMod p)` with `∀ i, bits i * (bits i - 1) = 0`
and `∑ i, bits i * 2 ^ (i : ℕ) = x`.

Kernel verdict: `Type mismatch` — an indexed function with quantified
constraints and a `Finset.sum` is a different object from eight wires and a
flat sum. The equivalence is a real lemma (index bookkeeping, sum unfolding)
that exists nowhere. This is the gadget `scribe demo --verify` runs and
`why.md` cites.

### conditional-select — ring-equal restatement (lower risk, still unverified)

| | IR statement | committed theorem |
|---|---|---|
| boolean | `b * b - b = 0` | `b * (b - 1) = 0` |
| select | `b * x + y - b * y - z = 0` | `b * x + (1 - b) * y = z` |

Kernel verdict: `Type mismatch`. Both pairs are equal by `ring` — but ring
equality is a proof obligation, not a definitional one, and the kernel is
right to refuse it: "obviously equivalent by algebra" is an assumption until
someone discharges it, and the binding probe's whole job is refusing to let
assumptions stand in for kernel checks.

## Remediation (not done here — deliberate)

For each non-binding gadget, write a **bridge theorem** in the committed file:
the IR-shaped statement, proven from the existing theorem plus the (small, in
conditional-select's case `linear_combination`-sized; in range-check's case a
genuine indexing lemma) equivalence argument. The bridge *is* the missing
equivalence proof, kernel-checked, and once it exists the binding probe
accepts the file. Do not weaken the probe to accept ring-equal statements —
the strictness is the product.

Left undone so the finding stays visible while Phases B/C are in flight, and
because re-proving into `lean/ZkGadgets/` while Phase B writes there invites
collisions.

## Positive-path evidence for fresh clones

The three binding gadgets double as the committed positive-path regression for
`bind_and_audit`: from a fresh clone,

```sh
scribe check --gadget examples/poseidon-sbox/gadget.toml --no-elab \
             --record lean/ZkGadgets/PoseidonSbox.lean
```

must succeed (and does), so the binding oracle is demonstrated to *accept*
genuine evidence, not merely reject everything — an oracle that rejects
everything has perfect negative discrimination and is useless.

## Guarding the binding oracle itself

`soundness_statement` mirrors `emit_lean` by construction, which is parallel
maintenance and will drift. A property test now pins them: for every gadget in
`examples/` (plus a definition-bearing synthetic), the token stream of
`soundness_statement(ir)` must equal the theorem statement `emit_lean(ir)`
emits, and `refutation_statement(ir, p)` likewise against `emit_refutation`.
See `statements_match_emitted_theorems_for_every_gadget` in
`crates/lean-emit/src/lib.rs`.
