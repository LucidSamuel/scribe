# scribe

```
               _ _
  ___  ___ _ __(_) |__   ___
 / __|/ __| '__| | '_ \ / _ \
 \__ \ (__| |  | | |_) |  __/
 |___/\___|_|  |_|_.__/ \___|
```

generates lean 4 proof scaffolds from zk constraint systems and drives proof completion with an llm feedback loop.

## what it does

1. **gadget-ir** — a minimal IR for polynomial constraints over a prime field.
2. **lean-emit** — reads the IR, emits a Lean 4 file with the theorem statement and `sorry`.
3. **proof-pilot** — drives the `claude` CLI in a loop: edit proof → `lake build` → read errors → repeat. stops when the kernel accepts or budget is exhausted.

the lean kernel is the oracle. `lake build` returning 0 means the proof is valid. the llm cannot fake it without `sorry` or `axiom`, which are blocked by pre-commit hook and CI.

## quickstart

### rust

```
cargo check --workspace
cargo test --workspace
```

### lean

requires [elan](https://github.com/leanprover/elan) (lean version manager).

```
# install elan (mac)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

cd lean
lake update
lake build
```

`lake build` should exit 0 with no warnings. both gadget proofs are complete.

### emit a scaffold

```
cargo run -p lean-emit -- examples/poseidon-sbox/gadget.toml
```

### proof loop

```
cargo run -p proof-pilot -- lean/ZkGadgets/AutoProof.lean \
  --lake-dir lean \
  --max-iters 10 \
  --transcript transcript.log
```

proof-pilot calls `claude -p` with the file + build errors, extracts the proof from the response, patches the file, rebuilds, and repeats until `lake build` passes clean or the budget is exhausted. the `--transcript` flag logs every iteration for debugging.

## gadgets

| gadget | constraints | soundness claim |
|---|---|---|
| 8-bit range check | 9 (8 boolean + decomposition) | `∃ k : Fin 256, k.val = x` |
| conditional select | 2 (boolean + mux) | `(b = 0 ∧ z = y) ∨ (b = 1 ∧ z = x)` |
| poseidon s-box | 3 (squaring chain) | `y = x ^ 5` |
| non-zero check | 1 (inverse) | `x ≠ 0` |
| edwards addition | 2 (baby jubjub add) | output point on curve |

## git hooks

reject commits that add `sorry`, `axiom`, or `native_decide` to lean files:

```
git config core.hooksPath .githooks
```

## project structure

```
crates/
  gadget-ir/       constraint system IR + TOML deserialization
  lean-emit/       IR → Lean 4 scaffold with sorry
  proof-pilot/     LLM proof loop (patcher, lean runner, session logging)
lean/
  ZkGadgets/
    Field.lean           field helper lemmas (proven)
    RangeCheck.lean      8-bit range check soundness (proven)
    ConditionalSelect.lean  conditional select soundness (proven)
examples/
  range-check/           8-bit range check (9 witnesses, 9 constraints)
  conditional-select/    conditional select (4 witnesses, 2 constraints)
  poseidon-sbox/         poseidon s-box x^5 (4 witnesses, 3 constraints)
  nonzero-check/         field inverse (2 witnesses, 1 constraint)
  edwards-addition/      baby jubjub point addition (6 witnesses, 2 constraints)
docs/
  architecture.md  data flow + crate descriptions
  why.md           motivation
```

## license

MIT
