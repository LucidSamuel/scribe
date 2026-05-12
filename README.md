# scribe

generates lean 4 proof scaffolds from zk constraint systems and drives proof completion with an llm feedback loop.

v1 verifies one gadget (8-bit range check) by hand. the tool then closes a second gadget's proof autonomously.

## what it does

1. **gadget-ir** — a minimal IR for polynomial constraints over a prime field. no framework dependency.
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

`lake build` will report `sorry` warnings — this is expected. the proof is filled in manually.

### emit a scaffold

```
cargo run -p lean-emit -- examples/range-check/gadget.toml
```

### proof loop (not yet implemented)

```
cargo run -p proof-pilot -- lean/ZkGadgets/RangeCheck.lean
```

## git hooks

reject commits that add `sorry`, `axiom`, or `native_decide` to lean files:

```
git config core.hooksPath .githooks
```

## project structure

```
crates/
  gadget-ir/       constraint system IR + TOML deserialization
  lean-emit/       IR → Lean 4 scaffold
  proof-pilot/     LLM proof loop (skeleton)
lean/
  ZkGadgets/
    Field.lean     field helper lemmas (stubs)
    RangeCheck.lean  8-bit range check theorem (sorry)
examples/
  range-check/     gadget.toml for the 8-bit range check
docs/
  architecture.md  data flow + crate descriptions
  why.md           motivation
```

## license

MIT
