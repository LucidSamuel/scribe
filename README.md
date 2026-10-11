<div align="center">

<pre>
               _ _
  ___  ___ _ __(_) |__   ___
 / __|/ __| '__| | '_ \ / _ \
 \__ \ (__| |  | | |_) |  __/
 |___/\___|_|  |_|_.__/ \___|
</pre>

### an LLM proof-completion loop for ZK circuit gadgets, with the Lean 4 kernel as the oracle

[![CI](https://img.shields.io/github/actions/workflow/status/LucidSamuel/scribe/ci.yml?branch=main&label=CI&logo=github)](https://github.com/LucidSamuel/scribe/actions/workflows/ci.yml)
[![Docker](https://img.shields.io/github/actions/workflow/status/LucidSamuel/scribe/docker.yml?branch=main&label=Docker&logo=docker)](https://github.com/LucidSamuel/scribe/actions/workflows/docker.yml)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE-MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4.30.0--rc2-1f425f.svg)](https://leanprover.github.io/)
[![Rust](https://img.shields.io/badge/Rust-stable-orange.svg?logo=rust)](https://www.rust-lang.org/)
[![proofs: kernel-checked](https://img.shields.io/badge/proofs-kernel--checked-success.svg)](#proven-gadgets)

[Getting Started](#getting-started) ·
[Usage](#usage) ·
[Proven Gadgets](#proven-gadgets) ·
[Architecture](docs/architecture.md) ·
[Why](docs/why.md)

</div>

---

## Background

Zero-knowledge circuits are notoriously hard to get right: a single under-constrained gate is a soundness bug that no amount of testing reliably catches. **scribe** turns the soundness of a ZK gadget into a theorem and proves it using a large language model to *write* the proof and the **Lean 4 kernel** to *check* it.

> [!IMPORTANT]
> The Lean kernel is the oracle, not the LLM. `proof-pilot` builds the Lake project and then compiles the exact target file. The real guarantee is an `#audit_axioms` gate compiled next to every theorem: it runs the kernel's own axiom tracking and **fails the build unless the proof's axiom set is a subset of `{propext, Classical.choice, Quot.sound}`**. So `sorry`, `admit`, `axiom`, or `native_decide` cannot survive — not even reached transitively through a dependency. Fast textual scans in `proof-pilot`, a pre-commit hook, and CI are a pre-filter; the axiom gate is the source of truth.

The main assurance mechanisms are:

- **Sound by construction.** Every proof in this repo is checked by the Lean 4 kernel, and an `#audit_axioms` gate next to each theorem runs the engine behind `#print axioms` at build time, rejecting anything that depends on more than the three standard axioms. That catches a transitive `sorryAx` (what `sorry`/`admit` elaborate to) or `native_decide`'s `ofReduceBool` reached through any dependency — which a textual grep cannot. See [`Audit.lean`](lean/ZkGadgets/Audit.lean).
- **Specs audited, not just proofs.** A kernel-checked proof of a meaningless statement proves nothing, so a dual-sided **verdict engine** probes the statements themselves at build time: `#audit_uses` / `#audit_requires` (C1) flag decorative or dropped hypotheses — written into a Lean file they fail the build; in the record/cache pipeline, *dropped* hypotheses are caught structurally by the kernel-checked binding probe (the statement regenerated from the IR carries every constraint hypothesis and must match definitionally), while `#audit_uses` runs as a reported, non-gating probe for *decorative* ones; `#audit_falsifiable` (C2) requires a kernel-checked refutation of the conclusion at a finite-model instantiation, killing vacuously-true specs; `#audit_satisfiable` (C3) requires a witness satisfying every constraint, killing impossible-antecedent specs. C2/C3 witnesses show that the tested constraints can hold and the conclusion can fail; C1 reports hypothesis use, which does not establish logical necessity or fidelity to the intended specification. `scribe refute` (C4) completes the dual side: an adversarial LLM loop attacks the spec itself, hunting for a kernel-checked counterexample — a checked counterexample refutes the precise claim, while surviving a bounded search remains inconclusive.
- **Automated.** An LLM drives a closed feedback loop, edit the proof, compile, read the errors (or structured LSP goal states), repeat until the kernel accepts or the budget runs out.
- **Real circuits.** `frontend-ragu` extracts Ragu constraints and checks its counts against the host framework; the resulting circuit claims can use the same verdict path as TOML inputs.

## How It Works

scribe's core represents claims, acceptance oracles, and versioned positive/negative corpora. Every verdict includes its discrimination status. The circuit path is:

1. **`frontend-toml` / `frontend-ragu`** extract constraints into **`circuit-ir`**.
2. **`lean-emit`** emits proof or refutation scaffolds with audit gates.
3. **`proof-pilot`** runs the bounded proof-editing loop; **`oracle-lean`** reports a proof, a counterexample, or an undetermined result.
4. **`scribe-cli`** exposes the workflow, artifact binding, cache and corpus commands.

A second adapter, **`oracle-differential`**, measures finite MSM comparisons; this evidence is not a universal equivalence proof. See [architecture](docs/architecture.md) for all crate boundaries.

## Getting Started

### Docker (fastest)

The published image bundles the Rust binaries, the Lean toolchain, and pre-cached Mathlib oleans, so there is no ~30-minute cold Mathlib build.

```sh
# five-minute demo: dry-run the range-check gadget proof (no API key needed)
docker run --rm ghcr.io/lucidsamuel/scribe:latest scribe demo

# judge a circuit claim (requires an API backend)
docker run --rm \
  -e ANTHROPIC_API_KEY="$ANTHROPIC_API_KEY" \
  -v "$(pwd)":/workspace \
  ghcr.io/lucidsamuel/scribe:latest \
  scribe judge --gadget /workspace/examples/range-check/gadget.toml --backend anthropic
```

See the [Docker](#docker) section for tags and local builds.

### From source

> [!NOTE]
> The Rust workspace builds with a stable toolchain. The Lean side requires [elan](https://github.com/leanprover/elan) (the Lean version manager); the pinned toolchain is `leanprover/lean4:v4.30.0-rc2`.

```sh
# Rust workspace
cargo check --workspace
cargo test  --workspace

# Lean proofs
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh   # install elan (mac/linux)
cd lean
lake exe cache get      # fetch pre-built Mathlib oleans
lake build              # should exit 0 with no warnings — every gadget proof is complete
```

> [!TIP]
> Running `scribe` or `proof-pilot` against a live model needs a backend. The default backend shells out to the `claude` CLI; pass `--backend openai|anthropic|...` plus `--api-key` / `--model` to use a hosted API instead. Run `scribe --help` or invoke `proof-pilot` without arguments for usage.

## Usage

### `scribe check`

Validate a TOML/JSON circuit claim, elaborate its statement, and look for bound
proof evidence. Static checks without evidence report UNDETERMINED, not SOUND.

```sh
scribe check --gadget examples/range-check/gadget.toml
scribe corpus validate --dry-run
```

### `scribe refute`

The adversarial half of the verdict engine (C4): instead of proving the spec, attack it.

```sh
scribe refute --gadget examples/range-check/gadget.toml \
  [--prime P]        # default: smallest prime satisfying the gadget's `p > N` bounds
  [--max-iters N]    # refutation attempts (default: 6)
  [--scaffold-only]  # emit the negated statement and stop
```

The gadget's soundness statement is emitted at a concrete small prime, **negated**, and an LLM refuter loop (system prompt `prompts/lean-refuter.md`) tries to prove the negation — i.e. exhibit witness values that satisfy every constraint while violating the spec. A kernel-accepted refutation is exactly as trustworthy as a kernel-accepted proof, and carries its own `#audit_axioms` gate. Exit codes: `2` = **REFUTED** (the circuit is under-constrained or the spec is wrong — the counterexample is in the output file), `0` = **SURVIVED** (no refutation within budget; evidence, not proof), `1` = infrastructure error.

### `scribe judge`

The verdict engine as one command: prove AND attack, and say which side won.

```sh
scribe judge --gadget examples/range-check/gadget.toml \
  [--prove-iters N] [--refute-iters M] [--prime P] [--samples-per-iter K]
```

The prover runs first (a kernel-accepted proof settles the question — no counterexample can exist, and sound gadgets usually prove in an iteration or two). Only if proving exhausts its budget does the adversarial refuter run. The verdict is backed by a kernel-checked artifact whenever it is not UNDETERMINED:

| Exit code | Verdict | Meaning |
|---|---|---|
| `0` | **SOUND** | kernel-accepted proof of the spec (path printed) |
| `1` | **UNDETERMINED** | neither proof nor refutation within budget |
| `2` | **UNSOUND** | kernel-checked counterexample (path printed) |
| `3` | — | infrastructure error |

The exit codes are stable and documented so third parties can script `scribe judge` in their own CI.

Completed judge proofs and refutations are preserved under
`lean/ZkGadgets/Evidence/` (or the selected Lake project's equivalent), with
filenames bound to the circuit and artifact contents. Commit the printed evidence
path; incomplete attempts stay in the ignored `Bench/` directory. Cache records
point to the preserved artifact, so later attempts do not overwrite its evidence.

`check` and `judge` report `ValidationSkipped` when a circuit corpus exists but
their acceptance procedure has not been measured. The historical `LeanOracle`
corpus report measures a different pipeline and is not automatically applied to
these commands. Use `scribe corpus validate --dry-run` to inspect that report.

**Best-of-n sampling.** `--samples-per-iter K` (also on `refute` and `proof-pilot`) fires K attempts per iteration and lets the kernel filter: candidates are deduplicated, tried shortest-first, and the first to build wins. Parallel sampling is soundness-free — a wrong candidate costs a build, never a false acceptance — and the transcript records every candidate plus the acceptance index, so `--replay` determinism is preserved.

### `scribe demo`

The five-minute first-run experience, built around the range-check gadget (legible to non-hash ZK engineers). Three tiers:

| Tier | What it does | Requirements |
|---|---|---|
| `scribe demo` | Dry-run: walks through the pipeline and shows the gadget description | none |
| `scribe demo --verify` | Runs `lake build` on the pre-computed `RangeCheck.lean` proof | Lean (no API key) |
| `scribe demo --live` | Runs the full LLM proof loop on a fresh scaffold | Lean **and** an API key / backend |

```sh
scribe demo                          # dry-run, no Lean or API key
scribe demo --verify                 # kernel-check the pre-computed proof
scribe demo --live --backend claude  # full LLM proof loop on a fresh scaffold
```

### Running the loop directly

```sh
# emit a scaffold from an IR file
cargo run -p lean-emit -- examples/poseidon-sbox/gadget.toml

# run the proof loop on a target file
cargo run -p proof-pilot -- lean/ZkGadgets/AutoProof.lean \
  --lake-dir lean \
  --max-iters 10 \
  --transcript transcript.log
```

`proof-pilot` calls the model with the file + build errors, extracts the proof from the response, patches the file, and repeats until both the project build and the exact target compilation pass clean. Useful flags:

- `--notes NOTES.md` — write a learning log; each iteration records the tactics tried and cites worked examples from `lean/ZkGadgets/`.
- `--save-transcript session.json` — save a versioned JSON transcript (iteration history, toolchain string, Mathlib rev).
- `--replay session.json` — deterministically replay a transcript; refuses on toolchain mismatch unless `--allow-toolchain-mismatch`.
- `--lsp` — use the Lean language server for structured diagnostics (goal states + hypotheses) instead of raw `lake build` text.
- `--system-prompt <file>` — override the default system prompt (`prompts/lean-prover.md`).

See [`transcripts/poseidon-sbox.md`](transcripts/poseidon-sbox.md) for a session that closes the Poseidon S-box proof in 2 iterations.

## Archived integrations

The zkGolf command, harvesting scripts and competition playbooks, Halva runtime
bridge (`scribe verify` / `scribe init`), and `gadget-ir` compatibility crate were
retired on 2026-10-09. The current CLI uses `circuit-ir` directly. `demo --live`
uses the same range-check TOML input as the dry-run and checked demo.

The complete prior implementation is preserved locally on
`codex/archive-deferred-2026-10-09`, at commit
`3584bd30031acf653e90947c485385c2e2b40f08`. It is also recoverable from Git
history. The three Halva Lean proofs and extraction/spec fixtures remain as
regression evidence; no Halva executable or upstream merge is needed to check them.

[NethermindEth/Halva #10](https://github.com/NethermindEth/Halva/pull/10) is an
open multiplicative-generator predicate fix, not lookup extraction. It is not a
dependency of the current runtime.

## Proven Gadgets

Every theorem below is complete and kernel-checked (`lake build` is green, and each theorem's `#audit_axioms` gate confirms it depends only on `propext`, `Classical.choice`, and `Quot.sound`).

| Gadget | Constraints | Soundness claim |
|---|---|---|
| 8-bit range check | 9 (8 boolean + decomposition) | `ZMod.val x < 256` (requires `p > 256`) |
| conditional select | 2 (boolean + mux) | `(b = 0 ∧ z = y) ∨ (b = 1 ∧ z = x)` |
| poseidon s-box | 3 (squaring chain) | `y = x ^ 5` |
| non-zero check | 1 (inverse) | `x ≠ 0` |
| edwards addition | 2 (baby jubjub add) | output point on curve (closure — see scope note) |
| **Halva** polynomial range check | 1 (10-factor polynomial) | `ZMod.val advice < 10` on enabled rows (requires `P > 10`) |
| **Halva** Fibonacci | 1 add gate + 17 copy constraints | output instance cell `= 21·f(0) + 34·f(1)` |
| **Halva** binary number | 4 (2 boolean + recomposition + range) | bits `b₀,b₁` with value `= 2·b₀ + b₁`, never both set |

> [!NOTE]
> **Scope — know what you proved.**
> - **Edwards addition proves closure, not functional correctness.** Inputs on the curve + the gadget constraints imply the output is on the curve. That is necessary but not sufficient for "computes EC addition" — a buggy gadget could emit a *wrong* on-curve point. Full soundness would conclude `(x₃,y₃) = (x₁,y₁) + (x₂,y₂)` (or witness uniqueness); the nonzero-denominator hypotheses are also *assumed* rather than derived from Baby Jubjub's completeness. Both are documented in [`EdwardsAddition.lean`](lean/ZkGadgets/EdwardsAddition.lean) and tracked as future work.
> - **Lookups and permutation arguments are not yet exercised.** Every Halva circuit proven here has `all_lookups = true` and `all_shuffles = true` stubbed trivially by the extractor — the theorems cover gate and copy constraints only. Lookup/permutation arguments are exactly where real halo2 soundness gets hard; these fixtures do not establish lookup/permutation soundness.

## Benchmark: ZKGadgetEval

`crates/bench` runs the proof loop over a 20-gadget suite (`benchmark/suite.toml`, tiers 1–3 by difficulty) and reports statistics an eval can be judged on, not just a smoke-test pass count:

```sh
cargo run -p zkgadget-eval -- --backend claude --budget 5 \
  --samples 3 --modes build,lsp -o results.json
```

- **`--samples k`** — resample each gadget *k* times; per gadget the JSON reports the unbiased **pass@k** estimator (`1 − C(n−c,k)/C(n,k)`) for every `k ≤ n` plus a **Wilson 95% interval** on the per-sample prove probability, so run-to-run variance is measured instead of hidden.
- **`--modes build,lsp`** — the feedback-mode axis (raw `lake build` text vs. structured LSP goal states) runs inside one invocation as an A/B; the summary is broken down per mode.
- **Negative gadgets** — the suite contains five deliberately buggy circuits whose spec is *false* (`kind = "negative"`), spanning distinct audit-bug classes: a range check missing a boolean constraint, a vacuous `x − x = 0` constraint, the classic is-zero gadget missing its `x·out = 0` half, a swap gate with a dangling output wire, and a one-term constraint typo (`x·inv − inv` for `x·inv − 1`). Every spec is kernel-checked *false* (a concrete counterexample refutes it, documented in each TOML), gadget names are neutral so nothing the model sees marks them as traps, and the loop is graded on **refusing** to prove them. A "proved" negative is a soundness alarm: the run prints it loudly and exits `2`. Without negatives, a suite cannot distinguish "the loop proves true specs" from "the loop proves anything you hand it".

Honest limitations: the suite exercises algebraic gate constraints only (no lookup or permutation arguments — see the scope note above), and samples are independent reruns of the same nondeterministic loop, not seed-controlled.

Results so far (claude-sonnet-5, two full-suite runs: a 1-sample A/B + a 3-sample variance run): **118/120 positive sessions proved, negatives refused 16/16, zero alarms**; no measurable quality difference between build and LSP feedback, and range-check-8 is the suite's only sub-1.0 pass@1 cell — see [`benchmark/RESULTS.md`](benchmark/RESULTS.md) for tables and caveats.

## Docker

The `ghcr.io/lucidsamuel/scribe` image is built on every push to `main` and on version tags (`.github/workflows/docker.yml`). It bundles:

- Rust release binaries: `scribe`, `proof-pilot`
- elan + the Lean toolchain pinned to `leanprover/lean4:v4.30.0-rc2`
- pre-cached Mathlib oleans (~2.5 GB of the ~3.2 GB image)

```sh
docker pull ghcr.io/lucidsamuel/scribe:latest
docker run --rm ghcr.io/lucidsamuel/scribe:latest scribe demo

# build locally (from repo root)
docker build -t scribe:dev .
docker run --rm scribe:dev scribe --help
```

Tags: `latest` (main branch), `sha-<commit>` (per-commit), `v<semver>` (releases).

## Project Structure

```
crates/            verdict core, frontends, oracles, proof loop and CLI
lean/ZkGadgets/    checked gadget proofs, audit commands and corpus artifacts
corpus/            versioned circuit and MSM discrimination evidence
benchmark/         suite manifests and recorded evaluation results
examples/          circuit IR / extraction + specification inputs
transcripts/       example proof-pilot sessions
prompts/           system prompts for proving and refutation
docs/              architecture and v2.1 design records
```

The complete crate inventory is in [architecture.md](docs/architecture.md).

## Documentation

- [**architecture.md**](docs/architecture.md) — data flow, crate descriptions, how the pieces connect.
- [**why.md**](docs/why.md) — motivation: why formally verify ZK circuits, and why an LLM loop.
- [**poseidon-sbox transcript**](transcripts/poseidon-sbox.md) — a real session closing a proof in 2 iterations.

## Contributing

Contributions are welcome — please open an issue or PR on [GitHub](https://github.com/LucidSamuel/scribe).

Before committing, enable the git hook that rejects any `sorry`, `axiom`, or `native_decide` added to Lean files (a fast pre-filter — the build's `#audit_axioms` gates are the real check):

```sh
git config core.hooksPath .githooks
```

> [!CAUTION]
> CI runs `cargo check` + `cargo test --workspace`, `lake build` (which enforces the per-theorem `#audit_axioms` gates), and a fast `sorry`/`axiom`/`native_decide` pre-filter scan over `lean/ZkGadgets`. A green local `lake build` and `cargo test` are the bar before opening a PR; running `cargo fmt` and `cargo clippy` first is good practice.

## License

Licensed under the [MIT License](./LICENSE-MIT).
