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

Zero-knowledge circuits are notoriously hard to get right: a single under-constrained gate is a soundness bug that no amount of testing reliably catches. **scribe** turns the soundness of a ZK gadget into a theorem and proves it — using a large language model to *write* the proof and the **Lean 4 kernel** to *check* it.

> [!IMPORTANT]
> The Lean kernel is the oracle, not the LLM. `proof-pilot` builds the Lake project and then compiles the exact target file. The model cannot fake acceptance with `sorry`, `axiom`, or `native_decide` — these are blocked in three independent places: `proof-pilot` itself, a pre-commit hook, and CI.

Three properties make this trustworthy:

- **Sound by construction.** Every proof in this repo is checked by the Lean 4 kernel. `#print axioms` on each theorem shows only the standard axioms — no `sorryAx`, no custom assumptions.
- **Automated.** An LLM drives a closed feedback loop — edit the proof, compile, read the errors (or structured LSP goal states), repeat — until the kernel accepts or the budget runs out.
- **Real circuits.** The `halva-bridge` consumes actual halo2 extractions (via [Nethermind's Halva](https://github.com/NethermindEth/halo2-fv-extractor)) and proves their soundness against a human-written specification.

## How It Works

scribe is a small Rust workspace. The pipeline runs IR → Lean scaffold → LLM proof loop → kernel-accepted `.lean`:

1. **`gadget-ir`** — a minimal IR for polynomial constraints over a prime field (TOML → struct).
2. **`lean-emit`** — reads the IR and emits a Lean 4 file with the theorem statement and a `sorry`.
3. **`proof-pilot`** — drives an LLM backend in a loop: edit the proof → compile the target file → read the errors → repeat. Stops when the kernel accepts or the budget is exhausted.
4. **`halva-bridge`** — combines a Halva halo2 extraction with a user specification and (optionally) sends the resulting theorem to `proof-pilot`.
5. **`scribe-cli`** — the top-level `scribe` binary, with `verify`, `init`, and `demo` subcommands.

## Getting Started

### Docker (fastest)

The published image bundles the Rust binaries, the Lean toolchain, and pre-cached Mathlib oleans — so there is no ~30-minute cold Mathlib build.

```sh
# five-minute demo: dry-run the range-check gadget proof (no API key needed)
docker run --rm ghcr.io/lucidsamuel/scribe:latest scribe demo

# verify a Halva extraction against a user spec (requires ANTHROPIC_API_KEY)
docker run --rm \
  -e ANTHROPIC_API_KEY="$ANTHROPIC_API_KEY" \
  -v "$(pwd)":/workspace \
  ghcr.io/lucidsamuel/scribe:latest \
  scribe verify \
    --halva-output /workspace/extracted.lean \
    --spec-file    /workspace/spec.lean \
    --output       /workspace/Proof.lean
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
> Running `scribe`, `proof-pilot`, or `halva-bridge` against a live model needs a backend. The default backend shells out to the `claude` CLI; pass `--backend openai|anthropic|...` plus `--api-key` / `--model` to use a hosted API instead. Run any binary with `--help` for the full flag list.

## Usage

### `scribe verify`

The single-command path from a Halva extraction (or extractor project) to a kernel-checked proof.

```sh
# from a pre-extracted Halva .lean file + a user spec snippet
scribe verify \
  --halva-output extracted.lean \
  --spec-file    spec.lean \
  --output       lean/ZkGadgets/MyCircuit.lean \
  [--backend claude|openai|...] \
  [--model MODEL] \
  [--max-iters N] \
  [--notes NOTES.md] \
  [--save-transcript session.json]

# from a Halva extractor project directory (runs the extractor, then verifies)
scribe verify \
  --circuit   path/to/halva-extractor-project \
  --spec-file spec.lean \
  --output    lean/ZkGadgets/MyCircuit.lean
```

Both forms run `proof-pilot` by default and exit `0` only when the Lean kernel accepts the proof. The output `.lean` file is the artifact; no `sorry` or `axiom` survive. Pass `--no-prove` to emit only the scaffold (which still contains `sorry`) and skip the proof loop.

> [!NOTE]
> **Scope.** `scribe verify --circuit` operates on a Halva *extractor project* — you still author the small extractor program that runs against your halo2 circuit. scribe does not read raw halo2 Rust source directly. The chain is: extractor-project output → Lean scaffold → LLM proof loop → kernel-accepted `.lean`.

### `scribe init`

Generates the editable Halva extractor project that `scribe verify --circuit` expects.

```sh
scribe init \
  --circuit path/to/raw-halo2-circuit-crate \
  --output  path/to/halva-extractor-project \
  [--name MyCircuit] \
  [--halva-git https://github.com/<owner>/<repo>.git] \
  [--halva-rev REV]
```

The generated project contains `Cargo.toml`, `src/main.rs`, and a README. Fill in `src/main.rs` to instantiate your circuit, call Halva, and print the extracted Lean to stdout — then pass that project to `scribe verify --circuit`. If `--halva-git` is omitted, the generated `Cargo.toml` leaves the Halva dependency as an explicit TODO rather than guessing a repository URL.

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

## The Halva Bridge

`halva-bridge` turns a real halo2 extraction into a proven soundness theorem. It parses Halva's `meets_constraints` output, merges in a user `Spec` + `soundness` theorem, and hands the result to `proof-pilot`.

```sh
cargo run -p halva-bridge -- examples/halva-range-check/extracted.lean \
  --spec-file examples/halva-range-check/spec.lean \
  --output    lean/ZkGadgets/HalvaRangeCheck.lean
```

Use `--prove` to launch `proof-pilot` after scaffolding. Structured specs can use `--spec <expr>` with repeatable `--extra-import <module>` flags; run `halva-bridge --help` for the backend and proof-loop options.

The same flow scales to harder circuits. `examples/halva-fibonacci/` and `examples/halva-binary-number/` are real extractions (`cargo run --example fib` / `--example scroll-binary-number` in the Halva repo) bridged to proven theorems — exercising **copy constraints** and **multi-gate** circuits respectively, neither of which the range-check example touches.

## Proven Gadgets

Every theorem below is complete and kernel-checked (`lake build` is green, with no `sorry` / `axiom` / `native_decide`).

| Gadget | Constraints | Soundness claim |
|---|---|---|
| 8-bit range check | 9 (8 boolean + decomposition) | `∃ k : Fin 256, k.val = x` |
| conditional select | 2 (boolean + mux) | `(b = 0 ∧ z = y) ∨ (b = 1 ∧ z = x)` |
| poseidon s-box | 3 (squaring chain) | `y = x ^ 5` |
| non-zero check | 1 (inverse) | `x ≠ 0` |
| edwards addition | 2 (baby jubjub add) | output point on curve |
| **Halva** polynomial range check | 1 (10-factor polynomial) | selected value is in `Fin 10` |
| **Halva** Fibonacci | 1 add gate + 17 copy constraints | output instance cell `= 21·f(0) + 34·f(1)` |
| **Halva** binary number | 4 (2 boolean + recomposition + range) | bits `b₀,b₁` with value `= 2·b₀ + b₁`, never both set |

## Docker

The `ghcr.io/lucidsamuel/scribe` image is built on every push to `main` and on version tags (`.github/workflows/docker.yml`). It bundles:

- Rust release binaries: `scribe`, `proof-pilot`, `halva-bridge`
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
crates/
  gadget-ir/       constraint system IR + TOML deserialization
  lean-emit/       IR → Lean 4 scaffold with sorry
  proof-pilot/     LLM proof loop (patcher, lean runner, session logging, transcript, replay)
  halva-bridge/    Halva extraction + semantic specification bridge
  scribe-cli/      top-level `scribe` binary (verify + init + demo)
  bench/           ZKGadgetEval benchmark suite
lean/ZkGadgets/    the proven theorems (Field + 8 gadgets)
examples/          IR / extraction + spec inputs for every gadget
transcripts/       example proof-pilot sessions
prompts/           system prompt(s) for the proof loop
docs/              architecture.md, why.md
```

## Documentation

- [**architecture.md**](docs/architecture.md) — data flow, crate descriptions, how the pieces connect.
- [**why.md**](docs/why.md) — motivation: why formally verify ZK circuits, and why an LLM loop.
- [**poseidon-sbox transcript**](transcripts/poseidon-sbox.md) — a real session closing a proof in 2 iterations.

## Contributing

Contributions are welcome — please open an issue or PR on [GitHub](https://github.com/LucidSamuel/scribe).

Before committing, enable the git hook that rejects any `sorry`, `axiom`, or `native_decide` added to Lean files:

```sh
git config core.hooksPath .githooks
```

> [!CAUTION]
> CI runs `cargo check` + `cargo test --workspace`, `lake build`, and a `sorry`/`axiom`/`native_decide` scan over `lean/ZkGadgets`. A green local `lake build` and `cargo test` are the bar before opening a PR; running `cargo fmt` and `cargo clippy` first is good practice.

## License

Licensed under the [MIT License](./LICENSE-MIT).
