# scribe

```
               _ _
  ___  ___ _ __(_) |__   ___
 / __|/ __| '__| | '_ \ / _ \
 \__ \ (__| |  | | |_) |  __/
 |___/\___|_|  |_|_.__/ \___|
```

an llm proof-completion loop for zk gadgets, with the lean kernel as oracle.

## what it does

1. **gadget-ir**: a minimal IR for polynomial constraints over a prime field.
2. **lean-emit**: reads the IR, emits a Lean 4 file with the theorem statement and `sorry`.
3. **proof-pilot**: drives an LLM backend in a loop: edit proof → compile the target Lean file → read errors → repeat. stops when the kernel accepts or budget is exhausted.
4. **halva-bridge**: combines Halva's halo2 extraction with a user specification and optionally sends the resulting theorem to proof-pilot.
5. **scribe-cli**: top-level `scribe` binary with `verify` and `demo` subcommands (see below).

the lean kernel is the oracle. proof-pilot builds the Lake project and then compiles the exact target file, including files outside the default Lake target. the llm cannot fake acceptance with `sorry` or `axiom`, which are blocked by proof-pilot, the pre-commit hook, and CI.

## quickstart

### docker (fastest)

the published image bundles Rust binaries, the Lean toolchain, and pre-cached Mathlib oleans.

```
# five-minute demo: dry-run the range-check gadget proof (no API key needed)
docker run --rm ghcr.io/lucidsamuel/scribe:latest scribe demo

# verify a Halva extractor project against a user spec (requires ANTHROPIC_API_KEY)
docker run --rm \
  -e ANTHROPIC_API_KEY="$ANTHROPIC_API_KEY" \
  -v "$(pwd)":/workspace \
  ghcr.io/lucidsamuel/scribe:latest \
  scribe verify \
    --halva-output /workspace/extracted.lean \
    --spec-file    /workspace/spec.lean \
    --output       /workspace/Proof.lean

# build locally
docker build -t scribe:dev .
```

see the [docker section](#docker) below for more.

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

`lake build` should exit 0 with no warnings. all six gadget proofs are complete.

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

proof-pilot calls `claude -p` with the file + build errors, extracts the proof from the response, patches the file, and repeats until both the project build and exact target compilation pass clean or the budget is exhausted.

additional proof-pilot flags (v2):

- `--notes NOTES.md` — write a `NOTES.md` learning log after the session; each iteration records concrete tactics tried and cites worked examples from `lean/ZkGadgets/`.
- `--save-transcript session.json` — save a versioned JSON transcript recording the full iteration history, toolchain string, and Mathlib rev.
- `--replay session.json` — deterministically replay a saved transcript; refuses on toolchain mismatch unless `--allow-toolchain-mismatch` is passed.
- `--lsp` — use the Lean language server for structured diagnostics (goal states + hypotheses) instead of raw `lake build` text.

by default it uses `prompts/lean-prover.md` as the system prompt; pass `--system-prompt <file>` to override it.

see [transcripts/poseidon-sbox.md](transcripts/poseidon-sbox.md) for an example session closing the Poseidon S-box proof in 2 iterations.

### bridge a Halva extraction

```
cargo run -p halva-bridge -- examples/halva-range-check/extracted.lean \
  --spec-file examples/halva-range-check/spec.lean \
  --output lean/ZkGadgets/HalvaRangeCheck.lean
```

Use `--prove` to launch proof-pilot after scaffolding. Structured specifications can use `--spec <expr>` with repeatable `--extra-import <module>` flags. Run `halva-bridge --help` for the backend and proof-loop options.

## scribe verify

`scribe verify` is the single-command path from a Halva extractor project to a kernel-checked proof.

**scoping note:** `scribe verify --circuit` operates on a Halva *extractor project* — you still author the Halva extractor program that runs against your halo2 circuit. scribe does not read raw halo2 Rust source. the command is: extractor-project-output → Lean scaffold → LLM proof loop → kernel-accepted `.lean` file.

```
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
  --circuit path/to/halva-extractor-project \
  --spec-file spec.lean \
  --output    lean/ZkGadgets/MyCircuit.lean
```

both forms run proof-pilot by default and exit 0 only when the Lean kernel accepts the proof. the output `.lean` file is the artifact; no `sorry` or `axiom` survive. pass `--no-prove` to only emit the scaffold (which still contains `sorry`) and skip the proof loop.

## scribe demo

`scribe demo` is the five-minute first-run experience for the range-check gadget (chosen because it is legible to non-hash ZK engineers). three tiers:

| flag | what it does |
|---|---|
| _(none)_ | dry-run: walks through the pipeline conceptually and shows the gadget description — no Lean toolchain or API key required |
| `--verify` | runs `lake build` on the pre-computed `lean/ZkGadgets/RangeCheck.lean` proof (needs Lean; **no** API key); this tier runs in CI |
| `--live` | runs the full LLM proof loop on a fresh scaffold (needs Lean **and** an API key / backend) |

```
# dry-run (no Lean or API key needed)
scribe demo

# kernel-check the pre-computed range-check proof (needs Lean, no API key)
scribe demo --verify

# run the live LLM proof loop on a fresh scaffold (needs Lean + API key)
scribe demo --live --backend claude
```

the dry-run output leads with a plain-English gadget description:
> *range-check gadget: proves that a field element x satisfies 0 ≤ x < 256 by decomposing x into 8 boolean bits and checking their weighted sum.*

## docker

the `ghcr.io/lucidsamuel/scribe` image is built on every push to `main` and on version tags, via `.github/workflows/docker.yml`. it bundles:

- Rust release binaries: `scribe`, `proof-pilot`, `halva-bridge`
- elan + Lean toolchain pinned to `leanprover/lean4:v4.30.0-rc2`
- pre-cached Mathlib oleans (avoids the ~30-minute cold Mathlib build)

target image size is approximately 3.2 GB (Mathlib oleans account for ~2.5 GB of that).

```
# pull latest
docker pull ghcr.io/lucidsamuel/scribe:latest

# demo (no LLM call)
docker run --rm ghcr.io/lucidsamuel/scribe:latest scribe demo

# verify with your own files
docker run --rm \
  -e ANTHROPIC_API_KEY="$ANTHROPIC_API_KEY" \
  -v "$(pwd)":/workspace \
  ghcr.io/lucidsamuel/scribe:latest \
  scribe verify \
    --halva-output /workspace/extracted.lean \
    --spec-file    /workspace/spec.lean \
    --output       /workspace/Proof.lean

# build locally (from repo root)
docker build -t scribe:dev .
docker run --rm scribe:dev scribe --help
```

tags: `latest` (main branch), `sha-<commit>` (per-commit), `v<semver>` (releases).

## gadgets

| gadget | constraints | soundness claim |
|---|---|---|
| 8-bit range check | 9 (8 boolean + decomposition) | `∃ k : Fin 256, k.val = x` |
| conditional select | 2 (boolean + mux) | `(b = 0 ∧ z = y) ∨ (b = 1 ∧ z = x)` |
| poseidon s-box | 3 (squaring chain) | `y = x ^ 5` |
| non-zero check | 1 (inverse) | `x ≠ 0` |
| edwards addition | 2 (baby jubjub add) | output point on curve |
| Halva polynomial range check | 1 (10-factor polynomial) | selected value is in `Fin 10` |

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
  proof-pilot/     LLM proof loop (patcher, lean runner, session logging, transcript)
  halva-bridge/    Halva extraction + semantic specification bridge
  scribe-cli/      top-level `scribe` binary (verify + demo subcommands)
lean/
  ZkGadgets/
    Field.lean              field helper lemmas (proven)
    RangeCheck.lean         8-bit range check soundness (proven)
    ConditionalSelect.lean  conditional select soundness (proven)
    PoseidonSbox.lean       poseidon s-box x^5 soundness (proven)
    NonzeroCheck.lean       field nonzero check soundness (proven)
    EdwardsAddition.lean    baby jubjub addition closure (proven)
    HalvaRangeCheck.lean     Halva range-check extraction soundness (proven)
examples/
  range-check/           8-bit range check (9 witnesses, 9 constraints)
  conditional-select/    conditional select (4 witnesses, 2 constraints)
  poseidon-sbox/         poseidon s-box x^5 (4 witnesses, 3 constraints)
  nonzero-check/         field inverse (2 witnesses, 1 constraint)
  edwards-addition/      baby jubjub point addition (6 witnesses, 2 constraints)
  halva-range-check/     real Halva extraction + user specification
transcripts/
  poseidon-sbox.md   example proof-pilot session (autonomous closure in 2 iterations)
docs/
  architecture.md  data flow + crate descriptions
  why.md           motivation
```

## docs

- [architecture.md](docs/architecture.md) — data flow, crate descriptions, how the pieces connect
- [why.md](docs/why.md) — motivation: why formal verification of zk circuits, why an llm loop
- [poseidon-sbox transcript](transcripts/poseidon-sbox.md) — example proof-pilot session closing a proof in 2 iterations

## license

MIT
