# Scribe v2 Roadmap

Status: in progress (started 2026-06-17). This file is the durable, authoritative
spec for the v2 work. Agents implementing phases must read this first.

## Goals (P1–P5)

- **P1 `scribe verify`** — single command from a Halva *extractor project* (or
  pre-extracted Halva output) to a kernel-checked proof.
- **P2 `scribe demo`** — five-minute first-run experience, three tiers.
- **P3 Docker** — reproducible image with pre-cached Lean/Mathlib.
- **P4 Structured failure output** — `SessionJournal` → `NOTES.md`.
- **P5 Transcript capture & replay** — `SessionJournal` → versioned JSON → deterministic replay.

## Locked decisions (resolved from review)

1. **Scoping honesty.** "One command" = extractor-project → proof, NOT raw halo2
   circuit → proof. The user still authors the Halva extractor program. Docs MUST
   say this plainly. `scribe init --circuit` now generates the editable extractor
   project template, but it does not parse raw halo2 Rust source directly.
2. **Demo gadget = range-check** (legible to non-hash ZK people), not poseidon-sbox.
   Lead dry-run output with a one-line plain-English description of the gadget.
3. **Replay toolchain pinning.** Transcript JSON records `toolchain` (contents of
   `lean/lean-toolchain`) and the Mathlib rev (from `lean/lake-manifest.json`).
   Replay refuses on mismatch unless `--allow-toolchain-mismatch` is passed.
4. **Testing is not optional.** Each phase ships tests:
   - NOTES.md: snapshot test of rendered output.
   - transcript: round-trip save→load→replay test.
   - demo: `scribe demo --verify` runs in CI (Linux + macOS).
5. **NOTES.md is a learning tool, not a goal mirror.** Templates suggest concrete
   tactics/lemmas and cite a worked instance in `lean/ZkGadgets/*.lean`
   (e.g. RangeCheck.lean), not just restate the goal.

## Architecture contract (the foundation — Phase 1)

Everything depends on these shared types compiling green.

- `proof_pilot::backend::make_backend(name, model, api_key, base_url) -> Box<dyn Backend>`
  — extracted from `halva-bridge/src/main.rs`, now shared. Plus `require_api_key`.
- `proof_pilot::journal::{SessionJournal, IterationRecord}` — `#[derive(Serialize, Deserialize)]`.
  - `SessionJournal`: theorem statement, lean_file, backend name, toolchain string,
    final outcome, `Vec<IterationRecord>`.
  - `IterationRecord`: iteration index, source_before, source_after, prompt,
    llm_response, build_errors, goal_states (text), suggestions, patch applied/rejected.
- `proof_pilot::session::run(config, backend) -> (SessionResult, SessionJournal)`
  — accumulates a record per iteration in BOTH the lake and LSP loops.
- `halva-bridge` exposes a `lib.rs` with the reusable parse/scaffold functions
  (`parse_halva_output`, `scaffold_soundness`, `scaffold_raw`, spec helpers) so
  `scribe-cli` can consume them; `main.rs` becomes a thin wrapper over the lib.
- `lib.rs` gains `pub mod journal;`.
- Existing 58 tests still pass; workspace builds clean.

## Phases (post-foundation, parallelizable)

- **B (P4+P5 in proof-pilot):** `notes.rs`, `transcript.rs`, `replay.rs`, new CLI
  flags (`--notes`, `--save-transcript`, `--replay`, `--allow-toolchain-mismatch`),
  tests. Owns all of `crates/proof-pilot` post-foundation.
- **C (P1+P2 scribe-cli):** new `crates/scribe-cli` (binary `scribe`) with `verify`
  and `demo` subcommands; workspace member. Depends only on the foundation API +
  halva-bridge lib. Does NOT edit proof-pilot source.
- **D (P3 + docs):** `Dockerfile`, `.github/workflows/docker.yml`, README updates.

## File ownership (no two agents touch the same file)

- Foundation: proof-pilot/{backend.rs, journal.rs, session.rs, lib.rs, main.rs,
  Cargo.toml}, halva-bridge/{lib.rs, main.rs, Cargo.toml}.
- B: proof-pilot/{notes.rs, transcript.rs, replay.rs, lib.rs (+mods), main.rs (+flags)}.
- C: scribe-cli/* (new), root Cargo.toml ([workspace] members).
- D: Dockerfile, .github/workflows/docker.yml, README.md.
