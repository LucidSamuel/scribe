# Phase D — DevEx

**Owns:** `crates/scribe-macros/*` (new), `crates/scribe-cli/src/*`,
`crates/bench/src/main.rs`, `benchmark/suite.toml`.

**Depends on:** Phase A green. Lands incrementally alongside B and C — each item
below is independently shippable.

## Why

Formal-methods tools die of friction, not of unsoundness. Every item here is
chosen because it removes a specific reason an engineer would close the tab.

The benchmark for "good enough" is not "a verification specialist can use it."
It is "a protocol engineer who has never written Lean can run it on their own
circuit and understand the output."

## Scope

### D1 — Extraction is a `cargo test`

`roadmap-v2.md` locked decision 1 conceded the honest scoping of the Halva path:
the user must author an extractor project per circuit. That tax is the main
reason the Halva front-end has three proven circuits and not thirty. Do not
reproduce it for ragu.

Ship `crates/scribe-macros` with:

```rust
scribe::extract!(SpendCircuit);
```

which expands to a `#[test]` that runs `frontend-ragu` over the circuit and
writes `CircuitIR` JSON to `target/scribe/<name>.json`.

Why a test and not a binary: it needs no new Cargo target, no config file, no
separate project, and it runs in CI the user already has. Extraction becomes
something that happens automatically when they run their existing test suite.

### D2 — Diagnostics cite the source circuit

When a proof stalls, the current output is Lean goal state referencing generated
hypothesis names (`h_c47`). An engineer who has never written Lean closes the
tab.

Use `Constraint.origin` (added in Phase A) to render:

```
stalled on constraint 47
  spend.rs:92  enforce_zero("nullifier binding")
```

Map generated Lean hypothesis names back to source spans in the failure path and
in `NOTES.md`. This is the single highest-leverage item in the phase.

### D3 — `scribe check`: the fast, free tier

A no-LLM, no-API-key subcommand that runs in seconds:

- does the circuit extract,
- is the IR well-formed against the schema,
- is the spec syntactically valid Lean,
- do C1–C3 pass (the build-time audits — these need `lake build`, not a model).

Exit codes stable and scriptable, matching the `judge` convention.

Nobody should wait twenty minutes and spend API budget to discover a typo. This
also becomes the cheap CI gate teams run on every commit, with `judge` reserved
for changed circuits.

### D4 — Fingerprint caching

Hash the `CircuitIR` (canonical JSON, excluding `provenance.source_rev`). If a
kernel-accepted proof already exists for that fingerprint, reuse it and report a
cache hit.

This is what makes scribe a CI *gate* rather than a CI *tax*: unchanged circuits
cost nothing. Note that ragu computes deep fingerprints per routine for exactly
this kind of memoization, so the concept is already proven in-ecosystem.

Cache lives in `target/scribe/`. Proofs themselves are committed — they are the
evidence.

### D5 — Corpus tooling

Phases B and C each produce a `Corpus` (broken circuits, broken backends). This
item makes corpora ergonomic rather than artisanal:

- `scribe corpus validate <oracle>` — run `validate()` and render the
  `DiscriminationReport`, with **escapes rendered as alarms**, not table rows.
- `scribe corpus add` — record a new known-bad instance, so a confirmed
  real-world bug becomes a permanent corpus entry (locked decision 5).
- Keep `crates/bench`'s existing exit-2 soundness alarm behavior intact when a
  negative is proved; re-express it on top of `validate()` rather than
  reimplementing it.

Then render discrimination in every verdict the CLI prints. `ACCEPT (oracle
unmeasured)` must look uncomfortable — that is the honest rendering of a check
nobody has tested, and making it visible is the entire product thesis surfacing
at the UI layer.

## Acceptance

- `scribe check` exits in under 5s with no API key on a cached circuit.
- A deliberately-failing proof cites `file:line` from the source circuit in both
  terminal output and `NOTES.md`.
- `scribe::extract!` produces `CircuitIR` JSON from a plain `cargo test`, with a
  worked example in `examples/`.
- Re-running `judge` on an unchanged circuit reports a cache hit and does not
  call a model.
- `scribe corpus validate` renders a `DiscriminationReport` and shows escapes as
  alarms.
- `crates/bench` still exits 2 when a negative is proved, now via `validate()`.
- Every CLI verdict shows its discrimination status, including `unmeasured`.

## Pitfalls

- **Don't let caching hide staleness.** The fingerprint must cover the spec and
  the constraint set. A spec edit with an unchanged circuit must invalidate.
- **Don't make `check` depend on a model.** Its whole value is being free and
  instant. If C1–C3 need `lake build`, that is fine; an API key is not.
- **Keep exit codes stable.** `judge`'s codes (0 SOUND / 1 UNDETERMINED /
  2 UNSOUND / 3 infra) are documented and scripted against. `check` should follow
  the same convention, not invent a new one.
- **The corpus is load-bearing.** Do not weaken the exit-2 alarm while moving it
  onto `validate()`.
- **Never let a verdict render without its discrimination status.** That is
  locked decision 2 reaching the UI; a clean-looking ACCEPT with no measurement
  behind it is the exact failure the product exists to prevent.

## Agent prompt

```
Read roadmap-v2.1.md and docs/v2.1/README.md, then docs/v2.1/phase-d-devex.md.

Implement Phase D of the scribe v2.1 roadmap: developer experience.

You own exactly:
  crates/scribe-macros/*    (new)
  crates/scribe-cli/src/*
  crates/bench/src/main.rs
  benchmark/suite.toml

Phase A must be green. Items D1-D5 are independently shippable — do them one at
a time, each with tests, rather than as one large change. D2 (source-cited
diagnostics) is the highest-leverage item; do it first if you are only doing one.

Guiding benchmark: not "a verification specialist can use it" but "a protocol
engineer who has never written Lean can run it on their own circuit and
understand the output."

Constraints:
- scribe check must never require an API key. lake build is acceptable.
- Exit codes follow the existing judge convention (0 SOUND / 1 UNDETERMINED /
  2 UNSOUND / 3 infra). Do not invent a new scheme.
- The exit-2 soundness alarm in crates/bench must not weaken. Re-expressing it
  on top of scribe-core's validate() is the goal; changing what happens when a
  negative is proved is not.
- Every verdict the CLI prints must show its discrimination status, including
  when it is `unmeasured`. Never render a bare ACCEPT.
- Fingerprint caching must cover the spec as well as the constraints, so a spec
  edit invalidates the cache.

Before reporting done, run and paste:
  cargo fmt --all
  cargo clippy --workspace --all-targets -- -D warnings
  cargo test --workspace

Report: which of D1-D5 you completed, test count delta, and measured timing for
scribe check on a cached circuit.
```
