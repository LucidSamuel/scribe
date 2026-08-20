# Phase A — known follow-ups

Findings from the Phase A implementation that are deliberately **not** fixed
yet. Each entry states the finding, why it is deferred, and what a fix would
involve, so the phase that hits it can be read against this file.

## F2 — C1 (`#audit_uses`) needs a policy for extracted IR

**Status: DECIDED 2026-08-20 (option b).** C1 stays non-gating everywhere in
the record/cache pipeline. *Dropped* hypotheses are caught structurally by the
binding probe — the statement regenerated from the IR carries every constraint
hypothesis and must match definitionally, which is stronger than C1 ever was —
so what C1 uniquely detects is *decorative* hypotheses, a smell rather than
unsoundness, reported but never gating. README wording updated to match. D5's
corpus-wide rendering should label extracted-IR C1 failures as
expected-for-faithful-extraction rather than alarming.

Original finding, kept for context:
**Where:** the C1 probe in `scribe check --record` / `bind_and_audit`
(`crates/scribe-cli/src/check.rs`), and the `#audit_uses` command itself.

Faithful extraction includes constraints that are *correct but not
load-bearing for a given spec*: ragu's SYSTEM-gate pair and spare `D` wires
are real constraints of the circuit, yet a spec about one output does not use
them, so `#audit_uses` reports FAILED on a proof whose extraction is complete
— the more faithful the frontend, the "worse" C1 looks. C1's discipline
("hypotheses are load-bearing") was designed against hand-written gadgets
where every hypothesis was authored on purpose.

Candidate policies: (a) per-frontend expected-unused annotations carried in
`CircuitIR` provenance and honored by the probe; (b) scope C1's gating meaning
to hand-written gadgets and report-only for extracted IR (the current de facto
behavior — C1 is already non-gating in the record pipeline, so today this is a
rendering/wording question); (c) spec-relevance slicing (flag only unused
hypotheses *reachable* from spec variables). Decide before Phase D5 renders
corpus-wide audit summaries, or every extracted entry will render with an
alarming-but-expected C1 failure.

## F1 — Decomposed mode silently disables itself on circuits with definitions

**Status:** open. Deferred until Phase B measures how often it bites.
**Where:** `crates/lean-emit/src/lib.rs`, `emit_lean_decomposed` (the
definitions guard in its entry condition).

### Finding

`lean-emit`'s decomposed mode — the scaffold variant that emits one helper
lemma per constraint so the LLM can attack a hard proof in small steps — falls
back to the plain single-theorem scaffold whenever the circuit carries
`definitions`. The guard exists because each helper lemma is a standalone
theorem: a constraint that mentions a definition name would need the whole
`let` chain restated in every helper's statement, and Phase A shipped the
simple fallback instead.

Nothing in `examples/` hits this path — no example gadget has definitions. But
**extracted ragu IR frequently carries definitions**: ragu's `Driver::add` is
free unlimited fan-in, which is exactly why `CircuitIR` grew `definitions` in
the first place (inlining a virtual wire into every constraint that mentions
it explodes the emitted Lean). Phase B measured the rate rather than assuming
it: **1 of 3 extracted circuit shapes** carries definitions (asserted by a
regression test in `crates/frontend-ragu`), and the ratio rises on real gadget
libraries since `add()` is ragu's free primitive. Consequence: decomposed mode
silently disables itself on every *definition-bearing* ragu circuit — which
skews toward the large, many-constraint circuits where hard proofs need
decomposition most.

### What a fix would involve

Two candidate shapes, in rough order of preference:

1. **Restate the `let` chain per helper lemma.** Each
   `lemma <gadget>_extract_<label>` opens with the same
   `let d1 := …; let d2 := …` prefix (only the definitions its constraint
   actually reaches, transitively, to keep statements small), followed by the
   constraint antecedent. Mechanical, local to `emit_lean_decomposed`, and
   keeps helpers self-contained. Cost: repeated `let` prefixes in the emitted
   file; statement size grows with definition depth.

2. **Hoist definitions into a shared context.** Emit definitions once as
   top-level `def`s parameterized over the variables (or a `section` with
   `variable` binders plus local `abbrev`s), so helpers and the main theorem
   all reference the same names. Smaller emitted text, but top-level `def`s
   change the unfolding behavior the prover sees (`simp [s]` vs. `intro s`),
   and the system prompt / lessons corpus would need to learn the new shape.

Either way the main theorem keeps its current definitions shape (`let` chain
opening the conclusion, kernel-validated in Phase A), so the fix is confined to
the decomposed emitter.

### Why not fixed now

Phase B is the first consumer of definition-carrying IR and will measure (a)
how many extracted circuits exceed the ≥2-constraint threshold where
decomposition matters, and (b) whether the plain scaffold's failure rate on
those circuits actually justifies the added emitter complexity. Fixing ahead of
that data would be speculative. **Phase B's report should state how often the
fallback fired** — that number decides whether this follow-up is urgent or
cosmetic.

## F3 — Extracted ragu constraints carry no source spans

**Status:** open. Surfaced by the Phase B review; owner Phase A (frontend-ragu
enhancement) with a D2 rendering consequence.
**Where:** `crates/frontend-ragu` sets `origin: None` on every extracted
constraint; `crates/scribe-cli/src/citations.rs` then falls back as designed.

D2's diagnostics render `file:line — label` only when the frontend recorded a
`Constraint.origin`. `frontend-toml` circuits can carry spans in their TOML;
extracted ragu circuits currently cannot — ragu's `Driver` calls carry no
caller location, so every ragu constraint gets `origin: None` and a stalled
proof cites the constraint *label and IR position* instead of a Rust
`file:line`. That fallback is honest and readable, but it is not the
`spend.rs:92 — enforce_zero("nullifier binding")` experience, and D1/D2 must
not be presented as source-cited diagnostics *for ragu circuits* until this
closes.

A fix would capture `#[track_caller]` / `std::panic::Location` in the
extractor's `enforce_zero` / `gate` / `add` entry points and stamp
`SourceSpan { file, line, label }` from it — cheap, but it changes
frontend-ragu's driver plumbing and should ride with D1 (the `extract!`
macro), which touches the same entry points.
