# Phase C — Instance 2: implementations via differential replay

**Owns:** `crates/oracle-differential/*` (new), `corpus/msm/*` (new),
`docs/v2.1/equivalence-notes.md` (new).

**Depends on:** Phase A green. **Runs in the same cycle as Phase B** — together
they determine whether `scribe-core` is real (locked decision 3).

> **Rewritten 2026-08-18** after a red-team audit of ragu at
> `fc61822c` (origin/main). The original brief proposed a broad broken-backend
> corpus graded by proof-digest equality. Three of its premises were false. This
> version is ~20% of that scope, targets the one gap that survived audit, and is
> buildable today. Read "What the audit killed" before doing anything.

## What the audit killed

**There is no proof digest.** `Proof<C, R>` (`crates/ragu_pcd/src/proof/mod.rs`)
derives only `Clone` — no `PartialEq`, no `Debug`, no serializer. Issue #660
(serde on proof) is open. The oracle the original brief proposed to grade cannot
be run today. Comparing at the **MSM boundary** instead sidesteps this entirely,
and is explicitly one of the narrow boundaries Tal names in #834 comment
5320700832 ("MSM results, (s)-evaluations, polynomial commitments, Poseidon
outputs, proof digests").

**Floor planning is not an escape.** `floor_plan()`
(`crates/ragu_circuits/src/floor_planner.rs`) is a prefix sum. There is no
proposal mechanism and no validation surface — non-overlap holds by
construction. Tal's phase-3 checklist already names the validations that close
every plan-level escape the audit could construct. Do not target it.

**Ragu already practices planted-defect oracle validation.** `PATCHER_SELFTEST`
in `qa/fuzz/src/record.rs` is a deliberately under-constrained circuit whose
oracle must fire, running in CI, alongside vacuity telemetry whose docs say "if
it creeps up, your differential is going soft." We are not introducing this
discipline. We are extending it to a surface it has not been applied to.

**Most surfaces are not externally mutable.** `s(X,Y)` evaluation (`mod wiring`
is private), registry evaluation (private fields), and floor plans
(`ConstraintSegment` has no constructor) all require patching a crate that PR
#503 is actively restructuring. Only `ragu_arithmetic::util::msm` (public,
generic) and the `PoseidonPermutation` trait are mutable from outside today.

## The gap that survived

`msm` selects its window strategy via `bucket_lookup(n)`, a 15-entry threshold
table spanning `n` up to roughly 3.2M. Different `n` take structurally different
code paths — bucket counts, window-boundary shift/limb arithmetic,
`Bucket::{None, Affine, Projective}` transitions.

Most of the fuzz fleet runs `TestRank = R<7>`, and `Limits::default()` is
`max_ops: 48` (`qa/fuzz/src/substrate.rs`). Production is
`ProductionRank = R<13>`.

**State this carefully — an earlier draft of this brief overstated it and review
caught the overstatement.** It is NOT true that the entire fleet runs `TestRank`
at 48 ops: `fuzz_verify_reject.rs` declares `type R = ProductionRank`,
`fuzz_witness_pinning.rs` caps at `Limits { max_ops: 16 }`, and other targets
vary. Verify the actual spread yourself before writing any number down.

**The gap is a hypothesis, not an established premise.** The hypothesis: a defect
confined to a large-`n` window path may be unreached by the circuit generation
the fleet actually performs, and would then be invisible to #834's phase 4 as
specified — replaying RNG fixes the randomness while doing nothing about a
generator that never reaches production sizes. Phase C exists to *measure*
whether that holds. Do not assert it in any deliverable until the measurement
supports it, and treat `fuzz_verify_reject` running at `ProductionRank` as the
obvious thing that could falsify it.

## Scope — a small corpus and one number

The original brief's *broad* corpus is dead; a corpus is not. Phase C's job in
this roadmap is to be the second instance that exercises the whole core, and a
coverage number alone touches only `Claim::Subject` — the easy half. It must also
run `Corpus`, `validate()`, and `Verdict`, or it does not test the product thesis
at all (locked decisions 3 and 5).

So: keep the narrowed MSM target, and represent it as a **small** versioned
corpus — the reference as a positive, two or three mutants as negatives. Three
entries exercise every trait exactly as well as thirty.

Target: two days.

### 1. `EquivalenceClaim` at the MSM boundary

```rust
pub struct EquivalenceClaim { pub boundary: Boundary }   // Msm for now
impl Claim for EquivalenceClaim {
    type Subject = EquivalenceSubject;   // { reference, candidate, inputs }
}
```

The subject is a pair of computations plus an input distribution — deliberately
nothing like a `CircuitIR`. **If this compiles without touching `scribe-core`,
the Phase A abstraction is real.** If it cannot, say so immediately; that finding
outranks shipping the phase.

### 2. Coverage measurement

Measure what fraction of `msm`'s branches is reached by the current
generated-circuit fleet at `TestRank`, versus what production exercises at
`ProductionRank`. Branches that matter:

- each `bucket_lookup(n)` threshold band,
- window-boundary shift/limb arithmetic,
- `Bucket::{None, Affine, Projective}` transitions.

Use the existing fuzz substrate rather than building a new generator. Report a
number.

### 3. A small corpus, placed by the measurement

Build `Corpus<EquivalenceClaim>` in `corpus/msm/`, versioned:

- **one positive** — the unmutated reference, which the oracle must accept,
- **two or three negatives** — mutants, at least one planted in a
  **demonstrably unreached** path.

Run `validate(DifferentialOracle, corpus)` and commit the
`DiscriminationReport`. The mutant in the unreached path should appear in
`escaped` — that is the finding, and having it come out of the same `validate()`
machinery Phase B uses is what proves the core generalizes.

This makes the escape *constructive* rather than hoped-for: coverage identifies
the blind spot, the mutant proves it exploitable, the report quantifies it.

Keep `crates/oracle-differential` boringly thin — compare outputs, accept iff all
match, `Undetermined` on panic (a crash is not proof of inequivalence). The
interesting work is the measurement.

### 4. `docs/v2.1/equivalence-notes.md`

The write-up: coverage numbers, the mutant, the green differential, and what
input-size strategy would close the gap. This doubles as the draft of a comment
on #834.

## Out of scope (locked decision 4, reinforced by the audit)

- Performance benchmarking or timing anything. If you measure speed, you have
  drifted into building ragu's harness instead of grading it.
- Floor planning, `s(X,Y)`, registry evaluation — not externally mutable, and
  under active restructuring in PR #503.
- Constant-timeness. Ragu has no `subtle`/`CtOption` usage and no written
  constant-time commitment for the prover; raising it would be proposing a new
  threat-model commitment, not catching a gap.
- Anything requiring a proof digest to exist.

## Acceptance

- `EquivalenceClaim` implemented with **zero changes to `scribe-core`**.
- A committed coverage number over the fleet's **actual** rank and op-limit
  spread (verify it; do not assume TestRank/48 uniformly).
- A versioned `Corpus<EquivalenceClaim>` of 1 positive + 2-3 negatives, run
  through `validate()`, with the `DiscriminationReport` committed.
- At least one mutant in a demonstrably unreached path appearing in `escaped`,
  reproducible from the notes.
- The ragu revision pinned and recorded (origin/main — there is no `upstream`
  remote in this checkout).
- Nothing in this crate times, benchmarks, or optimizes anything.

## Pitfalls

- **Keep the corpus small.** Three entries exercise the core as well as thirty.
  The original six-plus-entry scope was invalidated; resist rebuilding it because
  it feels more impressive.
- **Do not assert the coverage gap before measuring it.** Report at the strength
  the evidence supports — hypothesis until the number exists.
- **Do not claim ragu lacks oracle validation.** It has `PATCHER_SELFTEST` and
  vacuity telemetry. The claim is narrower: that discipline has not been applied
  to input-size coverage.
- **Pin `origin/main`.** There is no `upstream` remote here, and the working tree
  has been behind.
- **If `scribe-core` needs changing, stop and report.** Phase B is watching the
  same contract; a core change requested by one domain is a Phase A defect.

## Agent prompt

See [`kickoff-prompts.md`](kickoff-prompts.md).
