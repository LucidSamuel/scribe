# Scribe v2.1 Roadmap

Status: not started (spec written 2026-08-18, re-architected same day). This file
is the durable, authoritative spec for the v2.1 work, in the same contract style
as `roadmap-v2.md`. Agents implementing phases MUST read this file and
`docs/v2.1/README.md` first, then their own phase brief in `docs/v2.1/`.

v2 made scribe work end-to-end for one ecosystem and one proof technique. v2.1
re-centers scribe on the thing that is actually differentiated — **validated
acceptance oracles** — and proves the architecture against two live instances in
different domains.

## What scribe is, restated

Scribe is not "an LLM that writes Lean proofs." That capability is commoditizing
and will be done better elsewhere.

Scribe is the answer to a question almost nobody asks about their own tooling:
**when your check says PASS, can you show that it was capable of saying FAIL?**

Everything differentiated in this repo is already that move:

- `#audit_axioms` — the proof cannot smuggle in `sorry` / `native_decide`.
- C1 (`#audit_uses` / `#audit_requires`) — the hypotheses are load-bearing.
- C2 (`#audit_falsifiable`) — the conclusion is refutable at a finite model.
- C3 (`#audit_satisfiable`) — the constraints are satisfiable.
- C4 (`scribe refute`) — an adversary hunted for a counterexample and failed.
- `benchmark/suite.toml` — known-bad gadgets the loop must FAIL to prove; a
  proved negative exits 2 as a soundness alarm.

None of that is Lean-specific in *concept*. All of it is Lean-specific in *code*.
v2.1 fixes exactly that gap.

## The problem v2.1 fixes

Two problems, one root cause.

**1. The verdict engine cannot reach real work.** `scribe refute` and
`scribe judge` both take *"Gadget IR file (TOML)"*. `crates/halva-bridge` depends
on `proof-pilot` only — not on `gadget-ir` or `lean-emit` — and carries its own
types and emitters; the zkGolf path bypasses both. So scribe's most
differentiated machinery runs only on hand-written toy gadgets.

**2. The architecture admits exactly one oracle.** `proof-pilot` hardcodes
"run lake build, parse Lean errors." There is no way to plug in a different
acceptance procedure, which means whole classes of cryptographic assurance
problems are unreachable — including the one in front of us
([ragu #834](https://github.com/tachyon-zcash/ragu/issues/834), AI-assisted
prover optimization, whose phase 4 is precisely an unvalidated acceptance
oracle).

Root cause: scribe's spine is a Lean-proof-of-a-circuit pipeline. The spine
should be the oracle-validation core, with Lean-proof-of-a-circuit as one
instance of it.

## Goals (G1–G5)

- **G1 Verdict core.** `Claim` / `Oracle` / `Corpus` / `Verdict` as the spine.
  A `Verdict` cannot be constructed without an explicit `Discrimination` — a
  measured `DiscriminationReport`, or a typed `Unmeasured` status from the
  closed `UnmeasuredReason` enum.
- **G2 Two live instances, different domains.** Lean-kernel oracle over ragu
  circuits, and a differential-equivalence oracle over prover implementations
  (#834). The abstraction is earned by both, not designed for either.
- **G3 Ragu extraction with no per-circuit adapter.** `frontend-ragu` reaches
  every ragu and tachyon circuit through the `Driver` trait.
- **G4 DevEx.** Extraction is a `cargo test`. Diagnostics cite source lines, not
  Lean hypothesis names. A fast no-LLM tier. Fingerprint caching.
- **G5 Third-party extensibility.** A new domain is a new `Oracle` + `Corpus`
  pair; a new circuit ecosystem is a new `Frontend`. Neither requires changes to
  scribe core.

## Locked decisions

Resolved. Implement them; do not relitigate. Raise an issue if you believe one is
wrong.

1. **The spine is the oracle-validation core, not an IR.** `Claim`, `Oracle`,
   `Corpus`, `Verdict`, `DiscriminationReport`. `CircuitIR` is the subject type of
   *one* claim kind, not the center of the system. An abstraction that only makes
   sense for polynomial constraints does not belong in core.

2. **A `Verdict` is unconstructible without an explicit `Discrimination`.**
   Enforce in the type system, not by convention. An oracle that has never been
   measured against known-bad instances reports `Discrimination::Unmeasured`
   with a reason from the closed `UnmeasuredReason` enum (a free string would
   readmit `reason: "TODO"`), and the CLI renders that as prominently as the
   outcome itself. This single rule is the product thesis; do not weaken it for
   convenience.

3. **The abstraction must be earned by two instances in different domains,
   built in the same cycle.** Phase B (Lean/circuits) and Phase C (differential/
   implementations) are not sequential nice-to-haves — they are the two data
   points that determine whether the core is real. If they cannot share the core
   without contortion, the core is wrong and gets rewritten, not patched.

4. **Scribe hosts and grades oracles; it does not implement other people's
   acceptance procedures.** And it does not claim to *introduce* the discipline:
   ragu already runs `PATCHER_SELFTEST` (a planted defect its oracle must catch)
   and vacuity telemetry in `qa/fuzz`. The honest claim is that we generalize a
   practice across domains and apply it to surfaces its author has not covered —
   never that a host project lacks it. Check before asserting a gap. Scribe does not build ragu's fast-MSM comparison, a
   fuzzer, or an SMT backend. It provides the corpus, the discrimination
   measurement, and the verdict. The differential oracle in Phase C is a thin
   adapter over a comparison the host project owns, plus the corpus that makes
   its green runs mean something. If a phase starts growing a performance
   benchmark or a test runner, it has drifted — stop.

5. **Corpora are first-class, versioned artifacts.** A `Corpus` is not test
   fixtures. It is the evidence that backs every verdict the oracle issues, it
   is versioned, and it grows monotonically. Every confirmed real-world bug
   becomes a corpus entry.

6. **Every extractor and adapter self-validates against the host framework.**
   `frontend-ragu` compares its gate and constraint counts against
   `ragu_circuits::metrics` and fails hard on disagreement. This is the same
   discipline as the corpus, one layer down: the extractor is checked, not
   trusted.

7. **`CircuitIR` carries no ecosystem vocabulary.** No `routine`, `s-polynomial`,
   `floor plan`, `region`, `column`, `selector`, or `row`. Vocabulary is exactly:
   field, public variables, private variables, definitions, constraints,
   provenance, spec. If an adapter cannot express something in it, narrow the
   adapter — do not widen the IR.

8. **Halva is frozen.** It keeps working and is documented as a case study. No
   port to `CircuitIR`, no verdict-engine integration, no further investment.
   It is a halo2 extractor for a framework we do not use, and the three proven
   circuits have already done their job as evidence. Revisit only if a paying
   user needs halo2.

9. **`ragu_pcd` and protocol-level claims are out of scope for v2.1, not
   forever.** Recursion, transcripts, and accumulation need a different proof
   technique and a different claim kind. The core must not *preclude* them —
   a future `ProtocolClaim` with a golden-vector corpus is the natural next
   instance — but nothing in v2.1 targets them.

## Architecture contract (Phase A — the foundation)

```
                    ┌─────────────────────────────────────────┐
   Claim kind  ───→ │  Claim / Subject / Oracle / Corpus       │
                    │  ─────────────────────────────────────   │
   Subject     ───→ │  adjudicate(oracle, claim, subject)      │ ───→ Verdict
                    │  validate(oracle, corpus)                │      + Discrimination
                    └─────────────────────────────────────────┘
                              ▲                    ▲
              ┌───────────────┘                    └──────────────┐
   CircuitClaim (Phase B)                        EquivalenceClaim (Phase C)
   subject: CircuitIR                            subject: (reference, candidate, seeds)
   oracle:  Lean kernel + axiom audit            oracle:  digest comparison, replayed RNG
   corpus:  broken gadgets                       corpus:  broken backends
   LLM:     proof-pilot / refute                 LLM:     optimizer / refute
```

### `crates/scribe-core`

```rust
pub trait Claim {
    type Subject;
    fn kind(&self) -> &'static str;
    fn describe(&self) -> String;
}

pub trait Oracle<C: Claim> {
    fn adjudicate(&self, claim: &C, subject: &C::Subject) -> Outcome;
}

pub trait Corpus<C: Claim> {
    fn negatives(&self) -> Vec<Instance<C>>;  // the oracle MUST reject these
    fn positives(&self) -> Vec<Instance<C>>;  // the oracle MUST accept these
    fn version(&self) -> &str;
}

pub enum Outcome { Accept(Evidence), Reject(Diagnostics), Undetermined(Reason) }

pub struct DiscriminationReport {
    pub corpus_version: String,
    pub negatives_caught: usize,
    pub negatives_total: usize,
    pub escaped: Vec<InstanceId>,     // negatives the oracle wrongly accepted
    pub positives_accepted: usize,
    pub positives_total: usize,
}

pub enum Discrimination {
    Measured(DiscriminationReport),
    Unmeasured { reason: UnmeasuredReason },
}

/// Closed set on purpose. A free-form string readmits `reason: "TODO"`, which is
/// the erosion path locked decision 2 exists to block.
pub enum UnmeasuredReason { NoCorpusDefined, CorpusEmpty, ValidationSkipped }

pub struct Verdict { /* private fields */ }

impl Verdict {
    /// The ONLY constructor. There is no path to a Verdict that omits an
    /// explicit statement of measurement status — see locked decision 2.
    pub fn new(outcome: Outcome, discrimination: Discrimination) -> Self;
}
```

**Phase A landed 2026-08-18.** The signatures above are the *reconciled*
contract — they already incorporate the two deltas Phase A surfaced, and they
supersede any earlier sketch. B, C, and D build against these, not against
anything in git history:

- `Verdict::new` takes `Discrimination`, not `DiscriminationReport`. The earlier
  literal signature made `Unmeasured` unconstructible, contradicting locked
  decision 2's requirement that it be a legal, renderable state. The invariant is
  preserved and sharpened: **no Verdict exists without an explicit statement of
  measurement status.**
- `Definition` carries `id: usize`, sharing the variable id space. `Term.vars`
  holds ids, so a definition without one could never be referenced from a
  constraint, defeating its purpose.

**Known Phase A follow-up.** `lean-emit`'s decomposed mode falls back to the
plain scaffold whenever definitions are present. Nothing in `examples/` hits
that path, but extracted ragu IR frequently carries definitions — ragu's
`Driver::add` is free unlimited fan-in; Phase B measured 1 of 3 extracted
shapes definition-bearing, rising on real gadget libraries — so decomposed
mode silently disables itself on every definition-bearing ragu circuit,
skewing toward exactly the circuits where hard proofs need it most. Not a
blocker for Phase B; filed as A-follow-up F1.

`validate(oracle, corpus) -> DiscriminationReport` runs the oracle over every
corpus instance. An escaped negative is the loudest signal the system can
produce — it means the oracle accepted something known to be wrong, and every
verdict that oracle has ever issued is suspect. Surface it accordingly.

### `crates/scribe-frontend` + `crates/circuit-ir`

Unchanged in shape from the previous draft, but demoted: `CircuitIR` is the
subject type of `CircuitClaim`, not the spine. It grows `public`/`private`
variables (a correctness fix — a soundness statement is meaningless without
knowing what the verifier sees), `definitions` (named linear forms, because
ragu's `Driver::add` is free unlimited-fan-in and inlining explodes), `origin`
spans, `provenance`, and a versioned JSON schema.

`gadget-ir` becomes a deprecated re-export shim for one release.

## Phases

Phase A is a hard dependency. **Phases B and C run in the same cycle** — they are
the two instances that earn the core (locked decision 3). D lands incrementally.

- **Phase A — Verdict core.** `crates/scribe-core`, the four traits, the
  unconstructible-without-discrimination `Verdict`, `validate()`, and the
  `CircuitIR`/`Frontend` plumbing demoted to plugin status.
  Brief: [`docs/v2.1/phase-a-verdict-core.md`](docs/v2.1/phase-a-verdict-core.md)

- **Phase B — Instance 1: circuits via Lean.** `frontend-ragu` (structure-only
  `Driver`, `MaybeKind = Empty`), `LeanOracle`, and the existing negative gadgets
  ported to a real `Corpus`. First proof target: a `ragu_primitives` gadget.
  Brief: [`docs/v2.1/phase-b-instance-circuits.md`](docs/v2.1/phase-b-instance-circuits.md)

- **Phase C — Instance 2: implementations via differential replay.**
  `EquivalenceClaim` at the **MSM boundary**, a thin `DifferentialOracle`, a
  small versioned corpus (reference + mutants) run through `validate()`, and a
  branch-coverage measurement of `ragu_arithmetic::util::msm` across the fuzz
  fleet's actual rank spread — with at least one mutant planted in a
  demonstrably unreached path that the differential misses.
  **Rewritten 2026-08-18 after a red-team audit at ragu `fc61822c` invalidated
  three premises of the original brief** — there is no proof digest to compare
  (`Proof` derives only `Clone`, #660 open), floor planning is a prefix sum with
  no proposal surface, and ragu already practices planted-defect oracle
  validation (`PATCHER_SELFTEST` + vacuity telemetry in `qa/fuzz`). Scope is now
  roughly 20% of the original. Read the brief's "What the audit killed" first.
  Brief: [`docs/v2.1/phase-c-instance-equivalence.md`](docs/v2.1/phase-c-instance-equivalence.md)

- **Phase D — DevEx.** `scribe::extract!`, source-cited diagnostics,
  `scribe check` no-LLM tier, fingerprint caching, corpus tooling.
  Brief: [`docs/v2.1/phase-d-devex.md`](docs/v2.1/phase-d-devex.md)

## File ownership (no two agents touch the same file)

- **A:** `crates/scribe-core/*` (new), `crates/circuit-ir/*` (new),
  `crates/scribe-frontend/*` (new), `crates/frontend-toml/*` (new),
  `crates/gadget-ir/{src/lib.rs, Cargo.toml}` (shim only), `crates/lean-emit/*`,
  root `Cargo.toml`, `Cargo.lock`, `schema/circuit-ir-v1.json` (new).
- **B:** `crates/frontend-ragu/*` (new), `crates/oracle-lean/*` (new),
  `corpus/circuits/*` (new), `docs/v2.1/ragu-notes.md` (new).
- **C:** `crates/oracle-differential/*` (new), `corpus/msm/*` (new),
  `docs/v2.1/equivalence-notes.md` (new).
- **D:** `crates/scribe-macros/*` (new), `crates/scribe-cli/src/*`,
  `crates/bench/src/main.rs`, `benchmark/suite.toml`.

Phase A owns `lean-emit` and the root `Cargo.toml` exclusively. B, C, and D must
not edit either.

`crates/halva-bridge/*` is owned by nobody and must not be edited (locked
decision 8).

## Definition of done

- **A:** `cargo test --workspace` green, test count preserved or higher.
  Compile-fail tests proving `Verdict` cannot be constructed without an
  explicit `Discrimination` (and `Unmeasured` cannot take a free-form reason).
  JSON round-trip + schema. `frontend-toml` reproduces
  today's TOML path byte-for-byte on every gadget in `examples/`.
- **B:** a `ragu_primitives` gadget extracts to `CircuitIR`; counts match
  `ragu_circuits::metrics` exactly; one kernel-accepted soundness proof with
  axioms limited to `propext` / `Classical.choice` / `Quot.sound`; the five
  existing negatives run as a `Corpus` and the oracle catches all five.
- **C:** `EquivalenceClaim` implemented with zero `scribe-core` changes; a
  measured `msm` branch-path coverage number across the fuzz fleet's actual rank
  and op-limit spread; a small versioned `Corpus<EquivalenceClaim>` (reference as
  positive, mutants as negatives) run through `validate()`, with its
  `DiscriminationReport` committed; and at least one mutant in a demonstrably
  unreached path that the differential misses. **Phase C must exercise `Corpus`,
  `validate()`, and `Verdict`** — a coverage number alone tests only
  `Claim::Subject`, which is the easy half of the abstraction.
- **D:** `scribe check` under 5s with no API key on a cached circuit; failed
  proofs cite `file:line`; re-running `judge` on an unchanged circuit hits cache.
- **Cross-cutting:** B and C share `scribe-core` with no domain-specific escape
  hatches. If either needed a special case in core, that is a Phase A defect and
  gets fixed there.

## Non-goals for v2.1

- Any port of, or investment in, the Halva path (locked decision 8).
- Building acceptance procedures scribe does not own — fuzzers, SMT backends,
  performance benchmarks, ragu's own MSM comparison (locked decision 4).
- `ragu_pcd`, recursion, protocol-level claims (locked decision 9).
- Structured specs — `soundness_spec` stays a raw Lean string.
- Tachyon relation proofs. Extraction is churn-safe; specs against
  `stamp/proof/*` are not while that code is being rewritten upstream.
- A second emitter backend. One `Emitter` trait, one Lean implementation.
