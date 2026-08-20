# v2.1 kickoff prompts

Paste-ready prompts for launching each phase. All assume the agent starts in
`~/experiments/scribe` with the repo checked out.

**Sequencing:** A first, alone. Then B and C **in the same cycle, in parallel**.
D lands incrementally alongside them. Run the gate check between A and B/C.

---

## Phase A — Verdict core (run this first, alone)

```
You are implementing Phase A of the scribe v2.1 roadmap, in ~/experiments/scribe.

Read these three files in order before writing any code:
  roadmap-v2.1.md
  docs/v2.1/README.md
  docs/v2.1/phase-a-verdict-core.md

Implement Phase A: the verdict core.

You own exactly these paths, and must not edit any other file:
  crates/scribe-core/*        (new)
  crates/circuit-ir/*         (new)
  crates/scribe-frontend/*    (new)
  crates/frontend-toml/*      (new)
  crates/gadget-ir/src/lib.rs (deprecation shim only)
  crates/lean-emit/*
  Cargo.toml                  (workspace members)
  schema/circuit-ir-v1.json   (new)

Do NOT edit crates/halva-bridge — it is frozen (locked decision 8).

Two requirements are load-bearing. Everything else is detail.

1. scribe-core must be DOMAIN-INDEPENDENT. Claim::Subject is an associated type,
   not a shared enum — a circuit claim's subject is a CircuitIR, an equivalence
   claim's subject is (reference, candidate, seeds). scribe-core must compile
   with circuit-ir removed from its dependencies. If core mentions constraints,
   fields, or polynomials anywhere, the layering is wrong and you should fix the
   layering rather than the symptom.

2. Verdict has private fields and exactly ONE constructor, taking a
   DiscriminationReport. No Default, no From<Outcome>, no builder that defaults
   it. Ship a compile-fail test (trybuild or equivalent) proving a Verdict cannot
   be constructed without discrimination data. This is the product thesis
   expressed as a type — do not add convenience escape hatches, and if a later
   phase asks for one, that request is the bug.

Phases B and C will be built against these signatures in parallel, so treat the
trait definitions in roadmap-v2.1.md's architecture contract as a fixed contract.
If you need to deviate from them, stop and report it rather than improvising.

The locked decisions in roadmap-v2.1.md are resolved. Implement them; do not
relitigate. If you believe one is wrong, say so and stop — do not silently
implement the alternative.

Before reporting done, run in this order and paste the actual output:
  cargo fmt --all
  cargo clippy --workspace --all-targets -- -D warnings
  cargo test --workspace
  cd lean && lake build

Report:
  1. What you built, in two sentences.
  2. Test count delta (before -> after).
  3. Confirmation that scribe-core compiles with circuit-ir removed.
  4. Anything that contradicted the brief.
  5. Anything you deliberately left out, and why.

Do not report done if any verification command fails. Report the failure with
its output instead.
```

---

## Gate check — run between A and B/C

```
Phase A of the scribe v2.1 roadmap reports complete, in ~/experiments/scribe.

Read roadmap-v2.1.md and docs/v2.1/phase-a-verdict-core.md, then audit the
Phase A implementation against its acceptance criteria. Do not fix anything —
report findings only.

Check specifically:

1. Does crates/scribe-core compile with circuit-ir removed from its
   dependencies? Actually try it, do not read the Cargo.toml and assume.
2. Is there any path to constructing a Verdict without an EXPLICIT statement of
   measurement status? Note the reconciled contract: Verdict::new takes
   Discrimination = Measured(DiscriminationReport) | Unmeasured { reason }, and
   Unmeasured is deliberately legal — nothing could bootstrap otherwise. So the
   question is NOT "can a Verdict exist without a report" (it can, by design) but
   "can one exist without saying which". Look for Default, From, builders, pub
   fields, #[cfg(test)] escape hatches, and any convenience constructor. Also
   confirm UnmeasuredReason is a CLOSED enum, not a String — a free string
   readmits reason: "TODO", which is the erosion this rule exists to block.
3. Does scribe-core reference any circuit-specific concept in its TYPES,
   DEPENDENCIES, or public API NAMES? (Doc comments may use circuits
   illustratively provided at least one non-circuit domain appears alongside;
   a doc block that presupposes circuits is a smell, not a hard fail.)
4. Does frontend-toml produce byte-identical Lean to the pre-refactor path for
   every gadget in examples/? Verify against git history, not against the
   snapshot files the same commit introduced.
5. Do scribe refute and scribe judge still work end-to-end on
   examples/range-check/gadget.toml?
6. Run: cargo fmt --check, cargo clippy --workspace --all-targets -- -D warnings,
   cargo test --workspace, and cd lean && lake build.

Report each as PASS or FAIL with evidence. If any of 1-3 fails, say clearly that
Phases B and C must not start — those three are the abstraction, and building two
instances against a broken core wastes the cycle that is supposed to validate it.
```

---

## Phase B — Instance 1: circuits via Lean (parallel with C)

```
You are implementing Phase B of the scribe v2.1 roadmap, in ~/experiments/scribe.

Read these three files in order before writing any code:
  roadmap-v2.1.md
  docs/v2.1/README.md
  docs/v2.1/phase-b-instance-circuits.md

Implement Phase B: the first instance of scribe's verdict core — circuit
soundness adjudicated by the Lean kernel, over circuits extracted from ragu.

You own exactly:
  crates/frontend-ragu/*   (new)
  crates/oracle-lean/*     (new)
  corpus/circuits/*        (new)
  docs/v2.1/ragu-notes.md  (new)

Phase A must already be green. Phase C is being built in parallel against the
same scribe-core contract. If you find yourself needing to change scribe-core,
STOP and report it — that is a Phase A defect and a signal the abstraction is
wrong, not something to work around locally. This is the single most important
signal this phase produces.

Phase A landed with two signature deltas from the roadmap sketch; build against
these, not the sketch:
  - Verdict::new(outcome, discrimination: Discrimination) where
    Discrimination = Measured(DiscriminationReport) | Unmeasured { reason }.
  - Definition carries id: usize, sharing the variable id space. Term.vars holds
    ids, so definitions must be referenceable by id.

Also know: lean-emit's decomposed mode falls back to the plain scaffold whenever
definitions are present. Extracted ragu IR ALWAYS carries definitions (add() is
free unlimited fan-in and used liberally), so decomposed mode will silently
disable itself on every ragu circuit. Do not work around this in your crate —
report how often it bites and let it be filed as a Phase A follow-up.

Approach: implement ragu's Driver trait with MaybeKind = Empty, recording
gates, definitions, and constraints into a CircuitIR. The ragu checkout is at
~/ragu — read crates/ragu_core/src/drivers.rs and
crates/ragu_circuits/src/metrics.rs first. metrics.rs is a working precedent for
a structure-only driver. Pin and record the ragu revision you build against; do
not rely on a stale local checkout.

Do not skip VISIBILITY extraction. Constraint extraction alone puts every wire in
CircuitIR.private, leaving the public/private split dead and the soundness
theorem subtly wrong. Circuit::Output is ragu's "public instance, serialized into
the k(Y) instance polynomial that the verifier checks", and Circuit::instance()
returns it without needing witness data — run instance() for `public`, witness()
for the full constraint set, and assert public is a subset of what witness()
allocated. Document the mapping in ragu-notes.md.

CRITICAL: gate() imposes TWO constraints, A·B = C and C·D = 0. Driver::mul hides
the D wire, so this is the natural thing to miss. Dropping C·D = 0 yields an IR
weaker than the circuit, which makes any soundness proof against it prove the
wrong thing. Validate your extraction by comparing gate and constraint counts
against ragu_circuits::metrics on the same circuit, and fail hard on
disagreement.

Also promote benchmark/suite.toml's five negative gadgets into a real
Corpus<CircuitClaim> and run validate(LeanOracle, corpus). All five must be
caught. If one escapes, report it loudly — do not tune the corpus until it passes.

Target one ragu_primitives gadget (boolean.rs suggested) through to a
kernel-accepted proof, with #audit_axioms showing only propext, Classical.choice,
Quot.sound. Do NOT write specs for tachyon relations — that code is being
rewritten upstream and specs against it would be wasted. A tachyon extraction
smoke test (does it extract without error) IS in scope.

Before reporting done, run and paste the actual output:
  cargo fmt --all
  cargo clippy --workspace --all-targets -- -D warnings
  cargo test --workspace
  cd lean && lake build

Report:
  1. Did this domain require ANY change to scribe-core? (most important answer)
  2. What you built, in two sentences.
  3. Test count delta.
  4. The ragu revision you pinned.
  5. The DiscriminationReport.
  6. Anything in ragu's driver API that did not match this brief.
```

---

## Phase C — Instance 2: MSM coverage escape (parallel with B)

> Rewritten 2026-08-18. A red-team audit of ragu at fc61822c invalidated three
> premises of the original Phase C. This prompt reflects the narrowed scope.

```
You are implementing Phase C of the scribe v2.1 roadmap, in ~/experiments/scribe.
The ragu checkout is at ~/ragu.

Read these three files in order before writing any code:
  roadmap-v2.1.md
  docs/v2.1/README.md
  docs/v2.1/phase-c-instance-equivalence.md

Read the brief's "What the audit killed" section carefully. An earlier version of
this phase proposed a broad broken-backend corpus graded by proof-digest
equality. Three of its premises were false, and you must not rebuild it:

  - There is NO proof digest. ragu_pcd's Proof<C, R> derives only Clone — no
    PartialEq, no serializer (issue #660 open). Compare at the MSM boundary
    instead, which is one of the narrow boundaries Tal names in #834 comment
    5320700832.
  - Floor planning is NOT an escape. floor_plan() is a prefix sum with no
    proposal mechanism and no validation surface. Do not target it.
  - ragu ALREADY practices planted-defect oracle validation — PATCHER_SELFTEST
    in qa/fuzz/src/record.rs plus vacuity telemetry. Never write or imply that
    ragu lacks this discipline. We are extending it to a surface it has not
    covered, not introducing it.

You own exactly:
  crates/oracle-differential/*      (new)
  corpus/msm/*                      (new)
  docs/v2.1/equivalence-notes.md    (new)

Phase A must be green. Phase B is being built in parallel against the same
scribe-core contract. If you need to change scribe-core, STOP and report it —
that is a Phase A defect and the single most important signal this phase
produces.

Phase A landed with two signature deltas from the roadmap sketch; build against
these: Verdict::new(outcome, discrimination: Discrimination) where
Discrimination = Measured(DiscriminationReport) | Unmeasured { reason }; and
Definition carries id: usize.

THE TARGET. ragu_arithmetic::util::msm selects its window strategy via
bucket_lookup(n), a 15-entry threshold table spanning n up to roughly 3.2M.
Different n take structurally different code paths — bucket counts,
window-boundary shift/limb arithmetic, Bucket::{None, Affine, Projective}
transitions.

Most of the fuzz fleet runs TestRank = R<7> and Limits::default() is
max_ops: 48. But do NOT repeat the claim that the ENTIRE fleet does — that is
false and was caught in review: fuzz_verify_reject.rs declares
type R = ProductionRank, fuzz_witness_pinning.rs caps at max_ops: 16, and other
targets vary. Verify the real spread before writing any number down.

The HYPOTHESIS you are testing — not a premise you may assert — is that a defect
confined to a large-n window path is unreached by the circuit generation the
fleet actually performs, and would therefore be invisible to #834's phase 4 as
specified. Replaying RNG fixes the randomness; it does nothing about a generator
that never reaches production sizes. fuzz_verify_reject running at ProductionRank
is the obvious thing that could falsify this. Report at the strength your
evidence supports.

DELIVERABLE — a measurement plus a SMALL corpus. Target two days.

Phase C's job in the roadmap is to be the second instance that exercises the
WHOLE core. A coverage number alone touches only Claim::Subject, the easy half.
You must also run Corpus, validate(), and Verdict — otherwise this phase does not
test the product thesis. Keep the corpus small: three entries exercise every
trait as well as thirty.

  1. EquivalenceClaim at the MSM boundary. Subject is
     { reference, candidate, inputs } — deliberately nothing like a CircuitIR.
     If this compiles without touching scribe-core, the Phase A abstraction is
     real. That answer outranks shipping the phase.
  2. Measure what fraction of msm's branch paths the fuzz fleet actually reaches,
     across its real rank and op-limit spread. Use the existing fuzz substrate;
     do not build a new generator. Report a number with methodology.
  3. Build corpus/msm/ as a versioned Corpus<EquivalenceClaim>: ONE positive (the
     unmutated reference, which must be accepted) and TWO OR THREE negatives
     (mutants, at least one planted in a demonstrably unreached path). Run
     validate(DifferentialOracle, corpus) and commit the DiscriminationReport.
     The unreached-path mutant should appear in `escaped` — that is the finding,
     and having it emerge from the same validate() machinery Phase B uses is what
     proves the core generalizes.

Keep crates/oracle-differential boringly thin: compare outputs, accept iff all
match, Undetermined on panic (a crash is not proof of inequivalence). The
interesting work is the measurement.

OUT OF SCOPE. Performance benchmarking or timing anything — if you measure
speed you have drifted into building ragu's harness instead of grading it.
Floor planning, s(X,Y), and registry evaluation are not externally mutable and
are under active restructuring in PR #503. Constant-timeness — ragu has no
subtle/CtOption usage and no written constant-time commitment for the prover, so
raising it would propose a new threat-model commitment rather than catch a gap.

Pin origin/main and record the revision. There is no `upstream` remote in the
ragu checkout, and the working tree has been behind before.

Before reporting done, run and paste the actual output:
  cargo fmt --all
  cargo clippy --workspace --all-targets -- -D warnings
  cargo test --workspace

Report:
  1. Did this domain require ANY change to scribe-core? (most important answer)
  2. The coverage number, with methodology, and the fleet's actual rank spread.
  3. The corpus, the committed DiscriminationReport, and which mutant escaped.
  4. The ragu revision you pinned.
  5. Anything in the audit findings above that you found to be wrong.
```

---

## Builder continuation — Phase A hardening + Phase D (D2/D3/D4)

For the agent that implemented Phase A. It must NOT take Phase B or C — it
designed scribe-core, so either instance would fit trivially and destroy the
independence signal locked decision 3 exists to produce.

```
Continue scribe v2.1 work in ~/experiments/scribe. You implemented Phase A last
session. This is the post-audit hardening plus the Phase D items that do not
depend on Phases B or C.

Do NOT take Phase B or Phase C. You designed scribe-core, so either instance
would fit it trivially and destroy the independence signal those phases exist to
produce (roadmap-v2.1.md, locked decision 3). They go to fresh agents.

Re-read roadmap-v2.1.md first. Its architecture contract was reconciled after a
review audit: the Verdict signature, Definition.id, Phase A ownership, and Phase
C's scope all changed. The contract in that file is now single-sourced — build
against it, not against anything in git history or your own memory of last
session. Then read docs/v2.1/phase-d-devex.md.

## Part 1 — Phase A hardening (you own scribe-core as its author)

1. Harden Discrimination::Unmeasured. Its `reason` must become a closed enum —
   UnmeasuredReason = NoCorpusDefined | CorpusEmpty | ValidationSkipped — not a
   free String. A free string readmits `Unmeasured { reason: "TODO" }`, which is
   precisely the erosion locked decision 2 exists to block. Extend the trybuild
   suite if a compile-fail case can express the tightening.

2. Enforce ir_version in CircuitIR::from_json. Reject unknown majors at parse
   time, not by convention. Locked decision 6 is decorative otherwise, and both
   D4 caching and G5 third-party adapters depend on the field meaning something.

3. Make the schema test validate an INSTANCE against schema/circuit-ir-v1.json,
   not merely compare top-level property names. Add negative tests: an invalid
   ir_version, and a malformed SourceSpan.

4. File the decomposed-mode fallback as a documented A-follow-up in docs/v2.1/ —
   NOT as a GitHub issue; I file my own. State it precisely: lean-emit's
   decomposed mode falls back to the plain scaffold whenever definitions are
   present; nothing in examples/ hits that path, but extracted ragu IR always
   carries definitions because ragu's Driver::add is free unlimited fan-in and
   used liberally. So decomposed mode will silently disable itself on every ragu
   circuit — exactly where hard proofs need it most. Include what a fix would
   involve (restating the let chain per helper lemma, or hoisting definitions
   into a shared context) so Phase B's report can be read against it. Do NOT fix
   it now; Phase B needs to measure how often it actually bites first.

5. Revert the whitespace-only diff in crates/scribe-cli/src/golf.rs. It is
   pre-existing fmt drift you did not author and it should not ride along in the
   Phase A change.

## Part 2 — Phase D, items D2/D3/D4 only

You own exactly:
  crates/scribe-macros/*    (new, only if D2 needs it)
  crates/scribe-cli/src/*
  crates/bench/src/main.rs
  benchmark/suite.toml

Skip D1 (the extract! macro needs frontend-ragu, which is Phase B) and D5
(corpus tooling needs the corpora B and C produce). Do D2 first — it is the
highest-leverage item in the phase.

  D2 — Diagnostics cite the source circuit. Use the Constraint.origin spans you
  added in Phase A. When a proof stalls, render `spend.rs:92 —
  enforce_zero("nullifier binding")`, not `h_c47`. Map generated Lean hypothesis
  names back to source spans in both the terminal failure path and NOTES.md. An
  engineer who has never written Lean should be able to read the output.

  D3 — `scribe check`: a fast tier that NEVER requires an API key. Extraction
  succeeds, IR validates against the schema (real validation, per Part 1 item 3),
  spec is syntactically valid Lean, C1-C3 pass. Requiring lake build is fine;
  requiring a model is not. Exit codes follow the existing judge convention
  (0 SOUND / 1 UNDETERMINED / 2 UNSOUND / 3 infra) — do not invent a new scheme.

  D4 — Fingerprint caching on canonical CircuitIR JSON, excluding
  provenance.source_rev. The fingerprint MUST cover the spec as well as the
  constraints, so editing a spec invalidates the cache. Cache lives in
  target/scribe/. Proofs stay committed — they are the evidence.

While in scribe-cli, make every verdict render its discrimination status,
including when unmeasured. Never print a bare ACCEPT. `ACCEPT (oracle
unmeasured: no corpus defined)` should look uncomfortable — that discomfort is
locked decision 2 reaching the UI.

Guiding benchmark for every DevEx decision: not "a verification specialist can
use this" but "a protocol engineer who has never written Lean can run it on
their own circuit and understand the output."

## Rules

- Ship each item separately with tests, not as one large change.
- Do NOT commit or push anything. The branch carries my unrelated pending
  changes. Leave the tree dirty and give me the git commands to run myself.
- If you need to change scribe-core for a Phase D reason, that is suspicious —
  report it rather than doing it. Phases B and C are being measured on exactly
  that question right now.

Before reporting done, run and paste the actual output:
  cargo fmt --all
  cargo clippy --workspace --all-targets -- -D warnings
  cargo test --workspace
  cd lean && lake build

Report:
  1. The Unmeasured hardening and the ir_version/schema enforcement.
  2. Which of D2/D3/D4 you completed.
  3. Test count delta.
  4. Measured timing for `scribe check` on a cached circuit.
  5. The git commands for me to run.
```

---

## Phase D — DevEx (incremental, alongside B and C)

```
You are implementing Phase D of the scribe v2.1 roadmap, in ~/experiments/scribe.

Read these three files in order before writing any code:
  roadmap-v2.1.md
  docs/v2.1/README.md
  docs/v2.1/phase-d-devex.md

Implement Phase D: developer experience.

You own exactly:
  crates/scribe-macros/*    (new)
  crates/scribe-cli/src/*
  crates/bench/src/main.rs
  benchmark/suite.toml

Phase A must be green. Items D1-D5 are independently shippable — do them one at
a time, each with tests, rather than as one large change. D2 (source-cited
diagnostics) is the highest-leverage item; if you only do one, do that.

Guiding benchmark for every decision: not "a verification specialist can use
this" but "a protocol engineer who has never written Lean can run it on their own
circuit and understand the output."

Constraints:
- scribe check must NEVER require an API key. Requiring lake build is fine.
- Exit codes follow the existing judge convention (0 SOUND / 1 UNDETERMINED /
  2 UNSOUND / 3 infrastructure error). Do not invent a new scheme.
- The exit-2 soundness alarm in crates/bench must not weaken. Re-expressing it
  on top of scribe-core's validate() is the goal; changing what happens when a
  negative is proved is not.
- Fingerprint caching must cover the spec as well as the constraints, so that
  editing a spec invalidates the cache.
- Every verdict the CLI prints must show its discrimination status, including
  when it is unmeasured. Never render a bare ACCEPT. "ACCEPT (oracle
  unmeasured)" should look uncomfortable — that discomfort is the product
  thesis reaching the UI.

Before reporting done, run and paste the actual output:
  cargo fmt --all
  cargo clippy --workspace --all-targets -- -D warnings
  cargo test --workspace

Report:
  1. Which of D1-D5 you completed.
  2. Test count delta.
  3. Measured timing for scribe check on a cached circuit.
  4. Anything that contradicted the brief.
```
