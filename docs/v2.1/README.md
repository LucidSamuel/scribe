# v2.1 agent guide

How to pick up and execute a v2.1 phase. Read this, then `roadmap-v2.1.md`,
then your phase brief.

## Before you write code

1. Read `roadmap-v2.1.md` in full — especially **Locked decisions**. They are
   resolved. If you think one is wrong, stop and say so; do not silently
   implement the alternative.
2. Read your phase brief in this directory.
3. Read `docs/architecture.md` — and note that it describes the *intended* v1
   architecture, which v2.1 is making true. Where it disagrees with
   `roadmap-v2.1.md`, the roadmap wins.
4. Check file ownership. If your change requires editing a file another phase
   owns, that is a handoff, not a workaround. Say so and stop.

## Ground rules

- **`scribe-core` is domain-independent.** It must compile with `circuit-ir`
  removed from its dependencies. If core mentions constraints, fields, or
  polynomials, the layering is wrong (locked decision 1).
- **A change to `scribe-core` requested by one domain is a Phase A defect.** Stop
  and report it; do not work around it locally. Phases B and C are deliberately
  built against the same contract in parallel so that this shows up.
- **Do not widen `CircuitIR` to fit an ecosystem.** If your adapter cannot
  express something in its vocabulary, narrow the adapter (locked decision 7).
- **Never construct or render a verdict without its discrimination status.**
  Locked decision 2. There is no convenience constructor, and adding one defeats
  the product.
- **Do not break existing tests.** v2 shipped 58+ tests. The count goes up, never
  down. If a test must change shape, explain why in the PR body.
- **No `sorry`, `axiom`, or `native_decide` in any Lean you generate or commit.**
  The `#audit_axioms` gate is the source of truth; textual scans are a
  pre-filter. This is not negotiable and CI enforces it.
- **Deprecate, don't delete.** `gadget-ir` stays as a re-export shim for one
  release. Downstream code should keep compiling through the refactor.
- **Every phase ships tests.** A phase without tests is not done. See "Definition
  of done" in the roadmap.

## Verification (run all three, in order, before reporting done)

```sh
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
```

If your phase touches Lean:

```sh
cd lean && lake build      # must exit 0 with no warnings
```

## Reporting

When you finish, report:

1. What you built, in two sentences.
2. Test delta (before → after count).
3. Anything you hit that contradicts a locked decision or a brief.
4. Anything you deliberately left out and why.

Do not report done if any of the three verification commands fails. Report the
failure instead, with the output.

## Kickoff prompts

Paste-ready launch prompts for every phase, plus the A→B/C gate check, live in
[`kickoff-prompts.md`](kickoff-prompts.md).

## Phase order

A, then **B and C in the same cycle**, with D landing incrementally.

Phase A is the hard dependency. Do not start B/C/D against a half-built Phase A —
wait for the architecture contract to compile green.

B and C are deliberately parallel. They are two instances in *different domains*
— circuits adjudicated by the Lean kernel, and implementations adjudicated by
differential replay — and they exist to test whether `scribe-core` is a real
abstraction or a Lean-shaped hole wearing a generic name (locked decision 3).
One instance cannot answer that. If B and C cannot share the core without
special cases, the core is wrong and gets rewritten, not patched — and finding
that out is a successful outcome for the cycle.

The most important line in either phase's final report is the same question:
**did this domain require changing `scribe-core`?**
