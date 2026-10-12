# Polynomial evaluation corpus

This package checks a small protocol-facing algebraic contract: two polynomials
that agree on more **distinct** points than either degree are equal. It reuses
Mathlib's polynomial definitions and root-count theorem. It is a building block
for Reed–Solomon codeword uniqueness, not a proximity-gap result, a probabilistic
identity-test bound, or Ragu protocol soundness.

Run from the repository root:

```sh
python3 scripts/validate_protocol_corpus.py
```

The validator builds the fixed Lean reference evidence, then separately checks
that the exact statements in `manifest.json` have those proofs or refutations.
It audits transitive axioms using scribe's existing allowlist. A timeout reports
`budget_exhaustion`; a build/elaboration/process error reports `tooling_failure`.
Neither is counted as a negative detected. `kernel_checked` reports fixed
reference evidence, **not** model performance or an oracle detection rate.

Six positive statements form the dependency family: evaluation subtraction,
nonzero difference, difference degree, agreement implies a root, finite root
count, and uniqueness. Each has a matched false mutation with a checked finite
counterexample over `ZMod 5`. Additional final-claim negatives remove the
right-hand polynomial's degree bound and incorrectly count repeated samples.
The zero polynomial and zero-degree boundary are included in those witnesses.

Both direct library and decomposed proofs of the final contract are checked.
The six-root pilot must use only the manifest prefix, not import the reference
proofs. Even then Mathlib already contains the answer and related lemmas; this
is disclosed retrieval/proving work, not a contamination-free difficulty test.
All six roots are related, so they are not six independent protocol families.

The Rust refinement work lives separately in `ZkGadgets.Refinement.RaguHorner`.
It concerns an extracted Horner constraint model. This package does not convert
that into an end-to-end Rust semantic extraction claim or prove Ragu's verifier.
