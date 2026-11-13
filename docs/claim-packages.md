# Claim packages: first implementation

Scribe can seal generic protocol claim metadata and local evidence files:

```sh
cargo run -p scribe-cli -- claim seal \
  --package examples/claims/package.json --root examples/claims
```

The JSON envelope on stdout contains the package and its SHA-256. Failures exit
with code 3. Success means metadata and artifact integrity checks passed; it is
not a SOUND verdict. The example is deliberately marked unchecked.

Version 1 records a full source revision, toolchain declaration, string-valued
parameters, named artifacts with SHA-256 fingerprints, Lean declarations and
statements, declared trust modes and axioms, heuristics, and a cost ledger.
Dependency files and target profiles belong in the artifact map. Heuristics
require unique IDs, scope, evidence artifact references, and limitations. Costs
require unique IDs, scope, units, evidence references, and unsigned integer or
rational quantities (decimal strings, such as "42" or "3/2"). Extrapolated costs
can record their rule. This version cannot determine whether all relevant costs
or heuristics were disclosed or whether an extrapolation is justified.

Paths are relative to the supplied root. Traversal, absolute paths, and symlinks
escaping that root are rejected. All referenced artifacts are rehashed. The seal
hashes compact serde JSON serialization of the typed package: map keys are sorted,
array order is significant. This is a version-specific serialization, not a
general JSON canonicalization standard or a signature. Keep evidence immutable
while sealing; it does not snapshot files or defend against concurrent changes.

Trust modes are declarations, not verified facts. The seal command does not
run Lean, match a proposition to its source, audit axioms, validate source revision
provenance, establish cost bounds, or run a committee. A seal has private fields
and no Deserialize implementation so Rust callers must pass validation to obtain
one; untrusted JSON envelopes still need independent validation.

## Verify theorem statements with Lean

```sh
cargo run -p scribe-cli -- claim verify \
  --package examples/claims/poseidon-sbox.json --root . --lake-dir lean
```

This example checks Scribe's existing x^5 S-box gadget, not the Orchard
permutation or a collision. Verification builds the proof modules, parses each
package statement as a single Lean term, binds it to the named theorem, sends
the binding through the kernel, and checks actual transitive axioms against
both the package declaration and the trusted allowlist. A successful JSON
receipt includes the sealed package, probe, build transcript, toolchain, and
Scribe's environment fingerprint. Failure exits 3 without emitting a receipt.

This first verifier accepts closed theorem declarations without universe
parameters. Artifact sources must be inside the Lake project, with ASCII module
paths. The toolchain declaration must match lean-toolchain exactly. Unchecked
metadata can be verified without rewriting its declaration; native_decide claims
are rejected by this kernel-only path. Heuristics, costs, provenance, and the
meaning of the target specification remain outside the check.

Use this command only with trusted local Lean projects and sources: Lean
elaboration can execute code. Receipts are local run records, not signed
certificates or independently trusted verdicts. Re-run verification when
consuming an untrusted receipt. The environment fingerprint covers local Lean
sources, the toolchain and manifest; it is not a hermetic dependency snapshot
and does not hash compiled dependencies or toolchain binaries. Pre/post checks
reject observed input changes but do not provide filesystem snapshot isolation.

Run the real-kernel rejection suite after building the CLI:

```sh
cargo build -p scribe-cli
python3 scripts/test-claim-verification.py
```

## HashSmash follow-up gates

The organizer profile, constants, resource model, scoring policy and claim
schema are now pinned. The Orchard model includes a kernel-checked reference
vector, canonical encoding checks, and a baseline polynomial degree bound.
Verify its example package with:

```sh
cargo run -p scribe-cli -- claim verify --package examples/claims/orchard-model.json --root . --lake-dir lean
```

See [the candidate audit](hashsmash-audit.md) for the submitted package's status,
two concrete issues, and unresolved heuristic obligations. The model package
does not certify the attack, skipped-round claims, or its score.

Remaining work:
1. Resolve the candidate's finite-cost and gcd-termination findings.
2. Bind organizer experiment reports and judge prompts into portable evidence.
3. Implement organizer export and check against the pinned organizer validator.
4. Add the paired-lanes review dossier with heuristic-level findings.
5. Prove the two-round parametrization and check a real full-output collision
   when a witness is available.

Attack construction stays in poseidon-smash. No organizer submission or external
publishing is performed by this command.

## Recursive cost correction

The separate `examples/claims/orchard-accounting.json` package binds four
kernel-checked results: the correction recurrence's closed form, its sum over
the transcribed outer-call schedule, the revised total, and added code bytes.

```sh
python3 scripts/audit-orchard-accounting.py
cargo run -p scribe-cli -- claim verify --package examples/claims/orchard-accounting.json --root . --lake-dir lean
```

The Python audit independently evaluates the recurrence and closed form, then
uses 80-digit decimal arithmetic to project the five-decimal score. The Lean
package proves integer arithmetic only. The schedule and prices remain inputs;
neither check proves that an implementation follows them or that the full cost
ledger is complete. The example source revision records the base commit;
artifact hashes identify the proof bytes added after that revision.
