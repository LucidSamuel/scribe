# HashSmash Orchard integration and candidate audit

This document combines reproducible Scribe checks with historical observations
from a private competition checkout. The candidate proof, successor package and
719-entry API snapshot are not published here. Their quoted contents, repairs
and ranking cannot be independently reproduced from this repository; treat them
as author observations, not publicly established findings or certificates.
The public, reproducible result is the hash model and arithmetic conditional on
the explicitly transcribed schedule and prices. It does not establish that the
private candidate implements that schedule or achieves the reported score.

The current three-round candidate matches the input package of submission
`424fd2e1-a56b-4a4a-8864-224c95fae4a6`:
`f3151c47514693f0739c59a0284d4eaa12c93b4083f60e44e01d687cb2193021`.
The read-only Yukon observation in
[submission-review.json](../fixtures/hashsmash/orchard/submission-review.json)
records `plausible_not_refuted`, normalized cost 34.34453, status `review`,
`humanAccepted: false` and `formallyVerified: false`. The older submission
`3c3fc3b1-2a77-44c0-917b-27f99de9aeeb` is also in review, at 34.34480.
These are historical observations, not a live status feed or signed receipts.

Organizer setup passed 31 tests and the current candidate passed mechanical
validation. Its certificate manifest is empty. No candidate experiments were
executed during this audit. The frozen advisory packet contains no bound
experiment execution report, which does not imply that the remote organizer
failed to execute them.

## Private-checkout observations to resolve before another submission

One fresh-context, read-only critic inspected the frozen package under all four
initial review rubrics. This was one advisory critique, not four independent
reviews or the official defender/adjudicator committee. The parent independently
checked the two findings below against the exact package bytes.

### Conditional stage-D arithmetic discrepancy

At proof line 89, the recursive node's two-output pointwise pass lists six loads,
two stores, four multiplications and two additions/subtractions, but charges 20
operations. Lines 63 and 91 price each load/store, including address update, at 2.

| Component | Operations |
| --- | ---: |
| Six loads and two stores | 16 |
| Four multiplications | 4 |
| Two additions/subtractions | 2 |
| Total under the stated rules | 22 |

The direct whole-pair plan later in line 89 correctly uses 22. The recursive
node applies this pass on three rows and on two columns of two product rows.
Even just the top nodes of the thirteen budget-65,535 calls at lines 252–264
give `13 × (3 + 2 × 2) × 32768 × 2 = 5,963,776` extra operations under the
listed algorithm; descendants are additional. The declared time ceiling
`279 × 2^27.43338` leaves only about 254,811 operations above the listed
`N_max = 50,567,592,471`.

This is an inconsistency in the finite cost derivation. It needs a corrected
kernel schedule or count, followed by recomputation of row D and all affected
code/memory totals. It does not by itself refute H-ONE or H-NORMAL. This audit
does not publish a corrected score or overwrite the official review.

### Classical-tail zero remainder: algorithm ambiguity

Proof lines 93 and 128 say that a zero remainder in the classical tail ends the
trial in the ABORT discussion. Lines 89 and 241 promise that the tail finishes
and returns a normalized gcd. Ordinary Euclidean termination reaches a zero
remainder and returns the preceding nonzero remainder.

Clarify successful terminal zero versus premature termination inside a budgeted
half-gcd call, including the success path and costs. Until clarified, the written
stopping rule does not unambiguously deliver a gcd to stage E. This is a
specification issue, not an independently established failure of a hidden
implementation.

## Heuristic obligations

H-ONE requires a usable-centre fraction at least 0.3931 at degree 976,562.
The lower-depth rationale and experiments do not establish the full-depth
quantitative bound. H-NORMAL requires abnormal Euclidean sequences to occur with
probability at most 0.001 in the specific structured Graeffe family. A
Schwartz–Zippel calculation for independent random polynomial coefficients does
not transfer that probability to this family.

The probability union bound is coherent conditional on those premises and
successful gcd termination. Its displayed value is approximately
0.390268945312 before negligible corrections, so the floor 0.39026 is
conservative under the premises. Only about 0.0002689 deterioration in either
allowance, with the other fixed, can be tolerated before falling below 0.39.
No counterexample to either heuristic was established by this audit.

The original October strategy's presumed advantages should not be reused as
facts: the current candidate already claims two skipped full rounds, Graeffe
transforms and memory-aware polynomial arithmetic. The new work should address
its actual proof and accounting obligations.

## Scribe model and trust boundary

The organizer constants, r3 profile, cost model, score policy and claim schema
are pinned with file hashes and source revision under
[fixtures/hashsmash/orchard](../fixtures/hashsmash/orchard/manifest.json).
The JSON-to-Lean generator verifies the pin before producing the constants.
The upstream profile's `full_rounds: 56` field is misleading if interpreted as
the number of full rounds; its explicit round-selection text and reference code
define eight full rounds plus r partial rounds. The model follows that explicit
schedule. Likewise the old time-only descriptions in the resource model are
superseded for score projection by the separately pinned time-memory policy.

The Lean model preserves original indices 0–3, 4 through 3+r, and 60–63;
capacity 2^65; the deployed MDS/constants; exponent 5; and coordinate-zero
output. Its byte API enforces exactly 64 input bytes, canonical input elements,
and 32-byte little-endian output. The model supports r=0..56 for testing;
that is separate from live competition admission.

Differential testing compares the Lean integer and byte interfaces against the
hash-pinned organizer verifier for 1,025 vectors: 1,000 seeded random inputs
across all 57 supported round counts, 20 boundary vectors, and five rejection
cases. Malformed byte lengths are checked separately. This is executable
conformance evidence, not a proof of program equivalence.

A zero-input r3 vector is kernel-checked with `decide`, and the schedule and
noncanonical-input rejection lemmas are axiom-audited. Polynomial lifting
provides a baseline degree bound; it does not prove the candidate's two-round
skip, the heuristic probability bounds, attack cost, or a collision.

Next steps are to resolve the two candidate findings, obtain package-bound
organizer experiment evidence, formalize the exact two-round parametrization,
and extend the generic claim interface to organizer-compatible certificates and
a review dossier. The candidate checkout has not been modified by this work.

## Successor accounting work — 2026-11-14

The local successor is at
the separate `hashsmash-successor/pareto` checkout, branch
`orchard-accounting-successor`. Only candidate files were revised. Organizer
setup passed 31 tests before editing; the unchanged copied package matched the
submitted package hash. The revised package passes structural validation as
**draft**, hash `fb6aef0baff9a7b17b86293f1a6e7fbfc20b32fec6ba590f60579742580c50cf`.
The original candidate still validates with its original hash
`f3151c47514693f0739c59a0284d4eaa12c93b4083f60e44e01d687cb2193021`.

`scripts/audit-orchard-accounting.py` performs only independent arithmetic on
the published schedule; it does not load or execute participant code.
The recursive correction is Delta(6)=0 and
Delta(j)=2 Delta(j-1)+14*2^(j-1)=7*2^j*(j-6). Across the 28 outer calls it adds
66,732,288 operations. Corrected provisional total: 50,634,324,759 operations,
126,200,636 bytes, rounded time 27.43528, memory 26.91115, score 34.34643.
This does not validate the complete ledger or repair the terminal-zero rule.

The unpublished 719-entry submission snapshot was observed to show our 424fd2e1 entry lowest in
reported cost at three admitted partial rounds (34.34453), awaiting human
acceptance. This is an AI-screened claim, not a certified winning result.
The lowest reported four-round cost was 39.28233; round counts have distinct
profiles and normalization, so extending the attack requires a new argument.

An eighteenth Graeffe step has an incomplete marginal saving of 6,296,325
operations before repricing initialization. Its initial quotient length grows
from 131,407 to 262,479, potentially erasing that saving. The changed structured
pair also needs its own H-NORMAL support. No improvement is established.
The draft proof records this research gate and the unresolved obligations.
No candidate Python ran on the host, and nothing was submitted or pushed.

The correction now also has a Lean model in
`lean/ZkGadgets/Poseidon/Accounting.lean` and a statement-bound example in
`examples/claims/orchard-accounting.json`. The recurrence's closed form, exact
66,732,288-operation sum, revised total and 64 added code bytes are checked by
the kernel. The operation prices and schedule are transcribed model inputs,
not proven properties of the attack. The score projection uses 80-digit Decimal
arithmetic in the Python script and is not part of the Lean theorem.

## Terminal-zero repair in the local draft

The successor now explicitly returns the preceding nonzero divisor when a
classical-tail remainder becomes zero, then follows the normalization and
stage-E degree guard. Early zero inside a budgeted half-gcd call still aborts.
Sections 4.4 and 6.3 now agree. The proof records the Euclidean invariant that
justifies this terminal transition, including nonzero pseudo-division scaling.
Its complete instruction-level accounting is still unverified: this wording
repair does not establish a new score or discharge the heuristic obligations.

The repaired successor passes structural validation as draft with package hash
`2fe433af54eef28678a0b2a80e5fd0c4af197b3461dba63018693bb086992085`.
The earlier hash above identifies the prior accounting-only draft. The
competition candidate remains local; the Scribe model, checks and audit are
being published separately at the user's request.
