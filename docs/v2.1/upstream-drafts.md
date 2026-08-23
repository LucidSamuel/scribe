# Upstream drafts for tachyon-zcash/ragu

Status: updated 2026-08-24. **Draft 1 (the 2026-08-22 replacement) was POSTED
by Samuel as a comment on PR #842 on 2026-08-23**, alongside the pushed
ragu-side transition-table patch. **Draft 2 remains unposted** and awaits
Samuel's review (verify #612/#655 before posting). The replacement draft was
verified against PR #842 at `48433931`; the original 2026-08-21 draft 1 is
retained below as explicitly superseded historical material.

## Current replacement for draft 1 (2026-08-22)

**What it is.** A mutation-tested finding about the discriminating power of
PR #842's exact acceptance commands. It supersedes the older claim that the
direct MSM property is capped at 255 terms: #842 now samples through
`ProductionRank = 8192`, and the end-to-end prover genuinely reaches MSM sizes
8190, 8191, and 8192.

**Where it goes.** Prefer a concise comment on
<https://github.com/tachyon-zcash/ragu/pull/842>, because the concrete fix is a
small addition to `crates/ragu_acceleration/tests/msm_equivalence.rs`. The
general discrimination-certificate recommendation can also be linked from
<https://github.com/tachyon-zcash/ragu/issues/834>.

**Measured result.** In an isolated worktree at `48433931`, a sentinel defect
was planted in `accelerated_msm`: return an incorrect result only when
`coeffs.len() == 8104`. This is the highest Zakura Booth-window transition
below `ProductionRank`, not a power-of-two boundary.

The mutant escaped both commands used by the native-MSM acceptance path:

```text
cargo test --release -p ragu_acceleration --locked --features native-msm \
  --test msm_equivalence -- --test-threads=1

cargo test --release -p ragu_pcd --locked --features native-msm \
  --lib backend_tests:: -- --test-threads=1
```

The escape is deterministic. `arb_msm_size()` can generate arbitrary sizes
only through `TestRank` (0 through 128); above that it generates powers of two
plus or minus one. It therefore cannot generate 149, 404, 1097, 2981, 8104,
or their immediate lower neighbors.

A deterministic boundary table for both Pasta curves killed the mutant
immediately and passed against clean #842. The complete three-test MSM suite
then passed, as did native-MSM Clippy with `-D warnings`. A positive-control
mutant at `n == 8192` was rejected by the existing end-to-end proof-digest
comparison, confirming that the accelerated route is live and the finding is
specifically about unsupported decision boundaries rather than a vacuous
harness.

The current acceptance surface is now also encoded as the versioned Scribe
corpus `corpus/msm-pr842/`. Its input set is the complete support of #842's
`arb_msm_size()` strategy: every size from 0 through 128, then every supported
power-of-two neighbor through 8192. A fresh `validate()` run reports 1/2
negatives caught, with only `msm-pr842-mutant-8104-add-base` escaping. A
separate test supplies the missing 8104 case and rejects that mutant, proving
the escape is caused by the corpus boundary rather than a no-op defect.

**Additional hardening included in the local patch.** `Proof::test_digest`
currently accounts for every audited field, but its schema is a manual walk.
An exhaustive `Proof { field: _, ... }` pattern without `..` makes a future
field addition fail compilation until the digest module consciously accounts
for it. This does not change the digest or protocol.

### Current draft text

> I decided to play around with Scribe here by treating #842's exact CI
> commands as an oracle and asking a stricter question: can the green check be
> made red by a known-bad implementation?
>
> I encoded the complete size support of `arb_msm_size()` as a versioned
> Scribe corpus and ran two paired negatives through the same differential
> oracle: an incorrect result at `n = 8192` is caught, while the same defect at
> `n = 8104` escapes. The resulting discrimination report is 1/2 negatives
> caught, with the 8104 mutant named as the escape. Supplying 8104 directly
> rejects it, so the mutant is real and the escape is caused by input support.
>
> On #842 HEAD (`48433931`), I planted a one-line sentinel defect in the
> accelerated MSM: return an incorrect result only when
> `coeffs.len() == 8104`. That is not an arbitrary large size; it is the
> highest Booth-window transition in Zakura's `best_multiexp` below
> `ProductionRank = 8192`.
>
> Both existing acceptance layers stayed green: the direct Pallas/Vesta MSM
> differential properties passed, and the end-to-end PCD backend-equivalence
> tests passed.
>
> The reason is deterministic. The direct strategy's `window_boundaries`
> branch samples powers of two +/- 1, while Zakura changes its Booth window at
> 4, 32, 55, 149, 404, 1097, 2981, and 8104. Its other size branch is bounded
> by `TestRank = 128`, so most of those transition points are outside the
> strategy's support.
>
> I added a small deterministic table covering both sides of every real
> transition for both Pasta curves, plus the production maximum:
> `3/4, 31/32, 54/55, 148/149, 403/404, 1096/1097, 2980/2981, 8103/8104,
> 8192`. The new test fails immediately against the planted defect and passes
> against clean HEAD; the full MSM suite and Clippy also remain green.
>
> As a positive control, a defect at `n = 8192` is already caught by the
> end-to-end proof-digest test. I also instrumented backend dispatch: proving
> reaches MSM sizes 8190, 8191, and 8192. So this is not a claim that the
> current harness is vacuous. The production route is live; the gap is that
> probabilistic power-of-two sampling does not guarantee coverage of the
> optimized dependency's actual decision boundaries.
>
> I think the immediate fix is the deterministic transition test beside the
> proptest. More generally, each optimization PR could carry a small
> discrimination certificate: prove the override ran, enumerate its
> implementation decision boundaries, and show that the exact acceptance
> command rejects at least one planted defect. I have a tested patch for the
> transition suite if useful.

---

## Historical upstream activity check (2026-08-21)

**#834** ("AI-assisted prover optimization loop", open, `C-performance`/`I-pcd`)
has moved fast since the fc61822c pin: TalDerei posted an architecture proposal
(2026-08-17) splitting a `ragu_backend` trait (Arkworks-`VariableBaseMSM`-style,
reference impl + overridable accelerated impl) from `ragu_pcd` orchestration,
plus a five-item implementation checklist — item 3 is a differential equivalence
harness, item 4 is "add acceleration one override per PR." One merged bootstrap
PR plus four open stacked PRs implement it: #836 (placeholder crates, **merged**
2026-08-17), #839 (backend
interfaces, open), #840 (route ops through backends, open), #841 (**equivalence
test harness**, open — proptest-based three-way MSM/sparse-poly/registry/digest
comparison), and #842 (**zakura-pasta-curves assembly MSM override**, open,
benchmarked on 2^13 MSMs). Last activity 2026-08-19/20. **#660** ("Serde
feature on proof", open) is dormant — no comments, untouched since 2026-04-17;
notably, PR #841 adds a `ragu_pcd/src/proof/digest.rs` for equivalence
comparison, which overlaps #660's canonical-bytes question without referencing
it. `qa/crates/lean_extraction` is unchanged since the pin:
`src/driver.rs` on today's `main` is byte-identical to `fc61822c`, and no
issue or discussion about the `Extra = ()` shim exists upstream.

---

## Superseded draft 1 — do not post

This draft predates #842's expansion through `ProductionRank`. Its claims that
direct MSM equivalence is capped at 255 terms and never selects `c >= 7` are
historically accurate for #841 alone but stale for the current stacked PR.
Use the 2026-08-22 replacement above.

**What it is.** Feedback on the input-size coverage of the differential
acceptance oracle (checklist item 3 / PR #841, gating item 4 / PR #842), based
on the MSM band-coverage measurement in `docs/v2.1/equivalence-notes.md`.

**Where it goes.** A comment on
<https://github.com/tachyon-zcash/ragu/issues/834>. Alternatively it could be a
review comment on PR #841 (the `MAX_MSM_TERMS = 255` line); the issue is the
better venue since the point spans #841 and #842 and the design discussion
lives there.

**Moot check: not moot — the opposite.** The measurement predates the harness,
and PR #841 independently implements the general shape of recommended fix 1
(direct MSM sampling with edge bias). But the implementation caps direct MSM
equivalence at 255 terms, which covers window bands `c ∈ {1,3,4,5,6}` and
never selects `c ≥ 7` — while PR #842's accelerated backend is justified by
benchmarks at 2^13-point MSMs (band 10: 8,192 falls in `[8104, 22027)`) and the end-to-end digest
tests inherit the `ProductionRank` ceiling (`n ≤ 2^13 = 8192`, so at most
band 10; the fleet's cached trivial proof measured n = 5,507, band 9, but
#841's randomized dummy circuits have not been re-instrumented, so only the
rank ceiling is proven for the PR branch — which still leaves `c ≥ 11`
unreachable). So
the blind spot the escaped mutant demonstrates is now about to be inherited by
the acceptance oracle that will gate assembly-level MSM rewrites. The comment
is more timely than when the measurement was made, and I rewrote it around
their in-flight PRs rather than around the fuzz fleet alone.

**Expected reaction.** Likely constructive — TalDerei is actively iterating on
exactly this harness and the fix is a small strategy change in an open PR. The
plausible pushback is runtime at multi-million-term MSMs; the draft preempts
that by suggesting a deterministic one-case-per-edge suite (the single largest
case, band 16 at ~3.27M terms, costs seconds) rather than raising the proptest
case budget. Before posting: (a) re-check `bucket_lookup`'s thresholds in
`ragu_arithmetic/src/util.rs` on current `main` — the draft pins its band
edges to `fc61822c` and says so, but if the table was retuned the band
numbers should be refreshed; (b) the reproduction pointer was deliberately
kept vague ("written up") since the scribe repo is not public — if it becomes
public, a concrete link can replace it.

### Draft text

> I did an input-size coverage measurement of `ragu_arithmetic::util::msm`
> that seems directly relevant to the equivalence harness (checklist item 3,
> #841) and the acceptance rule for overrides (item 4, #842). Measured at
> `fc61822c` (2026-08-16), before the backend seam landed; `util.rs` is
> unchanged on `main` as of `02d1b151`, so the band edges below are current.
>
> **Background.** `msm` selects its window width via `bucket_lookup(n)`, a
> 15-threshold table partitioning `n` into 16 bands (`c = 1..=16`). Bands take
> structurally different code paths: bucket-vector size `2^c − 1`, segment
> count `ceil(255/c)`, the window shift/limb arithmetic in `get_at`, and the
> `Bucket::{None, Affine, Projective}` transitions. Band 2 is structurally
> empty (the first two thresholds are both 4), leaving 15 selectable bands.
> Bands 11–16 (`n ≥ 22027`) are unreachable from inside the protocol at any
> implemented rank: `R::num_coeffs() = 2^13 = 8192` for `ProductionRank`, and
> the only other production call site is the ~108-term decomposition MSM in
> `ragu_pcd::fuse`.
>
> **What the existing fuzz fleet exercises.** I instrumented `msm` with
> env-gated telemetry (one line per call recording `n` and the selected `c`,
> plus counters on every bucket transition and `get_at` branch) and ran all 24
> libFuzzer targets over their seeds plus fresh fuzzing (~18.2M executions,
> rustc 1.97.1):
>
> - **1 of 24 targets reaches `msm` at all** (`fuzz_verify_reject`), and only
>   during init: 32 calls building the cached `ProductionRank` trivial proof.
>   `verify()` itself performs no MSM, so per-input fuzzing adds zero MSM
>   coverage — the 32-call distribution is frozen and reproduced identically
>   across reruns.
> - Those 32 calls: `n ∈ {3×3, 4×12, 5×3, 7, 16, 63, 93, 111, 5507×9}`,
>   i.e. **4 of 15 selectable bands** (`c ∈ {1, 3, 5, 9}`).
> - Band 10 (`n ≥ 8104`) goes unreached even at `ProductionRank`: sparse
>   commits feed only nonzero blocks to `msm`, and the trivial proof's largest
>   commit has 5,507 nonzero coefficients of 8,192.
> - Micro-branch coverage *inside* reached bands is good (8 of 9: all bucket
>   transitions, both `get_at` alignment paths; the out-of-bounds early return
>   is structurally dead for 255-bit scalars with `c ≤ 16`). The gap is purely
>   input-size, not branch-local.
>
> **Escaped-mutant demonstration.** To check the gap is exploitable rather
> than theoretical, I ran a small planted-defect corpus against a differential
> oracle whose input distribution mirrors the nine sizes the fleet actually
> produces. Two single-line mutants (a bucket-transition point drop, a
> `get_at` sub-byte shift skip) are caught. A third — one doubling short,
> gated on `c ≥ 11` — **escapes**, and the escape is robust by construction:
> the fleet's empirical max is 5,507 and `2^13 = 8192 < 22027`, so no
> in-protocol input generation short of a rank bump can reach it. The mutant
> computes a genuinely wrong result the moment its path is entered (unit-test
> pinned), it just never is. To be clear about scope: this is a statement
> about the fleet's input distribution as an oracle input set, not about the
> planted-defect discipline itself — `PATCHER_SELFTEST` and the vacuity
> telemetry are exactly the right practice, and this measurement only says
> input size is a dimension they haven't been pointed at yet.
>
> **Why this matters for #841/#842 specifically.** The harness in #841 is
> exactly the right shape — direct MSM sampling is the first place the upper
> bands are reachable *at all*, since `msm` driven directly has no rank
> ceiling. But as written, `MAX_MSM_TERMS = 255` covers bands
> `c ∈ {1, 3, 4, 5, 6}` and never selects `c ≥ 7`; and `bounded_edge_usize`
> biases toward power-of-two edges rather than targeting `bucket_lookup`'s
> thresholds — within the 255-term cap the two coincide only by accident
> (4 and 32 are thresholds *and* powers of two; 55 and 149 are thresholds
> only), and above the cap they diverge entirely. Meanwhile the end-to-end
> digest comparison runs at `ProductionRank`, whose `n ≤ 2^13 = 8192` caps it
> at band 10 (the `c ≥ 11` bands stay unreachable regardless), and #842's
> override is motivated by benchmarks at 2^13-point MSMs — sizes the direct
> equivalence tests never generate. Net effect: an accelerated MSM whose
> defect lives in a wide-window path would pass the harness and be accepted.
>
> **Three low-cost closes:**
>
> 1. **Band-edge boundary sampling.** Sample `n` at each of `bucket_lookup`'s
>    15 thresholds ±1 — 30 sizes, one either side of every band boundary, so
>    every selectable band and every boundary transition in `get_at` is
>    exercised. Cheapest as a deterministic one-case-per-edge test next to
>    the proptest, not a raised proptest case budget: the largest case
>    (band 16, `n = 3,269,019`) dominates the cost at seconds of
>    reference-MSM time per curve, and everything below it is noise.
> 2. **One dense-commit fixture.** A near-dense `R<13>` polynomial commit
>    (`n ≥ 8104`) lights up band 10, the only band production can reach that
>    nothing currently exercises, and covers it at the real call site rather
>    than only via direct `msm` calls.
> 3. **A wide-band planted-defect selftest.** `qa/fuzz` already keeps its
>    oracle honest with `PATCHER_SELFTEST` (a planted defect the oracle must
>    catch) and vacuity telemetry — this discipline just hasn't reached
>    input-size coverage yet. The same pattern applied here (a deliberately
>    broken wide-window MSM the harness must reject) would keep the
>    equivalence oracle honest about size coverage permanently, including
>    after future `bucket_lookup` retunes.
>
> Full methodology, per-band tables, and the mutant corpus with its
> discrimination report are written up; happy to share any of it — or a
> concrete patch for (1) — if useful.

---

## Draft 2 — issue on `qa/crates/lean_extraction`'s dropped `C·D = 0`

**What it is.** A heads-up question about the extraction driver deliberately
under-modeling the D wire (`Extra = ()`, no fourth wire, no `C·D = 0`
constraint), asking whether the shim is still intended now that d-wires are
load-bearing elsewhere in the codebase.

**Where it goes.** A new issue on <https://github.com/tachyon-zcash/ragu>
(issue rather than discussion: it names concrete code and has a concrete
resolution; the repo's FV work is tracked in issues). Suggested labels if
available: whatever they use for `qa`/FV.

**Moot check: not moot.** `qa/crates/lean_extraction/src/driver.rs` on
today's `main` (`02d1b151`) is byte-identical to `fc61822c` — the shim is
unchanged — and there is no upstream issue or discussion mentioning it (search
for `lean_extraction` and "D wire" turned up the d-wire redesign PRs but
nothing about the extraction gap). The code comment shows the authors know, so
the draft is a question about intent and timeline, not a bug report.

**Expected reaction.** Most likely "known, deferred until the d-wire redesign
settles" with the issue kept open as a tracking item — which is still a win
(the gap becomes tracked instead of only living in a doc comment). Small
chance of "the Lean model only covers gadgets where the shim is provably
harmless," in which case the completeness point below is the part worth
pressing on. The one-line scribe mention is deliberately last and minimal;
cut it if it reads as a pitch.

### Draft text

**Suggested title:** `lean_extraction: is the Extra = () shim (no D wire, no
C·D = 0) still intended now that d-wires are constrained?`

> `qa/crates/lean_extraction`'s `ExtractionDriver` deliberately under-models
> the gate's fourth wire:
> [`src/driver.rs#L95-L107`](https://github.com/tachyon-zcash/ragu/blob/fc61822cf8c248d36b950c89817bf170d533a7f3/qa/crates/lean_extraction/src/driver.rs#L95-L107)
> declares `type Extra = ()` with a doc comment explaining that `gate()` emits
> the old three-wire `mul` shape
> ([L117-L138](https://github.com/tachyon-zcash/ragu/blob/fc61822cf8c248d36b950c89817bf170d533a7f3/qa/crates/lean_extraction/src/driver.rs#L117-L138))
> and `assign_extra` allocates a fresh wire with no accompanying constraint
> ([L140-L151](https://github.com/tachyon-zcash/ragu/blob/fc61822cf8c248d36b950c89817bf170d533a7f3/qa/crates/lean_extraction/src/driver.rs#L140-L151)),
> "at the cost of not modeling `C · D = 0` on the extracted side," to keep
> emitted Lean traces identical to the pre-redesign shape. (Links pin
> `fc61822c`; the file is unchanged on current `main` as of 2026-08-21.)
>
> The comment makes clear this is a known, intentional compat shim, so this is
> a question about current intent rather than a bug report. What prompted it:
> the constraint set the Lean side sees is now a strict subset of what the
> deployed circuits enforce, and the direction of that gap cuts differently
> for the two theorem families in `qa/lean`:
>
> - **Soundness** theorems (`constraints ⇒ Spec`) stay conservative today —
>   fewer modeled constraints means proving over a superset of the real
>   satisfying assignments. But any circuit whose soundness *depends* on
>   `C·D = 0` or on constrained d-wires can't have a faithful proof at all,
>   because the load-bearing constraint doesn't exist in the model — and
>   after #612 (constrain d-wire in stage masks), #606 (paired d-wire
>   allocation), and #655 (donated d-wires in the standard allocator),
>   d-wires are load-bearing in exactly that sense. (#620 proposed a
>   d-wire alloc-pairing regression test but was closed unmerged, its
>   author noting the proptests already cover it.)
> - **Completeness** theorems are proven over the shim's model, which has no
>   production D slot at all — `assign_extra` mints a separate, unconstrained
>   fresh witness instead of the gate's fourth wire.
>   "The honest prover satisfies the circuit" is established for the
>   pre-redesign circuit shape, not the deployed one — the real completeness
>   claim presumably still holds (default-zero D plus redeem-only-when-C=0),
>   but the kernel-checked statement doesn't cover it.
> - The fingerprint machinery pins traces to the old shape *by design*, so
>   this divergence is invisible to the trace-stability check — the one
>   mechanism that would otherwise flag a model/circuit mismatch.
>
> So: is the shim still the intended tradeoff now that the d-wire redesign
> has settled, and is re-modeling the fourth wire on the extraction side
> planned/tracked anywhere? Asking partly to calibrate how to read the
> existing `qa/lean` proofs (which of them are statements about deployed
> circuits vs. the legacy shape), and partly because I recently built a
> Driver-based extractor for a separate project that models the pair fully
> and reconciles against `ragu_circuits::metrics` counts — so I'm fairly
> confident the full model is tractable, and happy to compare notes if
> that's the direction.

---

## Verification trail (for Samuel, not for posting)

- Pinned rev evidence read from the cargo checkout at
  `~/.cargo/git/checkouts/ragu-2ccfa101a62981f4/fc61822/`.
- `driver.rs` drift check: `shasum` of the checkout file equals the shasum of
  `raw.githubusercontent.com/tachyon-zcash/ragu/main/.../driver.rs`
  (`9d6b5138…`) on 2026-08-21.
- PR #841 harness details read from branch `backend-equivalence-harness`:
  `MAX_MSM_TERMS = 255` in `crates/ragu_acceleration/tests/msm_equivalence.rs`;
  `bounded_edge_usize` (power-of-two bias) in
  `crates/ragu_testing/src/strategies.rs`; `ProductionRank` in
  `crates/ragu_pcd/src/backend_tests.rs`.
- Lean theorem shapes read from `qa/lean/Ragu/Circuits/Boolean/Alloc.lean`
  (both `soundness` and `completeness` proven per instance).
- `PATCHER_SELFTEST` confirmed in `qa/fuzz/src/recorder.rs:850` at the pin.
- Measurement numbers are from `docs/v2.1/equivalence-notes.md`, unmodified.
- `bucket_lookup` thresholds independently re-verified against the vendored
  copy (`crates/oracle-differential/src/vendored_msm.rs`): 15 entries,
  `[4, 4, 32, 55, 149, 404, 1097, 2981, 8104, 22027, 59875, 162755, 442414,
  1202605, 3269018]`; band 16 begins at `n = 3,269,018`.
- **Second fact-check pass (2026-08-21, independent review) confirmed:**
  current `main` is still `02d1b151`; #839–#842 remain open;
  `MAX_MSM_TERMS = 255` and the power-of-two-biased strategy are accurate;
  `zakura-pasta-curves` is the correct crate name; #660 is open and dormant.
  Two corrections it produced, now applied above: PR #620 was **closed
  unmerged** (its author said proptests already covered it) — the paired
  d-wire allocation landed via **#606**, which Draft 2 now cites; and the
  end-to-end ceiling claim is stated as the proven `ProductionRank` bound
  (n ≤ 8192, at most band 10) rather than the fleet-measured band 9, since
  #841's randomized dummy circuits have not been re-instrumented.
- **Still lower-confidence — re-check before posting**: PR numbers #612 and
  #655, and the #841 crate paths (`ragu_acceleration`, `ragu_testing` —
  unreconciled with the `ragu_backend` naming in the architecture comment).
