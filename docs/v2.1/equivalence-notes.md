# Phase C — equivalence instance notes: MSM coverage measurement and the escaped mutant

Status: measured 2026-08-18. Ragu pinned at `origin/main` =
`fc61822cf8c248d36b950c89817bf170d533a7f3` (the Phase C audit revision; the
`~/ragu` working tree was 23 commits behind it, so all measurement ran in an
isolated clone checked out at that revision — the working tree was not
touched). This doubles as the draft basis for a comment on ragu #834.

## What was measured

`ragu_arithmetic::util::msm` selects its window strategy via `bucket_lookup(n)`,
a 15-entry threshold table that partitions `n` into 16 window-width bands
(`c = 1..=16`). The band edges at revision `fc61822c`:

| band `c` | selected for `n` | reachable? |
|---|---|---|
| 1 | 0–3 | yes |
| 2 | — | **structurally empty** (first two thresholds are both 4) |
| 3 | 4–31 | yes |
| 4 | 32–54 | yes |
| 5 | 55–148 | yes |
| 6 | 149–403 | yes |
| 7 | 404–1096 | yes |
| 8 | 1097–2980 | yes |
| 9 | 2981–8103 | yes |
| 10 | 8104–22026 | yes, only by a near-dense `R<13>`/`R<14>` commit |
| 11–16 | ≥ 22027 | **not at any implemented rank** — `R::num_coeffs() = 2^rank` caps the commit-side MSM at 8192 (`ProductionRank = R<13>`); the only other production call site is a ~108-term decomposition MSM (`ragu_pcd/src/fuse/_06_ab.rs`) |

Different bands take structurally different code paths: bucket-vector sizes
(`2^c - 1`), segment counts (`ceil(255/c)`), window-boundary shift/limb
arithmetic in `get_at`, and `Bucket::{None, Affine, Projective}` transitions.

## Methodology

1. Cloned ragu at `fc61822c` into an isolated scratch checkout.
2. Instrumented `msm` in that clone with env-gated telemetry: one log line per
   `msm()` call recording `n` and the selected `c`, plus cumulative counters
   on every `Bucket::add_assign` transition, every final `Bucket::add` case,
   and the three `get_at` branches (out-of-bounds early return, byte-aligned
   window, byte-crossing shift).
3. Built the entire `qa/fuzz` fleet (24 libFuzzer targets, `-s none`, rustc
   1.97.1 — the two locally installed nightlies predate ragu's 1.97 MSRV; the
   clone-local `extract_dict` helper bin was dropped from the fuzz manifest
   because cargo-fuzz applies sancov flags to it without linking a sanitizer
   runtime, an upstream papercut unrelated to the measurement).
4. Ran all 24 targets for 20s each over their committed seeds plus fresh
   fuzzing (~18.2M total executions), telemetry per target; then re-ran the
   only two targets that link `ragu_pcd` (`fuzz_verify_reject`,
   `fuzz_staging`) for 60s each as confirmation (1,547 and 540,703 further
   executions respectively).

Runs are short, but the zero-coverage results below are structural, not
budget-limited: no fuzz target other than `fuzz_verify_reject` has any call
path to `msm` at all (the only production `msm` call sites are
`sparse::Polynomial::commit` and the decomposition MSM in `ragu_pcd::fuse`;
the substrate targets never commit — `fuzz_staging` references `ragu_pcd`
only in comments), and `fuzz_verify_reject`'s per-input work performs no MSM
(its call count froze at 32 across every execution; all 32 happen in the
one-time cached trivial-proof build). The 60s reruns reproduced the identical
32-call distribution.

## The fleet's actual rank and op-limit spread (verified, not assumed)

The roadmap's "most of the fleet runs TestRank at `max_ops: 48`" holds, with
these deviations:

- `fuzz_verify_reject`: `type R = ProductionRank` (`R<13>`), no substrate
  programs — it clones/corrupts/verifies one cached trivial proof.
- `fuzz_circuit_cheat`: `Limits { max_ops: 64 }`.
- `fuzz_witness_pinning`: body capped at `Limits { max_ops: 16 }`.
- Everything else that decodes substrate programs uses `Limits::default()`
  (= 48) at `TestRank = R<7>`; the pure-arithmetic targets (element ops,
  Poseidon, endoscalar, multipack, point identities, io roundtrip, …) carry
  no rank at all.

The op-limit spread turns out to be irrelevant to MSM reach: op limits shape
circuit polynomials, and the substrate targets never commit them.

## Results

**Targets reaching `msm` at all: 1 of 24.** Only `fuzz_verify_reject`
executes `msm`, and only during process initialization: 32 calls building the
one cached `ProductionRank` trivial proof. `verify()` itself performs no MSM,
so per-input fuzzing adds zero MSM coverage. Deterministic distribution over
those 32 calls:

| `n` | calls | band `c` |
|---|---|---|
| 3 | 3 | 1 |
| 4 | 12 | 3 |
| 5 | 3 | 3 |
| 7 | 1 | 3 |
| 16 | 1 | 3 |
| 63 | 1 | 5 |
| 93 | 1 | 5 |
| 111 | 1 | 5 |
| 5507 | 9 | 9 |

**Window-strategy band coverage: 4 of 15 reachable bands (27%).** The fleet
reaches bands `c ∈ {1, 3, 5, 9}`. Bands 4, 6, 7, 8 are skipped outright.
Band 10 (`n ≥ 8104`) goes unreached even at `ProductionRank`: the trivial
proof's largest commit has 5,507 nonzero coefficients out of 8,192 — sparse
commits feed only nonzero blocks to `msm`, so crossing into band 10 requires
a near-dense polynomial that nothing in the fleet produces. Bands 11–16 (40%
of the table) are unreachable at any implemented rank.

**Micro-branch coverage inside the reached bands is good: 8 of 9.** All three
`Bucket::add_assign` transitions, all three final `Bucket::add` cases, and
both `get_at` alignment paths fire (cumulative counters: 130,316 None→Affine,
127,510 Affine→Projective, 965,975 Projective→Projective, 17,097 / 2,806 /
127,510 final None/Affine/Projective, 1,255,102 shifted vs 200,704 aligned
window reads). The `get_at` out-of-bounds early return never fires — and is
structurally dead for 255-bit scalars with `c ≤ 16` (`skip_bytes ≤ 31 < 32`),
at every `n`, so it is excluded from the band-coverage denominator rather
than padded into it.

## The hypothesis, adjudicated

The brief's hypothesis: a defect confined to a large-`n` window path is
unreached by the circuit generation the fleet actually performs, and would be
invisible to #834's phase 4 as specified (RNG replay fixes randomness, not a
generator that never reaches production sizes). `fuzz_verify_reject` at
`ProductionRank` was named as the obvious falsifier.

**Confirmed, and stronger than hypothesized.** The falsifier does not
falsify: `fuzz_verify_reject` reaches `msm` only through one cached trivial
proof whose commits are sparse (max `n` = 5,507, band 9), and its fuzzed work
(verify) never executes `msm`. A defect gated on band 10 — production-rank
dense-commit territory — already escapes the fleet, and bands 11–16 are
unreachable at any implemented rank. The corpus mutant is planted at
`c ≥ 11` (`n ≥ 22027`) because that placement is demonstrable **both**
empirically (fleet max 5,507) and statically (`2^13 = 8192 < 22027`), making
the escape robust to future fleet changes short of a rank bump.

To keep the claim honest in the other direction: this is a statement about
the *fuzz fleet's generated-circuit distribution* as an acceptance-oracle
input set. It is not a claim that ragu lacks planted-defect discipline — ragu
runs `PATCHER_SELFTEST` (in `qa/fuzz/src/recorder.rs` at this revision) and
vacuity telemetry precisely to keep its oracles honest. The gap is narrower:
that discipline has not been applied to *input-size coverage* of the MSM
window strategy, and an equivalence oracle whose input distribution mirrors
the fleet inherits the blind spot.

## The corpus and the committed report

`corpus/msm/manifest.json` (`msm-corpus-v1`) is a `Corpus<EquivalenceClaim>`
whose input distribution is exactly the nine measured fleet sizes
`[3, 4, 5, 7, 16, 63, 93, 111, 5507]` over a deterministic seeded pool
(full-width scalars so every window segment of every selected band is
populated):

- **1 positive** — `msm-positive-shifted-window`: the reference algorithm run
  at a deliberately different window width (any fixed `c` computes the same
  sum). Accepted, non-vacuously.
- **3 negatives** — single-line planted defects in a vendored-verbatim copy
  of `msm` (provenance in `crates/oracle-differential/src/vendored_msm.rs`):
  - `msm-mutant-bucket-collision-drop` (bucket transition drops a point) —
    **caught**;
  - `msm-mutant-window-shift-drop` (`get_at` skips the sub-byte shift) —
    **caught**;
  - `msm-mutant-wide-window-skip-double` (one doubling short, gated on
    `c ≥ 11`) — **escaped**.

`validate(DifferentialOracle, corpus)` produces the committed
`corpus/msm/discrimination-report.json`:

```json
{
  "corpus_version": "msm-corpus-v1",
  "negatives_caught": 2,
  "negatives_total": 3,
  "escaped": ["msm-mutant-wide-window-skip-double"],
  "positives_accepted": 1,
  "positives_total": 1
}
```

Coverage identified the blind spot, the mutant proves it exploitable, the
report quantifies it — and it comes out of the same `validate()` machinery
Phase B uses, which is the point of running two instances against one core.
The escaped mutant is a real defect, not a no-op: unit test
`wide_window_defect_is_real_once_gated_path_is_entered` shows it computes a
wrong answer the moment its path is entered, and `bucket_lookup_band_edges`
pins the public-path link (`n = 22027` selects `c = 11`).

Reproduce: `cargo test -p oracle-differential`, and
`cargo run -p oracle-differential --example regenerate_report` after any
corpus change.

## What would close the gap

For #834's phase 4 (differential acceptance of AI-optimized prover code) as
currently specified over the existing fleet, the MSM comparison boundary
inherits a hard input-size ceiling. Closing it does not need a new generator:

1. **Direct boundary sampling.** Drive `msm` itself with sizes drawn from
   each `bucket_lookup` band (one representative per band edge ±1 suffices —
   sixteen sizes cover every window strategy, as this corpus demonstrates in
   miniature). This is the highest-value fix and costs seconds.
2. **A dense-commit fixture.** One near-dense `R<13>` polynomial commit
   (n ≥ 8104) would light up band 10, the only band production can reach
   that the fleet does not.
3. **Band-edge regression pins.** `bucket_lookup`'s own unit test pins the
   table; what is missing is anything that *executes* the upper bands. A
   planted-defect selftest at a wide band (exactly this corpus's escaped
   mutant) would keep the differential honest about size coverage — the same
   role `PATCHER_SELFTEST` plays for constraint coverage.

## Toolchain note (cross-phase finding)

Scribe pins rustc 1.90.0 (`rust-toolchain.toml`); ragu's MSRV is 1.97. A
path/git dependency on any ragu crate therefore cannot build inside this
workspace today. Phase C worked around it by vendoring the ~150-line `msm`
verbatim (provenance and the two semantics-preserving deltas documented in
`vendored_msm.rs`, faithfulness cross-checked against a structure-free
textbook MSM in unit tests). **Phase B cannot vendor its way around the same
wall** — `frontend-ragu` must link ragu's `Driver` trait — so reaching ragu
from this workspace requires bumping the scribe toolchain pin to ≥ 1.97,
which is a workspace-owner (Phase A) decision.

## Errata in the briefs found while verifying

- `PATCHER_SELFTEST` lives in `qa/fuzz/src/recorder.rs` at `fc61822c`, not
  `qa/fuzz/src/record.rs` as the roadmap/brief cite.
- The brief's implicit expectation that `fuzz_verify_reject` at
  `ProductionRank` might reach the top of the implemented-rank range was too
  generous: sparse commits keep even the production-rank trivial proof three
  bands below the table's implemented ceiling, and verification performs no
  MSM at all.
- Everything else checked out: the 15-entry table spanning to ~3.2M, `Proof`
  deriving only `Clone` (no digest to compare; #660 open), the ~108-term
  fuse MSM, `Limits::default() == 48`, and the named deviations
  (`ProductionRank` in verify-reject, 64 in circuit-cheat, 16 in
  witness-pinning).
