# ZKGadgetEval — full-suite results

Two runs to date: a 1-sample build-vs-LSP A/B (2026-07-10) and a 3-sample
variance run (2026-07-17). Combined: **118/120 positive sessions proved,
negatives refused 16/16, zero soundness alarms.** Both failures were the same
gadget (range-check-8), in different modes — see the variance section.

---

# Run 2: variance (samples = 3)

- **Date:** 2026-07-17 · **Backend:** `claude-cli (claude-sonnet-5)` · budget 5,
  **3 samples** per gadget per mode, modes `build` + `lsp` · **Total:** 256 minutes
- **Raw data:** `variance-run-2026-07-17.json`

| Mode | Pass rate | Tier 1 | Tier 2 | Tier 3 | Mean iters (proved) | Wall |
|---|---|---|---|---|---|---|
| `build` | 44/45 (98%) | 15/15 | 20/21 | 9/9 | 1.07 | 84 min |
| `lsp` | **45/45 (100%)** | 15/15 | 21/21 | 9/9 | 1.07 | 72 min |

**Negatives: refused 12/12** (2 gadgets × 2 modes × 3 samples).

The only non-perfect cell is **range-check-8 in build mode: 2/3** —
pass@1 = 0.67, pass@2 = 1.0, Wilson 95% [0.21, 0.94]. Every other positive cell
is 3/3 with pass@1 = 1.0.

## What the variance run corrects

- **The first run's "build beats LSP" was single-sample noise.** LSP went 45/45
  here — including range-check-8, which had been its only failure — while build
  dropped a range-check-8 sample. Mean iterations are identical and aggregate
  wall time mildly favored LSP. Verdict: **no measurable quality difference
  between feedback modes on this suite**; choose on cost/latency.
- **Range-check-8 is the suite's one hard obligation.** It is the sole failure
  in both runs (once per run, different modes each time) and the only gadget
  with pass@1 < 1. Its 9-constraint bit-decomposition proof — case-splitting
  8 boolean constraints into a `ZMod.val` bound — is the closest thing the
  suite has to a frontier obligation short of lookups.
- **Refusal of false specs is stable**: 16/16 across both runs, all with
  neutral gadget names.

---

# Run 1: first full-suite A/B (samples = 1)

- **Date:** 2026-07-10
- **Backend:** `claude-cli (claude-sonnet-5)`
- **Config:** budget 5 iterations, 1 sample per gadget per mode, modes `build` + `lsp` (in-harness A/B)
- **Suite:** v0.2.0 — 15 positive gadgets (tiers 1–3) + 2 negative gadgets (deliberately under-constrained, spec is false)
- **Raw data:** `full-run.json` produced by
  `cargo run -p zkgadget-eval -- --budget 5 --samples 1 --modes build,lsp -o benchmark/results/full-run.json`
- **Total wall time:** 77 minutes

## Summary

| Mode | Pass rate | Tier 1 | Tier 2 | Tier 3 |
|---|---|---|---|---|
| `build` (raw `lake build` text) | **15/15 (100%)** | 5/5 | 7/7 | 3/3 |
| `lsp` (structured goal states) | **14/15 (93%)** | 5/5 | 6/7 | 3/3 |

**Negatives: refused 4/4 false specs** (both gadgets × both modes) — zero soundness
alarms. The loop exhausted its budget on every false spec; the kernel and the
`#audit_axioms` gate rejected each attempted proof.

## Per-gadget results

| Gadget | Tier | build | lsp |
|---|---|---|---|
| range-check-8 | 2 | ✅ 1 iter, 475s | ❌ exhausted (5 iter, 757s) |
| boolean-check | 1 | ✅ 1 iter, 24s | ✅ 1 iter, 28s |
| nonzero-check | 1 | ✅ 1 iter, 13s | ✅ 1 iter, 29s |
| equality-check | 1 | ✅ 1 iter, 13s | ✅ 1 iter, 24s |
| add-gate | 1 | ✅ 1 iter, 12s | ✅ 1 iter, 30s |
| mul-gate | 1 | ✅ 1 iter, 23s | ✅ 1 iter, 35s |
| conditional-select | 2 | ✅ 2 iter, 48s | ✅ 2 iter, 59s |
| poseidon-sbox | 2 | ✅ 1 iter, 16s | ✅ 1 iter, 24s |
| poseidon-sbox-7 | 2 | ✅ 2 iter, 25s | ✅ 1 iter, 41s |
| swap-gate | 2 | ✅ 1 iter, 49s | ✅ 2 iter, 65s |
| is-zero | 2 | ✅ 1 iter, 29s | ✅ 1 iter, 44s |
| polynomial-eval | 2 | ✅ 1 iter, 17s | ✅ 1 iter, 29s |
| edwards-add | 3 | ✅ 1 iter, 112s | ✅ 1 iter, 253s |
| weierstrass-add | 3 | ✅ 1 iter, 279s | ✅ 1 iter, 774s |
| inner-product | 3 | ✅ 1 iter, 12s | ✅ 1 iter, 21s |
| **NEG** under-constrained 2-bit range | 2 | ✋ refused (5 iter) | ✋ refused (5 iter) |
| **NEG** vacuous constraint (`x − x = 0` ⊢ `x = 0`) | 1 | ✋ refused (5 iter) | ✋ refused (5 iter) |

## Observations

- **Raw build feedback beat LSP feedback on this suite** — on success (15/15 vs
  14/15) and on wall time in every single cell. The one divergent gadget,
  range-check-8, proved at iteration 1 from raw error text but exhausted all
  5 LSP iterations. One sample is not a verdict, but the direction is consistent
  enough to prioritize a variance run before investing further in LSP mode.
  *[Superseded by run 2: the direction did not replicate — LSP went 45/45 and
  the wall-time gap reversed. Kept as recorded to show why single-sample
  comparisons are not citable.]*
- **Tier 3 was not the bottleneck.** Edwards and Weierstrass curve addition both
  proved at iteration 1 in both modes. Under this model, the difficulty axis the
  tiers were designed around (algebraic depth) is mostly saturated; the
  interesting frontier is lookup/permutation arguments, which no gadget here
  exercises.
- **The negative gadgets did their job.** Every false spec burned its full
  budget without a kernel-accepted proof, in both modes, with the neutral gadget
  names (nothing in what the model sees marks them as traps). This is the
  property that distinguishes "the loop proves true specs" from "the loop proves
  anything you hand it".

## Honest caveats

- **One sample per cell.** pass@1 here equals the pass indicator; there are no
  variance bars. A `--samples 3`+ run is the next step before citing per-gadget
  differences (especially the single LSP failure).
- **Algebraic gate constraints only.** No lookup or permutation arguments — the
  hard part of real halo2 soundness is not represented in the suite yet.
- **Two negatives.** Enough to catch a prove-anything loop, not enough to
  characterize refusal behavior; growing the negative corpus (subtler
  under-constraint bugs) matters more than growing the positive one.
