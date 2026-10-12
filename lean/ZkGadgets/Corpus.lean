import ZkGadgets.Corpus.Refuterange_check_2bit
import ZkGadgets.Corpus.Refutezero_check
import ZkGadgets.Corpus.Refutezero_indicator
import ZkGadgets.Corpus.Refuteswap_pair
import ZkGadgets.Corpus.Refuteinverse_gate
import ZkGadgets.Corpus.Proveragu_boolean
import ZkGadgets.Corpus.Proveboolean_check
import ZkGadgets.Corpus.Proveadd_gate

/-!
# Corpus evidence aggregator

Imports every kernel-checked artifact behind
`corpus/circuits/discrimination-report.json` — the five refutations that
caught the negatives and the three proofs that accepted the positives — so
the default `lake build` re-checks the evidence itself, not just the JSON
summary. If any artifact breaks, the build goes red while the report would
otherwise have stayed green; per-instance metadata (outcome, artifact hash,
iterations) lives in `corpus/circuits/validation-artifacts.json`.
-/
