# why

ZK circuits are high-assurance code that rarely gets high-assurance verification. Formal verification of constraint systems exists — Clean, zk-lean, sp1-lean, Garden, acl2-jolt — but the proof work is manual and slow.

LLMs are getting good at Lean. Not great, but good enough to close routine goals with a feedback loop: try a tactic, read the error, try again. Lean's kernel is the oracle. `lake build` returning 0 is not an approximation — it is a proof certificate.

scribe connects these two facts. It takes a constraint system as a flat IR (no framework dependency), emits a Lean 4 scaffold with the theorem statement and hypotheses, and then drives an LLM to fill in the proof body. The human writes the spec and adjudicates when the LLM gets stuck. The machine does the tactic grind.

The v1 target is deliberately small: an 8-bit range check via bit decomposition. One gadget, one theorem, one proof. The tool's value is not in the complexity of what it verifies but in the automation of how it gets there.
