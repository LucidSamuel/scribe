import ZkGadgets.Poseidon.Orchard

/-! One kernel-checked reference vector. It is not a collision witness. -/
namespace Scribe.Poseidon.Orchard
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem zero_r3 : digest? 3 0 0 = some 23920805377093618800924611112976634518331945812171967564107961257532193172290 := by
  decide

#audit_axioms zero_r3
end Scribe.Poseidon.Orchard
