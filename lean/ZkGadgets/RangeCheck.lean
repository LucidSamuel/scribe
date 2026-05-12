import ZkGadgets.Field
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# 8-bit range check via bit decomposition

Constraint system:
  b_i * (b_i - 1) = 0       for i in [0, 8)   (each bit is boolean)
  sum (b_i * 2^i) = x                           (bit decomposition)

Soundness: if the constraints hold and p > 256, then x is in [0, 256).
-/

variable (p : ℕ) [Fact (Nat.Prime p)] (hp : p > 256)

-- Samuel fills this by hand in week 1. Do not auto-prove.
theorem range_check_8bit_sound
    (x : ZMod p)
    (bits : Fin 8 → ZMod p)
    (h_bit : ∀ i : Fin 8, bits i * (bits i - 1) = 0)
    (h_decomp : (∑ i : Fin 8, bits i * (2 : ZMod p) ^ (i : ℕ)) = x) :
    ∃ k : Fin 256, (k.val : ZMod p) = x := by
  sorry
