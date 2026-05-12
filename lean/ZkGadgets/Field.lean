import Mathlib.Data.ZMod.Basic

/-!
# Field helpers for ZK gadget verification

Common lemmas for working with ZMod p in constraint system proofs.
These are stubs — filled in as needed during proof work.
-/

variable (p : ℕ) [Fact (Nat.Prime p)]

-- Stub: a field element satisfying x * (x - 1) = 0 is 0 or 1.
-- Samuel fills this stub during week 1.
theorem bit_boolean (b : ZMod p) (h : b * (b - 1) = 0) :
    b = 0 ∨ b = 1 := by
  sorry

-- Stub: casting from Fin n to ZMod p is injective when n < p.
-- Samuel fills this stub during week 1.
theorem fin_val_cast_injective (n : ℕ) (hn : n < p) :
    Function.Injective (fun (k : Fin n) => (k.val : ZMod p)) := by
  sorry
