import ZkGadgets.Field

/-!
# Conditional select

Constraint system:
  b * (b - 1) = 0                 (b is boolean)
  b * x + (1 - b) * y = z         (conditional select)

Soundness: if constraints hold, then (b = 0 ∧ z = y) ∨ (b = 1 ∧ z = x).
-/

variable (p : ℕ) [Fact (Nat.Prime p)]

theorem conditional_select_sound
    (b x y z : ZMod p)
    (h_bool : b * (b - 1) = 0)
    (h_sel : b * x + (1 - b) * y = z) :
    (b = 0 ∧ z = y) ∨ (b = 1 ∧ z = x) := by
  rcases bit_boolean p b h_bool with hb | hb <;> simp [hb] at h_sel ⊢
  · exact h_sel.symm
  · exact h_sel.symm
