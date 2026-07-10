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

-- Soundness gate: this proof rests only on the trusted kernel axioms.
#audit_axioms conditional_select_sound
-- Verdict-engine probes (C2/C3): a non-boolean selector refutes the conclusion;
-- a genuine select (b = 1 picks x) satisfies every constraint.
#audit_falsifiable conditional_select_sound (p := 5) (b := 2) (x := 0) (y := 0) (z := 1)
#audit_satisfiable conditional_select_sound (p := 5) (b := 1) (x := 3) (y := 4) (z := 3)
