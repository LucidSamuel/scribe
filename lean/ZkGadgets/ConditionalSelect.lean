import ZkGadgets.Field
import Mathlib.Tactic.LinearCombination

/-!
# Conditional select

Constraint system:
  b * (b - 1) = 0                 (b is boolean)
  b * x + (1 - b) * y = z         (conditional select)

Soundness: if constraints hold, then (b = 0 ∧ z = y) ∨ (b = 1 ∧ z = x).

Two theorems live here:

* `conditional_select_sound_factored` — the human-shaped statement
  (`b * (b - 1) = 0`, `b * x + (1 - b) * y = z`), where the proof lives.
* `conditional_select_sound` — the **bridge theorem** (binding remediation,
  2026-08-21): the exact statement `lean_emit::soundness_statement` regenerates
  from `examples/conditional-select/gadget.toml`, proven from the factored form
  by discharging the two ring-equalities with `linear_combination`. This is the
  equivalence the binding probe found missing — asserted by resemblance until
  now, kernel-checked here.
-/

variable (p : ℕ) [Fact (Nat.Prime p)]

theorem conditional_select_sound_factored
    (b x y z : ZMod p)
    (h_bool : b * (b - 1) = 0)
    (h_sel : b * x + (1 - b) * y = z) :
    (b = 0 ∧ z = y) ∨ (b = 1 ∧ z = x) := by
  rcases bit_boolean p b h_bool with hb | hb <;> simp [hb] at h_sel ⊢
  · exact h_sel.symm
  · exact h_sel.symm

/-- **Bridge theorem**: the IR-shaped soundness statement — flat constraint
    polynomials `b * b - b = 0` and `b * x + y - b * y - z = 0` exactly as
    `examples/conditional-select/gadget.toml` regenerates them. The two
    hypothesis conversions are ring equalities, each discharged by
    `linear_combination`; the conclusion is shared verbatim. -/
theorem conditional_select_sound
    (b x y z : ZMod p)
    (h_boolean : b * b - b = 0)
    (h_select : b * x + y - b * y - z = 0) :
    (b = 0 ∧ z = y) ∨ (b = 1 ∧ z = x) :=
  conditional_select_sound_factored p b x y z
    (by linear_combination h_boolean)
    (by linear_combination h_select)

-- Soundness gates: both proofs rest only on the trusted kernel axioms.
#audit_axioms conditional_select_sound_factored
#audit_axioms conditional_select_sound
-- C1: the bridge must use every declared constraint hypothesis.
#audit_uses conditional_select_sound
-- Verdict-engine probes (C2/C3): a non-boolean selector refutes the conclusion;
-- a genuine select (b = 1 picks x) satisfies every constraint. Run against both
-- statement shapes.
#audit_falsifiable conditional_select_sound_factored (p := 5) (b := 2) (x := 0) (y := 0) (z := 1)
#audit_satisfiable conditional_select_sound_factored (p := 5) (b := 1) (x := 3) (y := 4) (z := 3)
#audit_falsifiable conditional_select_sound (p := 5) (b := 2) (x := 0) (y := 0) (z := 1)
#audit_satisfiable conditional_select_sound (p := 5) (b := 1) (x := 3) (y := 4) (z := 3)
