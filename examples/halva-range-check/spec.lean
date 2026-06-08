-- Extra imports needed for the soundness proof (not in Halva's default output).
-- halva-bridge moves these into the generated file header.
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-- Specification: when the range-check selector is enabled at a row,
    the advice value in that row is in [0, 10).
    Requires the prime P > 10 so that ZMod P casts are injective on Fin 10. -/
def Spec (c: ValidCircuit P P_Prime) (hp: P > 10): Prop :=
  ∀ row : ℕ, c.get_selector 0 row = 1 →
    ∃ k : Fin 10, (k.val : ZMod P) = c.get_advice 0 row

/-- Soundness: if the circuit meets all halo2 constraints (extracted by Halva),
    then it satisfies the range-check specification.
    Conditional on Halva's extraction being faithful to halo2 execution semantics. -/
theorem soundness (c: ValidCircuit P P_Prime) (hp: P > 10)
    (h: meets_constraints c): Spec c hp := by
  sorry
