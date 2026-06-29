-- Extra imports needed for the soundness proof (not in Halva's default output).
-- halva-bridge moves these into the generated file header.
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-- Specification: at every enabled row (fixed enable column 0 = 1), the binary-number
    chip witnesses a 2-bit value. Its two advice cells are genuine bits, the fixed
    "value" cell is their little-endian recomposition 2·b₀ + b₁, and the two bits are
    never both set — so the encoded value stays in range {0, 1, 2}. These are the
    semantic guarantees behind Halva's four polynomial gates. Requires P prime so the
    field has no zero divisors (used to split the boolean product constraints). -/
def Spec (c: ValidCircuit P P_Prime): Prop :=
  ∀ row : ℕ, c.get_fixed 0 row = 1 →
    (c.get_advice 0 row = 0 ∨ c.get_advice 0 row = 1) ∧
    (c.get_advice 1 row = 0 ∨ c.get_advice 1 row = 1) ∧
    c.get_fixed 1 row = 2 * c.get_advice 0 row + c.get_advice 1 row ∧
    c.get_advice 0 row * c.get_advice 1 row = 0

/-- Soundness: if the circuit meets all halo2 constraints (extracted by Halva),
    then every enabled row satisfies the binary-number specification.
    Conditional on Halva's extraction being faithful to halo2 execution semantics. -/
theorem soundness (c: ValidCircuit P P_Prime) (h: meets_constraints c): Spec c := by
  sorry
