-- Extra imports needed for the soundness proof (not in Halva's default output).
-- halva-bridge moves these into the generated file header.
import Mathlib.Tactic.LinearCombination

/-- Specification: the Fibonacci circuit lays out the recurrence f(i+2) = f(i+1) + f(i)
    across 8 enabled rows, seeded by the two instance inputs and copied row-to-row.
    Unwinding the add gate and the copy constraints, the third instance cell (the
    circuit's public output) must equal the 9th term of the recurrence:
    21·f(0) + 34·f(1). This is the semantic meaning a Halva extraction cannot state. -/
def Spec (c: ValidCircuit P P_Prime): Prop :=
  c.get_instance 0 2 = 21 * c.get_instance 0 0 + 34 * c.get_instance 0 1

/-- Soundness: if the circuit meets all halo2 constraints (extracted by Halva),
    then its public output is the correct Fibonacci linear combination of the inputs.
    Conditional on Halva's extraction being faithful to halo2 execution semantics. -/
theorem soundness (c: ValidCircuit P P_Prime) (h: meets_constraints c): Spec c := by
  sorry
