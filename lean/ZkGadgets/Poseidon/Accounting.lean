import ZkGadgets.Audit
import Mathlib.Tactic.Ring

/-! Arithmetic of the recursive-node correction in the submitted r3 ledger.
The node prices, base budget and outer-call schedule are explicit assumptions
of this model. These theorems do not verify an implementation or its total cost. -/
namespace Scribe.Poseidon.Orchard.Accounting

-- Depth zero is the base case of budget 63 (j = 6).
def correction : Nat → Nat
  | 0 => 0
  | depth + 1 => 2 * correction depth + 14 * 2 ^ (depth + 6)

theorem correction_closed_form (depth : Nat) :
    correction depth = 7 * 2 ^ (depth + 6) * depth := by
  induction depth with
  | zero => simp [correction]
  | succ depth ih =>
    simp only [correction, ih]
    rw [show depth + 1 + 6 = (depth + 6) + 1 by omega, pow_succ]
    ring

-- (recursive depth above the base, outer-call multiplicity).
def outerCalls : List (Nat × Nat) :=
  [(10, 13), (9, 2), (8, 2), (7, 2), (6, 1),
   (5, 1), (4, 2), (3, 2), (2, 1), (1, 2)]

def totalCorrection : Nat :=
  (outerCalls.map fun (depth, count) => count * correction depth).sum

theorem two_output_price : 8 * 2 + 4 + 2 = (22 : Nat) := by decide

theorem total_correction : totalCorrection = 66732288 := by decide

theorem corrected_total : 50567592471 + totalCorrection = 50634324759 := by
  rw [total_correction]

theorem corrected_memory :
    126200572 + ((8 * 22 + 3) - (8 * 20 + 3)) * 4 = (126200636 : Nat) := by decide

#audit_axioms correction_closed_form
#audit_axioms total_correction
#audit_axioms corrected_total
#audit_axioms corrected_memory
end Scribe.Poseidon.Orchard.Accounting
