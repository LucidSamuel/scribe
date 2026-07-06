import ZkGadgets.Audit
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

set_option linter.unusedVariables false

namespace Fibonacci.Ex1

def S_T_from_P (S T P : ℕ) : Prop :=
  (2^S * T = P - 1) ∧
  (∀ s' t': ℕ, 2^s' * t' = P - 1 → s' ≤ S)
def multiplicative_generator (P: ℕ) (mult_gen: ZMod P) : Prop :=
  mult_gen ^ P = 1
structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) where
  Advice: ℕ → ℕ → ZMod P
  AdviceUnassigned: ℕ → ℕ → ZMod P
  AdvicePhase: ℕ → ℕ
  Fixed: ℕ → ℕ → ZMod P
  FixedUnassigned: ℕ → ℕ → ZMod P
  Instance: ℕ → ℕ → ZMod P
  InstanceUnassigned: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
  Challenges: (ℕ → ℕ → ZMod P) → ℕ → ℕ → ZMod P
  num_blinding_factors: ℕ
  S: ℕ
  T: ℕ
  k: ℕ
  mult_gen: ZMod P
variable {P: ℕ} {P_Prime: Nat.Prime P}
def Circuit.isValid (c: Circuit P P_Prime) : Prop :=
  S_T_from_P c.S c.T P ∧
  multiplicative_generator P c.mult_gen ∧ (
  ∀ advice1 advice2: ℕ → ℕ → ZMod P, ∀ phase: ℕ,
    (∀ row col, (col < 3 ∧ c.AdvicePhase col ≤ phase) → advice1 col row = advice2 col row) →
    (∀ i, c.Challenges advice1 i phase = c.Challenges advice2 i phase)
  )
abbrev ValidCircuit (P: ℕ) (P_Prime: Nat.Prime P) : Type := {c: Circuit P P_Prime // c.isValid}
namespace ValidCircuit
def get_advice (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => c.1.Advice col row
def get_fixed (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => c.1.Fixed col row
def get_instance (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => c.1.Instance col row
def get_selector (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => c.1.Selector col row
def get_challenge (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ idx phase => c.1.Challenges c.1.Advice idx phase
def k (c: ValidCircuit P P_Prime) := c.1.k
def n (c: ValidCircuit P P_Prime) := 2^c.k
def usable_rows (c: ValidCircuit P P_Prime) := c.n - (c.1.num_blinding_factors + 1)
def S (c: ValidCircuit P P_Prime) := c.1.S
def T (c: ValidCircuit P P_Prime) := c.1.T
def mult_gen (c: ValidCircuit P P_Prime) := c.1.mult_gen
def root_of_unity (c: ValidCircuit P P_Prime) : ZMod P := c.mult_gen ^ c.T
def delta (c: ValidCircuit P P_Prime) : ZMod P := c.mult_gen ^ (2^c.S)
end ValidCircuit
def is_shuffle (c: ValidCircuit P P_Prime) (shuffle: ℕ → ℕ): Prop :=
  ∃ inv: ℕ → ℕ,
  ∀ row: ℕ,
    inv (shuffle row) = row ∧
    (row ≥ c.usable_rows → shuffle row = row)
def sufficient_rows (c: ValidCircuit P P_Prime) : Prop :=
  c.n ≥ 8 --cs.minimum_rows
--End preamble

def copy_0 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 0 0 = c.get_instance 0 0
def copy_1 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 1 0 = c.get_instance 0 1
def copy_2 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 0 1 = c.get_advice 1 0
def copy_3 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 1 1 = c.get_advice 2 0
def copy_4 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 0 2 = c.get_advice 2 0
def copy_5 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 1 2 = c.get_advice 2 1
def copy_6 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 0 3 = c.get_advice 2 1
def copy_7 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 1 3 = c.get_advice 2 2
def copy_8 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 0 4 = c.get_advice 2 2
def copy_9 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 1 4 = c.get_advice 2 3
def copy_0_to_9 (c: ValidCircuit P P_Prime) : Prop :=
  copy_0 c ∧ copy_1 c ∧ copy_2 c ∧ copy_3 c ∧ copy_4 c ∧ copy_5 c ∧ copy_6 c ∧ copy_7 c ∧ copy_8 c ∧ copy_9 c
def copy_10 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 0 5 = c.get_advice 2 3
def copy_11 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 1 5 = c.get_advice 2 4
def copy_12 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 0 6 = c.get_advice 2 4
def copy_13 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 1 6 = c.get_advice 2 5
def copy_14 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 0 7 = c.get_advice 2 5
def copy_15 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 1 7 = c.get_advice 2 6
def copy_16 (c: ValidCircuit P P_Prime) : Prop :=
  c.get_advice 2 7 = c.get_instance 0 2
def all_copy_constraints (c: ValidCircuit P P_Prime): Prop :=
  copy_0_to_9 c ∧ copy_10 c ∧ copy_11 c ∧ copy_12 c ∧ copy_13 c ∧ copy_14 c ∧ copy_15 c ∧ copy_16 c
def selector_func_col_0 (c: ValidCircuit P P_Prime) : ℕ → ZMod P :=
  λ row =>
  if row < 8 then 1
  else 0
def selector_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => selector_func_col_0 c row
    | _ => 0
def fixed_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | _ => c.1.FixedUnassigned col row
def advice_phase (c: ValidCircuit P P_Prime) : ℕ → ℕ :=
  λ col => match col with
  | _ => 0
def gate_0 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1 name: "add" part 1/1
  ∀ row: ℕ, (c.get_selector 0 row) * (((c.get_advice 0 row) + (c.get_advice 1 row)) + (-(c.get_advice 2 row))) = 0
def all_gates (c: ValidCircuit P P_Prime): Prop :=
  gate_0 c
def all_lookups (c: ValidCircuit P P_Prime): Prop :=
  true
def all_shuffles (c: ValidCircuit P P_Prime) : Prop := true
def meets_constraints (c: ValidCircuit P P_Prime): Prop :=
  sufficient_rows c ∧
  c.1.num_blinding_factors = 5 ∧
  c.1.Selector = selector_func c ∧
  c.1.Fixed = fixed_func c ∧
  c.1.AdvicePhase = advice_phase c ∧
  c.usable_rows ≥ 8 ∧
  all_gates c ∧
  all_copy_constraints c ∧
  all_lookups c ∧
  all_shuffles c ∧
  ∀ col row: ℕ, (row < c.n ∧ row ≥ c.usable_rows) → c.1.Instance col row = c.1.InstanceUnassigned col row

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
  obtain ⟨_, _, hsel, _, _, _, hgates, hcopies, _, _, _⟩ := h
  -- The add gate fires on every enabled row (selector = 1 for rows < 8), so the
  -- third advice cell is the sum of the first two on each of those rows.
  unfold all_gates gate_0 at hgates
  have hg : ∀ r : ℕ, r < 8 →
      c.get_advice 0 r + c.get_advice 1 r + -(c.get_advice 2 r) = 0 := by
    intro r hr
    have hsr : c.get_selector 0 r = 1 := by
      show c.1.Selector 0 r = 1
      rw [hsel]
      show (if r < 8 then (1 : ZMod P) else 0) = 1
      rw [if_pos hr]
    have hrow := hgates r
    rw [hsr, one_mul] at hrow
    exact hrow
  -- The copy constraints wire cells across rows (and to the instance column).
  simp only [all_copy_constraints, copy_0_to_9, copy_0, copy_1, copy_2, copy_3, copy_4,
    copy_5, copy_6, copy_7, copy_8, copy_9, copy_10, copy_11, copy_12, copy_13, copy_14,
    copy_15, copy_16] at hcopies
  obtain ⟨⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9⟩,
    hc10, hc11, hc12, hc13, hc14, hc15, hc16⟩ := hcopies
  -- Walk the recurrence row by row; each a₂(r) is a fixed linear combination of the
  -- two inputs (the Fibonacci coefficients), derived from the gate + the wiring.
  have e0 : c.get_advice 2 0 = c.get_instance 0 0 + c.get_instance 0 1 := by
    linear_combination -(hg 0 (by omega)) + hc0 + hc1
  have e1 : c.get_advice 2 1 = c.get_instance 0 0 + 2 * c.get_instance 0 1 := by
    linear_combination -(hg 1 (by omega)) + hc2 + hc1 + hc3 + e0
  have e2 : c.get_advice 2 2 = 2 * c.get_instance 0 0 + 3 * c.get_instance 0 1 := by
    linear_combination -(hg 2 (by omega)) + hc4 + e0 + hc5 + e1
  have e3 : c.get_advice 2 3 = 3 * c.get_instance 0 0 + 5 * c.get_instance 0 1 := by
    linear_combination -(hg 3 (by omega)) + hc6 + e1 + hc7 + e2
  have e4 : c.get_advice 2 4 = 5 * c.get_instance 0 0 + 8 * c.get_instance 0 1 := by
    linear_combination -(hg 4 (by omega)) + hc8 + e2 + hc9 + e3
  have e5 : c.get_advice 2 5 = 8 * c.get_instance 0 0 + 13 * c.get_instance 0 1 := by
    linear_combination -(hg 5 (by omega)) + hc10 + e3 + hc11 + e4
  have e6 : c.get_advice 2 6 = 13 * c.get_instance 0 0 + 21 * c.get_instance 0 1 := by
    linear_combination -(hg 6 (by omega)) + hc12 + e4 + hc13 + e5
  have e7 : c.get_advice 2 7 = 21 * c.get_instance 0 0 + 34 * c.get_instance 0 1 := by
    linear_combination -(hg 7 (by omega)) + hc14 + e5 + hc15 + e6
  -- The last copy wires a₂(7) into the public output cell.
  unfold Spec
  linear_combination e7 - hc16

end Fibonacci.Ex1

-- Soundness gate: the proof rests only on the trusted kernel axioms.
#audit_axioms Fibonacci.Ex1.soundness
