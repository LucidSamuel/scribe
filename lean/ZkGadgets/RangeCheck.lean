import ZkGadgets.Field
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# 8-bit range check via bit decomposition

Constraint system:
  b_i * (b_i - 1) = 0       for i in [0, 8)   (each bit is boolean)
  sum (b_i * 2^i) = x                           (bit decomposition)

Soundness: if the constraints hold and p > 256, then x is in [0, 256).
-/

variable (p : ℕ) [Fact (Nat.Prime p)] (hp : p > 256)

theorem range_check_8bit_sound
    (x : ZMod p)
    (bits : Fin 8 → ZMod p)
    (h_bit : ∀ i : Fin 8, bits i * (bits i - 1) = 0)
    (h_decomp : (∑ i : Fin 8, bits i * (2 : ZMod p) ^ (i : ℕ)) = x) :
    ∃ k : Fin 256, (k.val : ZMod p) = x := by
  -- Each bit is 0 or 1 in ZMod p
  have h01 : ∀ i, bits i = 0 ∨ bits i = 1 := fun i => bit_boolean p (bits i) (h_bit i)
  -- Natural representative for each bit
  set nb : Fin 8 → ℕ := fun i => if bits i = 1 then 1 else 0 with nb_def
  -- Each bit equals its natural representative
  have hcast : ∀ i, bits i = (nb i : ZMod p) := by
    intro i; simp only [nb_def]
    rcases h01 i with h | h <;> simp [h]
  -- Each natural bit is ≤ 1
  have hle : ∀ i : Fin 8, nb i ≤ 1 := by
    intro i; simp only [nb_def]; split <;> omega
  -- The natural weighted sum is < 256
  have hlt : ∑ i : Fin 8, nb i * 2 ^ (i : ℕ) < 256 := by
    apply Nat.lt_of_le_of_lt
    · apply Finset.sum_le_sum; intro i _
      exact Nat.mul_le_mul_right _ (hle i)
    · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
      omega
  -- Provide the Fin 256 witness
  exact ⟨⟨∑ i : Fin 8, nb i * 2 ^ (i : ℕ), hlt⟩, by
    rw [← h_decomp]
    push_cast
    congr 1; ext i
    rw [hcast i]⟩
