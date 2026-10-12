import ZkGadgets.Protocol.EvaluationUniqueness

/-! Explicit finite witnesses refute the precise mutated universal statements.
These are kernel proofs, not unsuccessful searches for proofs. -/
namespace Scribe.Protocol.Mutations
open Polynomial
abbrev K := ZMod 5
instance : Fact (1 < 5) := ⟨by decide⟩
instance : Nontrivial K := inferInstanceAs (Nontrivial (ZMod 5))

-- The pilot pairs one negative with each dependency-family root.
theorem subtraction_as_addition :
    ¬ (∀ (p q : K[X]) (x : K), (p - q).eval x = p.eval x + q.eval x) := by
  intro h
  have bad := h 0 1 0
  norm_num at bad
  exact (by decide : (-1 : K) ≠ 1) bad

theorem dropped_nonzero_difference :
    ¬ (∀ (p q : K[X]), p - q ≠ 0) := by
  intro h
  exact h 0 0 (by simp)

theorem minimum_degree_bound :
    ¬ (∀ (p q : K[X]), (p - q).natDegree ≤ min p.natDegree q.natDegree) := by
  intro h
  have bad := h X 0
  simp at bad

theorem agreement_sum_root :
    ¬ (∀ (p q : K[X]) (x : K), p.eval x = q.eval x → (p + q).IsRoot x) := by
  intro h
  have bad := h 1 1 0 rfl
  norm_num [IsRoot] at bad
  exact (by decide : (2 : K) ≠ 0) bad

theorem dropped_nonzero_root_bound :
    ¬ (∀ (r : K[X]) (S : Finset K),
      (∀ x ∈ S, r.IsRoot x) → S.card ≤ r.natDegree) := by
  intro h
  have bad := h 0 {0} (by simp [IsRoot])
  simp at bad

theorem nonstrict_uniqueness :
    ¬ (∀ (p q : K[X]) (S : Finset K),
      (∀ x ∈ S, p.eval x = q.eval x) →
      max p.natDegree q.natDegree ≤ S.card → p = q) := by
  intro h
  have bad := h X 0 {0} (by simp) (by simp)
  exact X_ne_zero bad

-- Additional assumption-ablation cases guard the final theorem's contract.
theorem omitted_rhs_degree :
    ¬ (∀ (p q : K[X]) (S : Finset K),
      (∀ x ∈ S, p.eval x = q.eval x) → p.natDegree < S.card → p = q) := by
  intro h
  have bad := h 0 X {0} (by simp) (by simp)
  exact X_ne_zero bad.symm

theorem repeated_samples :
    ¬ (∀ (p q : K[X]) (samples : List K),
      (∀ x ∈ samples, p.eval x = q.eval x) →
      max p.natDegree q.natDegree < samples.length → p = q) := by
  intro h
  have bad := h X 0 [0, 0] (by simp) (by simp)
  exact X_ne_zero bad

#audit_axioms subtraction_as_addition
#audit_axioms dropped_nonzero_difference
#audit_axioms minimum_degree_bound
#audit_axioms agreement_sum_root
#audit_axioms dropped_nonzero_root_bound
#audit_axioms nonstrict_uniqueness
#audit_axioms omitted_rhs_degree
#audit_axioms repeated_samples
end Scribe.Protocol.Mutations
