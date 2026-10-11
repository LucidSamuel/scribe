import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import ZkGadgets.Audit

/-! Polynomial evaluation uniqueness, an RS codeword uniqueness building block.
This is not an RS proximity gap, a probabilistic identity test, or a Ragu
protocol soundness theorem. All algebraic definitions are Mathlib's.
-/
namespace Scribe.Protocol
open Polynomial

variable {F : Type*} [Field F]

theorem evaluation_difference (p q : F[X]) (x : F) :
    (p - q).eval x = p.eval x - q.eval x := eval_sub p q x

theorem difference_nonzero (p q : F[X]) (hne : p ≠ q) : p - q ≠ 0 :=
  sub_ne_zero.mpr hne

theorem difference_degree (p q : F[X]) :
    (p - q).natDegree ≤ max p.natDegree q.natDegree := natDegree_sub_le p q

theorem agreement_is_root (p q : F[X]) (x : F) (h : p.eval x = q.eval x) :
    (p - q).IsRoot x := by
  simp [IsRoot, h]

theorem sample_root_bound (r : F[X]) (S : Finset F) (hne : r ≠ 0)
    (hroots : ∀ x ∈ S, r.IsRoot x) : S.card ≤ r.natDegree := by
  apply card_le_degree_of_subset_roots
  intro x hx
  exact (mem_roots hne).mpr (hroots x hx)

/-- Agreement at more distinct points than either degree determines a polynomial. -/
theorem evaluation_unique (p q : F[X]) (S : Finset F)
    (hagrees : ∀ x ∈ S, p.eval x = q.eval x)
    (hdegree : max p.natDegree q.natDegree < S.card) : p = q := by
  by_contra hne
  have hcount := sample_root_bound (p - q) S (difference_nonzero p q hne)
    (fun x hx => agreement_is_root p q x (hagrees x hx))
  have hbound := difference_degree p q
  omega

-- Independent library proof of the same contract, useful for checking the
-- decomposition against a pre-existing result rather than trusting the split.
theorem evaluation_unique_library (p q : F[X]) (S : Finset F)
    (hagrees : ∀ x ∈ S, p.eval x = q.eval x)
    (hdegree : max p.natDegree q.natDegree < S.card) : p = q :=
  eq_of_natDegree_lt_card_of_eval_eq' p q S hagrees hdegree

#audit_axioms evaluation_difference
#audit_axioms difference_nonzero
#audit_axioms difference_degree
#audit_axioms agreement_is_root
#audit_axioms sample_root_bound
#audit_axioms evaluation_unique
#audit_axioms evaluation_unique_library
#audit_uses evaluation_unique
#audit_requires evaluation_unique "eval"
#audit_requires evaluation_unique "natDegree"
end Scribe.Protocol
