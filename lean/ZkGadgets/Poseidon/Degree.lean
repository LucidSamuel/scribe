import ZkGadgets.Poseidon.Orchard
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Baseline degree bound for the exact pinned round schedule.
This does not establish either claimed skipped full round or H-ONE/H-NORMAL. -/
namespace Scribe.Poseidon.Orchard
open Polynomial
noncomputable section

structure PolyState where
  a : Polynomial F
  b : Polynomial F
  c : Polynomial F

def evalState (s : PolyState) (x : F) : State :=
  ⟨s.a.eval x, s.b.eval x, s.c.eval x⟩

def bounded (s : PolyState) (d : Nat) : Prop :=
  s.a.natDegree ≤ d ∧ s.b.natDegree ≤ d ∧ s.c.natDegree ≤ d

def layer (full : Bool) (p : Polynomial F) (c : Nat) : Polynomial F :=
  if full then (p + C (c : F)) ^ 5 else p + C (c : F)

def linearRow (v : Nat × Nat × Nat) (a b c : Polynomial F) : Polynomial F :=
  C (v.1 : F) * a + C (v.2.1 : F) * b + C (v.2.2 : F) * c

def polyRound (index : Nat) (s : PolyState) : PolyState :=
  let rc := roundConstants[index]!
  let full := index < 4 || index ≥ 60
  let a := layer true s.a rc.1
  let b := layer full s.b rc.2.1
  let c := layer full s.c rc.2.2
  ⟨linearRow mds[0]! a b c, linearRow mds[1]! a b c, linearRow mds[2]! a b c⟩

theorem eval_polyRound (index : Nat) (s : PolyState) (x : F) :
    evalState (polyRound index s) x = roundStep index (evalState s x) := by
  simp only [evalState, polyRound, layer, linearRow, roundStep,
    ↓reduceIte]
  split_ifs <;> simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

private theorem layer_bound (p : Polynomial F) (c d : Nat) (full : Bool)
    (h : p.natDegree ≤ d) : (layer full p c).natDegree ≤ 5 * d := by
  have hc : (p + C (c : F)).natDegree ≤ d :=
    natDegree_add_le_of_degree_le h (by simp)
  unfold layer
  split_ifs
  · exact natDegree_pow_le_of_le 5 hc
  · omega

private theorem linearRow_bound (v : Nat × Nat × Nat) (a b c : Polynomial F)
    (d : Nat) (ha : a.natDegree ≤ d) (hb : b.natDegree ≤ d) (hc : c.natDegree ≤ d) :
    (linearRow v a b c).natDegree ≤ d := by
  have scalar (k : F) (p : Polynomial F) (hp : p.natDegree ≤ d) :
      (C k * p).natDegree ≤ d := by
    exact natDegree_mul_le.trans (by simpa using hp)
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (scalar _ _ ha) (scalar _ _ hb)) (scalar _ _ hc)

theorem polyRound_bound (index : Nat) (s : PolyState) (d : Nat) (h : bounded s d) :
    bounded (polyRound index s) (5 * d) := by
  rcases h with ⟨ha, hb, hc⟩
  unfold bounded polyRound
  exact ⟨linearRow_bound _ _ _ _ _ (layer_bound _ _ _ _ ha) (layer_bound _ _ _ _ hb) (layer_bound _ _ _ _ hc),
    linearRow_bound _ _ _ _ _ (layer_bound _ _ _ _ ha) (layer_bound _ _ _ _ hb) (layer_bound _ _ _ _ hc),
    linearRow_bound _ _ _ _ _ (layer_bound _ _ _ _ ha) (layer_bound _ _ _ _ hb) (layer_bound _ _ _ _ hc)⟩

def polyPermute (indices : List Nat) (s : PolyState) : PolyState :=
  indices.foldl (fun state index => polyRound index state) s

theorem eval_polyPermute (indices : List Nat) (s : PolyState) (x : F) :
    evalState (polyPermute indices s) x =
      indices.foldl (fun state index => roundStep index state) (evalState s x) := by
  induction indices generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simpa [polyPermute, eval_polyRound] using ih (polyRound i s)

theorem polyPermute_bound (indices : List Nat) (s : PolyState) (d : Nat)
    (h : bounded s d) : bounded (polyPermute indices s) (5 ^ indices.length * d) := by
  induction indices generalizing s d with
  | nil => simpa [polyPermute] using h
  | cons i rest ih =>
    have bound := ih (polyRound i s) (5 * d) (polyRound_bound i s d h)
    simpa [polyPermute, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem orchard_degree_bound (r : Rounds) (s : PolyState) (h : bounded s 1) :
    bounded (polyPermute (schedule r) s) (5 ^ (8 + r.val)) := by
  simpa [schedule_length] using polyPermute_bound (schedule r) s 1 h

#audit_axioms eval_polyRound
#audit_axioms eval_polyPermute
#audit_axioms polyRound_bound
#audit_axioms orchard_degree_bound
end
end Scribe.Poseidon.Orchard
