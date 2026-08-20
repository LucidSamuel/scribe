import ZkGadgets.Field
import ZkGadgets.Audit
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# 8-bit range check via bit decomposition

Constraint system:
  b_i * (b_i - 1) = 0       for i in [0, 8)   (each bit is boolean)
  sum (b_i * 2^i) = x                           (bit decomposition)

Soundness: if the constraints hold and p > 256, then `x` is genuinely a byte,
i.e. its canonical natural representative is in [0, 256).

The conclusion is `ZMod.val x < 256`, NOT `∃ k : Fin 256, (k.val : ZMod p) = x`.
The existential is vacuous whenever `p ≤ 256` (every field element is then the cast
of some byte), so it would state something strictly weaker than "x is a byte" and
could be proved without ever using `hp`. `ZMod.val x < 256` cannot be proved without
`hp` — the bound `p > 256` is what makes `ZMod.val` agree with the integer value.

Two theorems live here:

* `range_check_8bit_sound_indexed` — the human-shaped statement
  (`bits : Fin 8 → ZMod p`, ∀-quantified boolean constraints, `Finset.sum`
  decomposition), where the proof lives.
* `range_check_8bit_sound` — the **bridge theorem** (binding remediation,
  2026-08-21): the exact statement `lean_emit::soundness_statement` regenerates
  from `examples/range-check/gadget.toml` — nine flat wires `x b0 … b7`, eight
  individual boolean constraints, one flat weighted sum — proven from the
  indexed form by instantiating `bits := ![b0, …, b7]` and discharging the
  indexing / sum-unfolding bookkeeping. That bookkeeping is the equivalence
  lemma the binding probe found missing — asserted by resemblance until now,
  kernel-checked here.
-/

variable (p : ℕ) [Fact (Nat.Prime p)]

theorem range_check_8bit_sound_indexed
    -- `hp` is an explicit, load-bearing hypothesis: the proof fails without it, and
    -- `#check @range_check_8bit_sound_indexed` shows it in the signature (it is not dropped).
    (hp : p > 256)
    (x : ZMod p)
    (bits : Fin 8 → ZMod p)
    (h_bit : ∀ i : Fin 8, bits i * (bits i - 1) = 0)
    (h_decomp : (∑ i : Fin 8, bits i * (2 : ZMod p) ^ (i : ℕ)) = x) :
    ZMod.val x < 256 := by
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
  -- x is the cast of the natural weighted sum N, with N < 256.
  have hxN : x = ((∑ i : Fin 8, nb i * 2 ^ (i : ℕ) : ℕ) : ZMod p) := by
    rw [← h_decomp]
    push_cast
    congr 1; ext i
    rw [hcast i]
  -- N < 256 < p (this is where `hp` is used), so `ZMod.val` of the cast is exactly N.
  have hNp : (∑ i : Fin 8, nb i * 2 ^ (i : ℕ)) < p := by omega
  rw [hxN, ZMod.val_natCast_of_lt hNp]
  exact hlt

/-- Non-vacuity witness: the byte bound `ZMod.val x < 256` is a genuine restriction,
    not `True` in disguise. In `ZMod 257` (prime, > 256) the element `256` refutes the
    conclusion — so the soundness theorem is saying something real, and dropping the
    constraints (or the `p > 256` hypothesis) would make it false. This is the kind of
    refutation a spec-level search should always be able to find for an honest spec. -/
example : ¬ ((256 : ZMod 257).val < 256) := by decide

-- Verdict-engine guards (C1): fail the build if the `p > 256` bound is ever dropped
-- from the signature, or if the proof stops using a declared hypothesis.
#audit_requires range_check_8bit_sound_indexed "p > 256"
#audit_uses range_check_8bit_sound_indexed
-- Soundness gate: the proof rests only on the trusted kernel axioms.
#audit_axioms range_check_8bit_sound_indexed
-- Verdict-engine probes (C2/C3), derived from the signature itself:
-- the conclusion must be falsifiable (256 is a field element of ZMod 257 whose
-- canonical value is not < 256 — the old ∃-spec was unfalsifiable and fails this),
-- and the constraints must be satisfiable (the all-ones byte 255 meets them all).
#audit_falsifiable range_check_8bit_sound_indexed (p := 257) (x := 256)
#audit_satisfiable range_check_8bit_sound_indexed (p := 257) (x := 255) (bits := fun _ => 1)

/-- **Bridge theorem**: the IR-shaped soundness statement, exactly as
    `lean_emit::soundness_statement` regenerates it from
    `examples/range-check/gadget.toml` — nine flat wires, eight individual
    boolean constraints (`bᵢ * bᵢ - bᵢ = 0`), one flat weighted decomposition.
    Proven from `range_check_8bit_sound_indexed` with `bits := ![b0, …, b7]`:
    the per-bit obligations reduce by `fin_cases` + `linear_combination`, and
    the `Finset.sum` obligation unfolds with `Fin.sum_univ_succ` down to the
    flat sum, closed by `linear_combination h_decomposition`. -/
theorem range_check_8bit_sound
    (x b0 b1 b2 b3 b4 b5 b6 b7 : ZMod p)
    (hp : p > 256)
    (h_bit_0 : b0 * b0 - b0 = 0)
    (h_bit_1 : b1 * b1 - b1 = 0)
    (h_bit_2 : b2 * b2 - b2 = 0)
    (h_bit_3 : b3 * b3 - b3 = 0)
    (h_bit_4 : b4 * b4 - b4 = 0)
    (h_bit_5 : b5 * b5 - b5 = 0)
    (h_bit_6 : b6 * b6 - b6 = 0)
    (h_bit_7 : b7 * b7 - b7 = 0)
    (h_decomposition :
      b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5 + 64 * b6 + 128 * b7 - x = 0) :
    ZMod.val x < 256 := by
  refine range_check_8bit_sound_indexed p hp x ![b0, b1, b2, b3, b4, b5, b6, b7] ?_ ?_
  · intro i
    fin_cases i
    · show b0 * (b0 - 1) = 0; linear_combination h_bit_0
    · show b1 * (b1 - 1) = 0; linear_combination h_bit_1
    · show b2 * (b2 - 1) = 0; linear_combination h_bit_2
    · show b3 * (b3 - 1) = 0; linear_combination h_bit_3
    · show b4 * (b4 - 1) = 0; linear_combination h_bit_4
    · show b5 * (b5 - 1) = 0; linear_combination h_bit_5
    · show b6 * (b6 - 1) = 0; linear_combination h_bit_6
    · show b7 * (b7 - 1) = 0; linear_combination h_bit_7
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, pow_succ, pow_zero]
    linear_combination h_decomposition

-- Soundness gate for the bridge, plus C1: every flat constraint hypothesis is used.
#audit_requires range_check_8bit_sound "p > 256"
#audit_uses range_check_8bit_sound
#audit_axioms range_check_8bit_sound
-- C2/C3 against the IR shape: same refutation (256 in ZMod 257), same all-ones
-- witness (255 = 1 + 2 + 4 + … + 128), spelled on the flat wires.
#audit_falsifiable range_check_8bit_sound (p := 257) (x := 256)
#audit_satisfiable range_check_8bit_sound (p := 257) (x := 255)
  (b0 := 1) (b1 := 1) (b2 := 1) (b3 := 1) (b4 := 1) (b5 := 1) (b6 := 1) (b7 := 1)

-- The ∃-search over Fin 256 in the decoy's `decide` recurses past the default depth.
set_option maxRecDepth 4096 in
/-- Regression demonstration for C2: the pre-fix spec concluded
    `∃ k : Fin 256, (k.val : ZMod p) = x`, which is vacuously true whenever
    `p ≤ 256` — here it is at `p = 5`, proved with no range hypothesis at all
    (every field element is the cast of some byte). -/
private theorem vacuous_spec_decoy :
    ∀ x : ZMod 5, ∃ k : Fin 256, ((k.val : ℕ) : ZMod 5) = x := by decide

-- ...and `#audit_falsifiable` rejects it: no instantiation refutes that
-- conclusion, which is exactly what "the spec has no content" means. Asserted
-- through the core function so this build stays green while proving the probe
-- would have caught the original bug.
run_cmd Lean.Elab.Command.liftTermElabM do
  let two ← `(2)
  let rejected ← try
      ScribeAudit.probeFalsifiable ``vacuous_spec_decoy #[(`x, two)]
      pure false
    catch _ => pure true
  unless rejected do
    throwError "C2 regression test failed: the vacuous existential spec was not rejected"
