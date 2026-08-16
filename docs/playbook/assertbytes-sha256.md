# zkGolf Reference-Solution Proof Pattern Catalog
## Corpus: `Solution/AssertBytes/*`, `Challenge/Instances/AssertBytes/*`, `Solution/SHA256/*`, `Challenge/Instances/SHA256/*`

---

## 0. The five obligations (trusted statement shapes)

Both challenges pin exactly six declarations (`Challenge/Instances/{AssertBytes,SHA256}/Challenge.lean`, lines 21–34):

```lean
def main : Var Input (F circomPrime) → Circuit (F circomPrime) (Var Output (F circomPrime))
instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main
theorem soundness   : GeneralFormalCircuit.Soundness   (F circomPrime) main Assumptions      Spec
theorem completeness: GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec
theorem mainCost    : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩
theorem isR1CS      : Challenge.CostR1CS.isR1CS main
theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env => eval env input) →
  Circuit.ComputableWitnesses (main input) n
```

`Challenge/Instances/*/Cost.lean` is a 2-line stub (`allocations := 42`, `constraints := 42`) that the checker **overwrites** with the solver's claimed numbers; solutions re-declare `@[reducible] def allocations/constraints` locally (`Solution/AssertBytes/Main.lean:113-114` = `128`/`144`; `Solution/SHA256/Main.lean:650-651` = `204224`/`209586`).

---

# 1. SOUNDNESS PATTERNS

### S1. `circuit_proof_start` + unfold-list opener (universal entry point)
- **Where**: every soundness proof. `Solution/AssertBytes/Main.lean:32`; `Num2Bits.lean:48`; `SHA256/Add32.lean:78`; `SHA256/Main.lean:37`.
- **Goal before**: `GeneralFormalCircuit.Soundness … main Assumptions Spec` / `Soundness (F p) main Assumptions Spec` / `FormalAssertion.Soundness …` — an opaque bundled statement.
- **Idiom**:
```lean
circuit_proof_start [main, Spec, Num2Bits.circuit, Num2Bits.Spec, Num2Bits.Assumptions]
```
  bare form (nothing to unfold): `circuit_proof_start`  (`CheckLenFlags.lean:59`, `SelectDigest.lean:59`).
- **After**: introduces the canonical named context `i₀` (offset), `env`, `input_var` / `input_var_<field>` (per `ProvableStruct` field), `input` / `input_<field>`, `h_input : Vector.map (Expression.eval env) input_var = input` (or a tuple of per-field equations), `h_assumptions`, `h_holds` (constraint conjunction, `circuit_norm`-reduced), goal = `Spec` body.
- **Rule of thumb visible in corpus**: put in the list (a) the raw `main`/inner circuit name, (b) each *subcircuit*'s `.circuit`, `.Spec`, `.Assumptions`. E.g. `SHA256Round.lean:83`:
```lean
circuit_proof_start [sha256Round, UpperSigma1.circuit, UpperSigma0.circuit,
  Ch32.circuit, Maj32.circuit, Add32.circuit]
```

### S2. "Index through `h_input`" bridge (var-elem ↦ value-elem)
- **Where**: `AssertBytes/Main.lean:34`; `BitsBool.lean:36-37`; `And32.lean:58-65`; `Xor32.lean:81-88`; `Ch32.lean:64-69`; `Maj32.lean:76-87`; `CheckLenFlags.lean:63-67`.
- **Goal before**: goal/hypothesis mentions `Expression.eval env input_var[i]` but the spec mentions `input[i]`.
- **Idiom** (three equivalent spellings, all present):
```lean
rw [← h_input, Vector.getElem_map]                             -- AssertBytes/Main.lean:34
have hval : input[i.val] = Expression.eval env input_var[i.val] := by
  rw [← h_input, Vector.getElem_map]                           -- BitsBool.lean:36
have h_ai : ∀ i : Fin 32, Expression.eval env input_var_a[i.val] = input_a[i] := by
  intro i
  have := Vector.ext_iff.mp h_input_a i i.isLt
  simp [Vector.getElem_map] at this; exact this                -- And32.lean:58
```
- **After**: goal purely in value-level `input[i]`; discharge with `exact h_holds i`.

### S3. "Constraint ⇒ equation" normalizer (`add_neg_eq_zero` / `sub_eq_zero` / `ring_nf`)
- **Where**: `Num2Bits.lean:64,67`; `And32.lean:69`; `Xor32.lean:94-96`; `Ch32.lean:73-75`; `Maj32.lean:94,100`; `CheckPaddedByte.lean:65-68`; `CheckLenFlags.lean:75,99`; `SelectDigest.lean:78-82`.
- **Goal before**: `h_holds` in *circuit-normal* form `e₁ + -e₂ + … = 0` (Clean flattens `-`/subtraction to `+ -`).
- **Idiom** (three tiers of aggressiveness):
```lean
-- tier 1: pure rewrite
rw [add_neg_eq_zero] at this                          -- CheckPaddedByte.lean:67
exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact this)   -- And32.lean:69
exact add_neg_eq_zero.mp h1                           -- Num2Bits.lean:64
-- tier 2: ring-normalize both sides then match syntactically
have key : lhs - rhs = 0 := by ring_nf; ring_nf at h; exact h
exact sub_eq_zero.mp key                              -- Xor32.lean:94-96, Ch32.lean:73-75
exact eq_of_sub_eq_zero (by ring_nf; ring_nf at this; exact this)  -- Maj32.lean:100
-- tier 3: explicit `have h_ring : … = … := by ring; rw [h_ring]; exact h_lin`  -- Add32.lean:123-134
```
- **After**: a clean field equation `env.get (i₀ + i) = <affine/quadratic expression in inputs>`.

### S4. Witness-vector read-back (`Vector.mapRange` ↦ `env.get (i₀ + i)`)
- **Where**: `Num2Bits.lean:50-56`; `And32.lean:70-74`; `Xor32.lean:97-101`; `Ch32.lean:76-80`; `Maj32.lean:101-105`; `Add32Theorems.lean:62-66` (factored as `z_var_eval`).
- **Goal before**: the spec applies to `Vector.map (Expression.eval env) (Vector.mapRange n (fun i => var ⟨i₀ + i⟩))`.
- **Idiom**:
```lean
set bit_vars : Vector (Expression (F circomPrime)) n :=
  Vector.mapRange n (fun i => var ⟨i₀ + i⟩) with hbv
have hval : ∀ (i : ℕ) (hi : i < n), (bit_vars.map env)[i] = env.get (i₀ + i) := by
  intro i hi
  simp only [hbv, Vector.getElem_map, Vector.getElem_mapRange]
  rfl                                                  -- Num2Bits.lean:51-56
-- or the reusable named lemma:
lemma z_var_eval (env) (i₀) :
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i => var {index := i₀ + i})
    = Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := by
  ext i; simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]  -- Add32Theorems.lean:62
```
  Consumed as `rw [z_var_eval env i₀]` (`Add32.lean:82`) or `rw [h_z]` (`And32.lean:74`).
- **After**: goal about a concrete `Vector.ofFn (fun i => env.get (i₀ + i))`; then a `simp [Vector.getElem_ofFn]` `show`-rewrite pushes indexing through:
```lean
simp_rw [show ∀ i : Fin 32, (Vector.ofFn fun j : Fin 32 => env.get (i₀ + j.val))[i] =
    env.get (i₀ + i.val) from fun i => by simp [Vector.getElem_ofFn]]  -- And32.lean:79
```

### S5. Subcircuit-spec consumption ("un-curry `h_holds` and chain")
- **Where**: `LowerSigma0.lean:46-54`; `UpperSigma0/1`, `LowerSigma1` (identical); `ScheduleStep.lean:62-71`; `SHA256Round.lean:93-117`; `CompressBlock.lean:52-63`; `CheckPad.lean:62-88`; `SHA256/Main.lean:40,53,73-116`.
- **Goal before**: after `circuit_proof_start [.., Sub.circuit]`, `h_holds` is a nested conjunction of `Sub.Assumptions … → Sub.Spec …` implications, with `Assumptions`/`Spec` still folded.
- **Idiom** (canonical 3-step):
```lean
-- (1) unfold the sub-Assumptions/Spec and flatten `∧ →` into curried args
simp only [Xor32.Assumptions, Xor32.Spec, and_imp] at h_holds
-- (2) destructure one hypothesis per subcircuit invocation, in source order
obtain ⟨c1, c2⟩ := h_holds
-- (3) discharge the antecedents from parent assumptions / earlier outputs, chain
obtain ⟨v1, n1⟩ := c1 nr7 nr18
obtain ⟨v2, n2⟩ := c2 n1 ns3          -- n1 = normalization from the previous call
refine ⟨?_, n2⟩
rw [v2, v1, valueBits_eval_rotr32 …, valueBits_eval_shr32 …]
rfl
```
  Larger arity (`SHA256Round.lean:97`, 11 subcircuits):
```lean
obtain ⟨c_sig1, c_ch, c_t10, c_t11, c_t12, c_t1, c_sig0, c_maj, c_t2, c_newa, c_newe⟩ := h_holds
have s_sig1 := c_sig1 h_e;      clear c_sig1
have s_ch   := c_ch h_e h_f h_g; clear c_ch
have s_t10  := c_t10 h_h s_sig1.2; clear c_t10
…
```
  Note the `clear` after each `have` — an explicit context-size control idiom in the big-arity case.
- **After**: `v*` = value equations, `n*` = `Normalized` facts; final `rw [s_wj.1, s_sum1.1, s_sum0.1, s_sig0.1, s_sig1.1]` collapses the chain into the spec literal.

### S6. `simp only [Sub.Assumptions, Sub.Spec, …, h_eval, and_imp] at h_holds` with an eval-bridge in the simp set
- **Where**: `SHA256Round.lean:93-96`.
- **Goal before**: `h_holds` mentions `Vector.map (Expression.eval env) input_var_state[i]` but the chained facts are about `input_state[i]`.
- **Idiom**: prove the bridge first, then *include it in the simp set*:
```lean
have h_eval (i : ℕ) (hi : i < 8) :
    Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
  have h := getElem_eval_vector env input_var_state i hi
  rw [h_input_state] at h
  rw [← CircuitType.eval_var_fields env (input_var_state[i]'hi)]
  exact h
simp only [UpperSigma1.Assumptions, …, Add32.Spec, h_eval, and_imp] at h_holds
```
- **After**: `h_holds` stated entirely in value-level `input_state[i]`, so the chain in S5 applies without per-step rewriting.

### S7. Spec-shape reassociation via `show … ; unfold …; omega`
- **Where**: `ScheduleStep.lean:71-74`.
- **Goal before**: the circuit produces a left-associated `add32` chain; the `Spec` states the *balanced* shape `add32 (add32 σ₁ w₇) (add32 σ₀ w₁₆)`.
- **Idiom**:
```lean
rw [s_wj.1, s_sum1.1, s_sum0.1, s_sig0.1, s_sig1.1]
show _ = _root_.add32 (_root_.add32 _ _) (_root_.add32 _ _)
unfold _root_.add32
omega
```
- **After**: closed — `add32 a b = (a+b) % 2^32`, and `omega` handles mod-2^32 reassociation on ℕ.
- **Cousin** (`SHA256Round.lean:131`): rewrite `%` to the named op to match the spec literal:
```lean
simp only [show ∀ a b : ℕ, (a + b) % 2 ^ 32 = _root_.add32 a b from fun _ _ => rfl] at v_newa v_newe
```

### S8. Field→ℕ lifting under a prime-size bound (`Add32`'s core)
- **Where**: `Add32.lean:90-161`.
- **Goal before**: field linear constraint `Σa + Σb − Σz − 2³²·cout = 0` must yield the ℕ relation `va + vb = vz + 2³²·vcout`.
- **Idiom**:
```lean
have h_p_large := h_large.elim                  -- Fact (p > 2^33)
have h33 : (2:ℕ)^33 = 2^32 + 2^32 := by norm_num
have hp32 : (2:ℕ)^32 < p := by omega
…
have h_pow32_val : (2^32 : F p).val = 2^32 := by
  have hcast : ((2^32 : ℕ) : F p) = (2^32 : F p) := by push_cast; ring
  rw [← hcast, ZMod.val_natCast_of_lt hp32]
have h_lhs_val : (… + …).val = valueBits input_a + valueBits input_b := by
  rw [ZMod.val_add, h_fa, h_fb]; exact Nat.mod_eq_of_lt h_sum_lt_p
have h_rhs_val : (… + (2^32 : F p) * env.get (i₀+32)).val = vz + 2^32 * vcout := by
  rw [ZMod.val_add, ZMod.val_mul, h_fz, h_pow32_val]
  rw [Nat.mod_eq_of_lt h_mul_lt, Nat.mod_eq_of_lt h_total_lt]
have h_nat_eq : … := by
  have := congr_arg ZMod.val h_lin'
  rw [h_lhs_val, h_rhs_val] at this; exact this
rcases IsBool.val_of_IsBool h_cout_isbool with hc0 | hc1
· … exact (Nat.mod_eq_of_lt (h_nat_eq ▸ hvz_lt)).symm
· rw [show vcout = 1 from hc1, Nat.mul_one] at h_nat_eq; omega
```
- **Key lemma names**: `ZMod.val_add`, `ZMod.val_mul`, `ZMod.val_natCast_of_lt`, `ZMod.natCast_val`, `ZMod.cast_id`, `Nat.mod_eq_of_lt`, `IsBool.val_of_IsBool`; closers `linarith`, `omega`.

### S9. `testBit` extensionality for bitwise ops (Nat-level)
- **Where**: `And32Theorems.lean:21-34`; `Xor32.lean:58-72` (`private lemma bool_finsum_xor`); `Ch32Theorems.lean:38-61`; `Maj32Theorems.lean:39-76`; `Theorems.lean:72-86,160-203,229-253`.
- **Goal before**: `(Σ f i · 2ⁱ) &&& (Σ g i · 2ⁱ) = Σ (f i &&& g i)·2ⁱ` (and `^^^`, `Ch`, `Maj` variants).
- **Idiom** (the fixed skeleton — appears 6×):
```lean
apply Nat.eq_of_testBit_eq; intro j
by_cases hj : j < n
· have hfg : ∀ i : Fin n, (f i &&& g i) = 0 ∨ … := by
    intro i; rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
  rw [Nat.testBit_and, testBit_binary_sum n f hf ⟨j, hj⟩, testBit_binary_sum n g hg ⟨j, hj⟩,
      testBit_binary_sum n _ hfg ⟨j, hj⟩]
  rcases hf ⟨j, hj⟩ with hfi | hfi <;> rcases hg ⟨j, hj⟩ with hgi | hgi <;> simp [hfi, hgi]
· push_neg at hj
  have pow_le : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
  have hgS := sum_bool_lt_two_pow n g (fun i => by rcases hg i with h|h <;> simp [h])
  …
  rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ hgS) pow_le),
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hfgS pow_le)]
```
- **Ch-specific extra**: `have h4 : (4294967295 : ℕ) = 2^32 - 1 := by norm_num; rw [h4]` then `Nat.testBit_two_pow_sub_one` + `simp only [hj, decide_true]` (`Ch32Theorems.lean:36,45-46`).
- **After**: closed. The out-of-range branch uses bound lemmas `Nat.and_lt_two_pow`, `Nat.xor_lt_two_pow`, `Nat.and_le_left`.

### S10. "Spec from per-bit constraint" extraction lemma (offload the math)
- **Where**: `Ch32Theorems.lean:64-94` (`spec_of_constraint`); `Maj32Theorems.lean:79-121` (`spec_of_constraint`).
- **Statement shape**:
```lean
lemma spec_of_constraint (input_e input_f input_g z : fields 32 (F p))
    (he hf hg : Normalized …)
    (h_eq : ∀ i : Fin 32, z[i] = input_g[i] + input_e[i] * (input_f[i] - input_g[i])) :
    valueBits z = Specs.SHA256.Ch (valueBits input_e) (valueBits input_f) (valueBits input_g) ∧
    Normalized z
```
- **Circuit-side usage** (`Ch32.lean:83`, `Maj32.lean:109`): the entire soundness closes with `exact spec_of_constraint input_e input_f input_g z he hf hg h_eq'`.
- **Internal idiom**: `Ch_def : ∀ a b c : ℕ, Specs.SHA256.Ch a b c = (a &&& b) ^^^ ((a ^^^ 4294967295) &&& c) := fun _ _ _ => rfl` and `have h1 : valueBits z = ∑ i : Fin 32, (z[i]).val * 2^i.val := rfl` — i.e. **`rfl`-unfold the spec and `valueBits` rather than `simp [Spec]`**.

### S11. Inductive-invariant soundness for `foldlRange` loops
- **Where**: `MessageSchedule.lean:70-195` (48 steps); `SHA256Rounds.lean:70-130` (64 rounds).
- **Goal before**: `h_holds : ∀ i : Fin 48, <per-step subcircuit implication at foldlAcc i>`; goal is the spec of the *final* accumulator.
- **Idiom**:
```lean
rw [sha256Compress_eq_valStateAfterRound]           -- spec ↦ own recursive description
have h_inv : ∀ (k : ℕ) (_ : k ≤ 64),
    Vector.map valueBits (eval env (stateVar i₀ input_var_state k)) =
      valStateAfterRound … k ∧
    (∀ (j : ℕ) (hj : j < 8), Normalized (eval env ((stateVar i₀ input_var_state k)[j]'hj))) := by
  intro k hk
  induction k with
  | zero => …  -- unfold `stateVar`/`valStateAfterRound` at 0, use h_input_state
  | succ k ih =>
    have hk'' : k < 64 := by omega
    obtain ⟨ih_val, ih_norm⟩ := ih (by omega)
    specialize h_holds ⟨k, hk''⟩
    rw [foldlAcc_eq_stateVar i₀ input_var_state input_var_schedule k hk''] at h_holds
    simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
      SHA256Round.Spec, SHA256Round.Assumptions] at h_holds
    have h_spec := h_holds ⟨by intro i; have h := ih_norm i.val i.isLt
                              rw [getElem_eval_vector] at h; exact h, h2, h3⟩
    obtain ⟨h_value, h_norm⟩ := h_spec
    rw [stateVar, valStateAfterRound, dif_pos hk'']
    …
obtain ⟨h_val_64, h_norm_64⟩ := h_inv 64 (le_refl 64)
```
- **Two mandatory support lemmas per loop** (defined in the `*Theorems` file):
  - `foldlAcc_eq_stateVar` / `foldlAcc_eq_varSchedule`: `Circuit.FoldlM.foldlAcc i₀ (Vector.finRange n) body init ⟨k,h⟩ = stateVar i₀ … k`. Comment at `SHA256RoundsTheorems.lean:63-65` explains the subtlety: *"Uses `SHA256State (Expression (F p))` for the accumulator type (not the `Var SHA256State (F p)` alias) so the lemma's pattern matches `h_holds` syntactically — `rw` can't see through the alias."*
  - `sha256Compress_eq_valStateAfterRound` / `messageSchedule_eq_valSchedule`: spec-`Fin.foldl` = own recursive value description, proved by a generalized `suffices h : ∀ k (hk : k ≤ N), Fin.foldl k … = valX k` + `Fin.foldl_succ_last` + `rw [show <castSucc body> = <val body> from rfl, ih]`.
- **After**: `∀ i, valueBits sched[i] = expected[i] ∧ Normalized sched[i]`; final bridging uses `getElem_eval_vector` (`MessageSchedule.lean:187-195`).

### S12. `fin_cases` for 8-slot / 5-slot state postconditions
- **Where**: `SHA256Round.lean:140-157`; `SHA256/Main.lean:111-116, 124-129`; `SelectDigestTheorems.lean:29-33`.
- **Goal before**: `∀ i : Fin 8, Normalized out[i]` where `out` is a `#v[…]` literal with heterogeneous slots.
- **Idiom**:
```lean
intro i
fin_cases i
· convert s_newa.2 using 1
  rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1
· convert (h_eval 0 (by omega)).symm ▸ h_a using 1
  rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1
…                                     -- 8 identical bullets
```
- **`omega`-driven variant** (avoids `fin_cases` on a `ℕ` index): `rcases (by omega : j = 0 ∨ j = 1 ∨ … ∨ j = 7) with rfl|rfl|…|rfl` (`SHA256RoundsTheorems.lean:124-126`, `Cost.lean:734-735, 834-835`, `MainTheorems.lean:74`).

### S13. Vector-literal spec matching by pushing `map`/`eval` inside
- **Where**: `SHA256Round.lean:134-138`.
- **Goal before**: `(#v[new_a, a, b, c, new_e, e, f, g]).map valueBits ∘ eval env = Specs.SHA256.sha256Round …`
- **Idiom**:
```lean
simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, circuit_norm]
simp only [Specs.SHA256.sha256Round, Vector.getElem_map]
rw [v_newa, v_newe, e 0 (by omega), e 1 (by omega), e 2 (by omega),
  e 4 (by omega), e 5 (by omega), e 6 (by omega)]
```
- **After**: both sides are explicit 8-element vectors with matching slot shapes → closed by the `rw` chain.

### S14. One-hot selector collapse (soundness of `SelectDigest` / `CheckPaddedByte`)
- **Where**: `SelectDigest.lean:70-82`; `CheckPaddedByteTheorems.lean:52-99` (`eval_expectedPaddedByte`); `PaddingTheorems.lean:208-230` (`oneHot_mul_sum`).
- **Goal before**: a constraint row `lenFlags[len] * (digest[w] − selectedWord …) = 0` for **all** `len`, plus `OneHotAt lenFlags ℓ`.
- **Idiom** (soundness direction: instantiate at the selected index, kill the multiplier):
```lean
let selectedLen : Fin inputBufferLen := ⟨input_messageLen.val, h_len⟩
have hflag_eval : Expression.eval env input_var_lenFlags[selectedLen.val] = input_lenFlags[selectedLen] := by
  simp [← h_flags, Vector.getElem_map]
have hflag_one : input_lenFlags[selectedLen] = 1 := by
  have := h_onehot selectedLen; simpa [selectedLen] using this
have hrow := h_holds w selectedLen
rw [hflag_eval, hflag_one, one_mul] at hrow
rw [← sub_eq_add_neg] at hrow
have hdigest := sub_eq_zero.mp hrow
```
- **Completeness direction** (sum collapse): `rw [hdigest, oneHot_mul_sum h_onehot h_len g, ← hlen_eq]; ring` (`SelectDigest.lean:163-164`).
- **`oneHot_mul_sum` proof idiom** (`PaddingTheorems.lean:213-230`): `Finset.sum_congr rfl` rewriting each `flags[i]` to `if i.val = ℓ then 1 else 0`, then `Finset.sum_ite_eq'`.

### S15. `natCast` injectivity under a small bound (byte-level equalities)
- **Where**: `CheckPaddedByteTheorems.lean:102-110` (`natCast_inj_lt_256`); used at `CheckPaddedByte.lean:86,96`.
- **Idiom**:
```lean
lemma natCast_inj_lt_256 {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (h : ((a:ℕ) : F p) = ((b:ℕ) : F p)) : a = b := by
  have hp : (256 : ℕ) < p := by have h2 : (256:ℕ) < 2^33 := by norm_num
                                have := h_large.out; omega
  have hva : ((a:ℕ) : F p).val = a := ZMod.val_natCast_of_lt (by omega)
  have hvb : ((b:ℕ) : F p).val = b := ZMod.val_natCast_of_lt (by omega)
  rw [← hva, ← hvb, h]
```
- **Consumed as**: `have hnat := natCast_inj_lt_256 hlt_word hlt_msg h_eq; rw [hnat]; unfold specPaddedByte; rw [dif_pos ⟨h, hj2⟩, Vector.getElem_map]; rfl`.

### S16. `dif_pos`/`dif_neg` case-split matching a `dite`-shaped spec
- **Where**: `CheckPaddedByte.lean:73-99` and `:115-131`; `CheckPaddedByteTheorems.lean:93-99,119-122`; `SHA256/Main.lean:118`.
- **Idiom**:
```lean
by_cases h : j.val < ℓ
· rw [dif_pos h] at h_eq
  … unfold specPaddedByte; rw [dif_pos ⟨h, hj2⟩, Vector.getElem_map]; rfl
· rw [dif_neg h] at h_eq
  … unfold specPaddedByte; rw [dif_neg (by intro hc; exact h hc.1)]
```
  and top-level: `rw [Specs.SHA256.Spec, dif_pos (le_of_lt h_len_assum)]` (`Main.lean:118`).

### S17. Top-level chaining of five block-compressions (`SHA256/Main.lean`)
- **Where**: `SHA256/Main.lean:73-129`.
- **Idiom** — each block obtains its spec by supplying an *inline anonymous-constructor* pair of `Normalized` proofs, then immediately rewrites the value equation with the previous block's:
```lean
obtain ⟨st1_val, st1_norm⟩ := h_c1
  ⟨(by intro i; exact state0_normalized env i.val i.isLt),
   (by intro i
       have h := paddedBlock_normalized env pvar h_bool' 0 i.val i.isLt
       rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 0) i.val i.isLt])⟩
rw [state0_value env, block_val 0] at st1_val
obtain ⟨st2_val, st2_norm⟩ := h_c2 ⟨st1_norm, (by …)⟩
rw [st1_val, block_val 1] at st2_val
… (×5)
have h_sd_spec := h_sd ⟨h_len_lt, h_onehot, by intro k i; fin_cases k
                                              · exact st1_norm i  … ⟩
rw [Specs.SHA256.Spec, dif_pos (le_of_lt h_len_assum)]
apply Vector.ext; intro w hw
simp only [fieldElemsToNat, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
rw [h_sd_spec ⟨w, hw⟩]
refine digest_final _ msg ℓ (le_of_lt h_len_assum) (fun k => ?_) ⟨w, hw⟩ hw
fin_cases k <;> exact st{1..5}_val
```
- **`set` abbreviations at the top** (`Main.lean:44-47`): `set msg := Vector.map ZMod.val input_message with hmsg`, `set ℓ := ZMod.val input_messageLen with hℓ`, `set pvar : Var SHA256PaddedBits _ := Vector.mapRange paddedBitsLen fun i => var { index := i₀ + i } with hpvar`.

### S18. `simp_all only [...]` as a "collapse everything already proved" closer
- **Where**: `CompressBlock.lean:111`.
- **Idiom**: `simp_all only [implies_true, and_self, forall_const, and_true]` — used once, after all bridging `have`s, to discharge the `Normalized`-conjunct half of the goal, leaving only the value equality.

---

# 2. COMPLETENESS PATTERNS

### C1. `circuit_proof_start` + `h_env` (dual of S1)
- **Where**: every completeness proof.
- **Context produced**: `env : ProverEnvironment (F p)` (so every eval is `env.toEnvironment`), `h_env` = the *witness-generator equations* (`env.get (i₀+i) = <compute env>`, one per `witnessVector`/`witnessField`) **or** the subcircuit `Assumptions → Spec` implications, `h_spec` (for `FormalAssertion.Completeness`, the target `Spec` is a *hypothesis*), `h_assumptions` (`ProverAssumptions`). Goal = the constraint conjunction.

### C2. "Witness value ⇒ constraint holds" (`rw [h_env i]; ring`)
- **Where**: `And32.lean:91-94`; `Ch32.lean:96-99`; `Maj32.lean:113-119`; `Xor32.lean:125-133`; `Num2Bits.lean:78-82`; `Add32.lean:177-186`.
- **Goal before**: constraint row in `+ -` normal form with `env.get (i₀ + i)` occurrences.
- **Idiom** (minimal form):
```lean
intro i
have := h_env i
simp only [Vector.getElem_ofFn] at this
rw [this]; ring
```
  multi-witness variant (`Maj32.lean:113`):
```lean
refine ⟨fun i => ?_, fun i => ?_⟩
· have := (h_env.1) i;   simp only [Vector.getElem_ofFn] at this; rw [this]; ring
· have := (h_env.2.1) i; simp only [Vector.getElem_ofFn] at this; rw [this]; ring
```
  with a cast step in between (`Xor32.lean:128-133`):
```lean
have hcast : ((input_a[i].val ^^^ input_b[i].val : ℕ) : F p) =
    input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i] := by
  rw [← IsBool.xor_eq_val_xor (ha i) (hb i)]
  have := ZMod.natCast_val (R := ZMod p) (…); rw [this]; exact ZMod.cast_id p _
rw [henv, hcast, h_ai i, h_bi i]; ring
```
  boolean-branch variant (`Add32.lean:181-186`): `rcases Nat.mod_two_eq_zero_or_one (…) with h | h <;> rw [h] <;> push_cast <;> ring`.

### C3. `rcases <bit alternative> <;> rw [h] ; ring` for booleanity rows
- **Where**: `Num2Bits.lean:78-82`.
```lean
intro i
rw [h_env i]
rcases @fieldToBits_bits circomPrime _ n input i.val i.isLt with h0 | h1
· rw [h0]; ring
· rw [h1]; ring
```

### C4. "Assumption transport" (mirror of S2, `rwa` instead of `rw`)
- **Where**: `AssertBytes/Main.lean:42-43`.
```lean
intro i
have := h_assumptions i
rwa [← h_input, Vector.getElem_map] at this
```

### C5. Subcircuit-assumption assembly (`refine ⟨…⟩` in source order)
- **Where**: `LowerSigma0.lean:60-67`; `ScheduleStep.lean:76-86`; `SHA256Round.lean:195-206`; `CompressBlock.lean:121-142`; `CheckPad.lean:90-114`; `SHA256/Main.lean:229-265`.
- **Goal before**: a nested conjunction, one conjunct per subcircuit = its `Assumptions` at the *evaluated* inputs.
- **Idiom** — the pattern is *bidirectional*: first `simp only [Sub.Assumptions, Sub.Spec, and_imp] at h_env ⊢` (**note the `⊢`**, unfolding the goal too), consume `h_env` for the `Normalized` outputs, then `refine`/`exact` the tuple:
```lean
simp only [Xor32.Assumptions, Xor32.Spec, and_imp] at h_env ⊢
have nr7 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 7
…
obtain ⟨_, n1⟩ := h_env.1 nr7 nr18
exact ⟨⟨nr7, nr18⟩, n1, ns3⟩                    -- LowerSigma0.lean:62-67
```
  With per-slot rewriting (`SHA256Round.lean:195-206`):
```lean
refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· rw [h_eval 4 (by omega)]; exact h_e
· rw [h_eval 4 (by omega), h_eval 5 (by omega), h_eval 6 (by omega)]; exact ⟨h_e, h_f, h_g⟩
…
· exact ⟨n_t1, by simp_all⟩
```

### C6. `Finset.sum_eq_single` for one-hot completeness sums
- **Where**: `CheckLenFlags.lean:126-154`.
```lean
rw [eval_foldl_sum]
have : (∑ i : Fin inputBufferLen, Expression.eval env.toEnvironment input_var_lenFlags[i.val]) = 1 := by
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h_flag_val i)]
  rw [Finset.sum_eq_single (⟨input_messageLen.val, h_msg_lt⟩ : Fin inputBufferLen)]
  · simp
  · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]
  · intro h; exact absurd (Finset.mem_univ _) h
rw [this]; ring
```
- Also with the weight: `rw [if_neg (fun h => hb (Fin.ext h))]; ring` then `rw [hsum, ZMod.natCast_val, ZMod.cast_id]; ring`.

### C7. Inductive-invariant completeness for loops (normalization-only invariant)
- **Where**: `MessageSchedule.lean:199-266`; `SHA256Rounds.lean:132-188`.
- **Note**: the completeness invariant drops the value half of S11's invariant, keeping only `∀ j hj, Normalized (eval env.toEnvironment ((varSchedule i₀ input_var k)[j]'hj))`; the `succ` case uses `h_env ⟨k, hk''⟩` (instead of `h_holds`) but is otherwise textually identical.
- **Closing**: `intro i; … rw [foldlAcc_eq_varSchedule i₀ input_var i.val hk]; simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions, circuit_norm]; refine ⟨?_,?_,?_,?_⟩` then four `have h := ih (i.val + 16 - k) (by omega); rw [CircuitType.eval_var_fields] at h; exact h`.

### C8. Prover-witness value computation (`Main`'s completeness)
- **Where**: `SHA256/Main.lean:144-196`.
- **Idiom**: prove `witnessVector`'s generator applied to *this* env equals the pure value function, then transport:
```lean
have hbwit : paddedBitsWitness { message := input_var_message, messageLen := input_var_messageLen } env
    = paddedBitsValue msg ℓ := by
  simp only [paddedBitsWitness]; rw [hb, h_msgLen_eq]
have h_pad_val : Vector.map (Expression.eval env.toEnvironment) pvar = paddedBitsValue msg ℓ := by
  rw [← hbwit]; apply Vector.ext; intro i hi
  rw [hpvar, Vector.getElem_map, Vector.getElem_mapRange]
  rw [show Expression.eval env.toEnvironment (var { index := i₀ + i }) = env.get (i₀ + i) from rfl]
  exact h_pad_env ⟨i, hi⟩
have h_bool'    := fun i => by rw [h_pad_val]; exact paddedBitsValue_isBool msg ℓ i
have h_byte_eq' := fun j => by rw [h_pad_val]; exact paddedByteVal_paddedBitsValue msg h_msg256 ℓ j
```

### C9. `omit h_large in` on completeness when the size hypothesis is unused
- **Where**: `SelectDigest.lean:132`; `CheckPaddedByte.lean:101`; `CheckLenFlags.lean:103`.
- **Idiom**: `omit h_large in theorem completeness : …` — explicitly drops the `[Fact (p > 2^33)]` instance so the proof term does not depend on it. Same device used pervasively for helper lemmas (`omit [Fact (Nat.Prime p)] h_large in`, `Add32Theorems.lean:22`).

---

# 3. `mainCost` PATTERNS

### M1. Terms, not tactics: `circuitCost` as a `fun input => CostIs …` term
- **Where**: `AssertBytes/Main.lean:121-125`; `SHA256/Main.lean:653-666`.
```lean
theorem mainCost : circuitCost main ⟨allocations, constraints⟩ :=
  fun input =>
    show CostIs (main input) ⟨allocations, constraints⟩ from
      CostIs.forEach (fun a n => costIs_assertion_num2Bits 8 a n)
```
```lean
theorem mainCost : circuitCost main ⟨allocations, constraints⟩ :=
  fun input =>
  (CostIs.bind (CostIs.witnessVector paddedBitsLen _) fun _ =>
   CostIs.bind (CostIs.witnessVector inputBufferLen _) fun _ =>
   CostIs.bind (Cost.costIs_sub_checkPad _) fun _ =>
   CostIs.bind (Cost.costIs_sub_compressBlock _) fun _ =>   -- ×5
   …
   CostIs.bind (Cost.costIs_sub_selectDigest _) fun _ =>
   CostIs.pure _
     : CostIs (main input) ⟨allocations, constraints⟩)
```
- **Why it closes**: `CostIs c K := ∀ n, circuitCount c n = K`; the `Count` arithmetic (`Count.add`) is definitional, so the ascription `: CostIs (main input) ⟨204224, 209586⟩` type-checks by `rfl` on `Nat` addition. **No `decide`, no `native_decide`, no `norm_num`.**

### M2. `CostIs` combinator vocabulary (mirrors circuit combinators 1:1)
`CostR1CS.lean:311-399`:
| Circuit form | Cost lemma | Count |
|---|---|---|
| `pure a` | `CostIs.pure` | `Count.zero` |
| `do a; b` | `CostIs.bind hf (fun _ => hg)` | `K₁ + K₂` |
| `witnessVector m c` | `CostIs.witnessVector m _` | `⟨m, 0⟩` |
| `witnessField c` | `CostIs.witnessField _` | `⟨1, 0⟩` |
| `witnessVar c` | `CostIs.witnessVar _` | `⟨1, 0⟩` |
| `assertZero e` | `CostIs.assertZero _` | `⟨0, 1⟩` |
| `subcircuit C b` | `CostIs.subcircuit (costIs_inner …)` | inner |
| `assertion C b` | `CostIs.assertion (costIs_inner …)` | inner |
| `Circuit.forEach xs body` | `CostIs.forEach (fun a n => …)` | `⟨m*K.a, m*K.c⟩` |
| `Circuit.mapFinRange m body` | `CostIs.mapFinRange (fun _ _ => …)` | `m • K` |
| `Circuit.foldlRange m init body` | `CostIs.foldlRange (fun _ _ n => … n)` | `m • K` |
`circuitCount_eq_of_CostIs` converts to the `= K` form; `CostIs c K 0` instantiates at offset 0.

### M3. Arithmetic-massage before the term (when `Count` addition doesn't reduce)
- **Where**: `AssertBytes/Cost.lean:44-52`.
```lean
theorem costIs_num2Bits (n : ℕ) (x : Expression (F circomPrime)) :
    CostIs (Num2Bits.main n x) ⟨n, n + 1⟩ := by
  unfold Num2Bits.main
  have hcount : (⟨n, 0⟩ + (⟨n * 0, n * 1⟩ + ⟨0, 1⟩) : Count) = ⟨n, n + 1⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1; simp
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) n _) fun bits => ?_
  refine CostIs.bind (CostIs.forEach fun b m => CostIs.assertZero (b * (b - 1)) m) fun _ => ?_
  exact CostIs.assertZero _
```
- Simpler `Nat.mul_zero`/`Nat.mul_one` variant (`SHA256/Cost.lean:1069-1074`):
```lean
theorem costIs_bitsBool (n : ℕ) [NeZero n] (input) : CostIs (BitsBool.main n input) ⟨0, n⟩ := by
  have h : CostIs (BitsBool.main n input) ⟨n * 0, n * 1⟩ := CostIs.forEach fun _ => CostIs.assertZero _
  rw [Nat.mul_zero, Nat.mul_one] at h
  exact h
```

### M4. Named `Count` constants + derived-composition arithmetic (SHA256)
- **Where**: `SHA256/Cost.lean:70-96`.
```lean
def and32Cost : Count := ⟨32, 32⟩
def xor32Cost : Count := ⟨32, 32⟩
def add32Cost : Count := ⟨33, 34⟩
def ch32Cost  : Count := ⟨32, 32⟩
def maj32Cost : Count := ⟨64, 64⟩
def sigmaCost : Count := ⟨64, 64⟩
def scheduleStepCost : Count := ⟨227, 230⟩
def messageScheduleCost : Count :=
  ⟨48 * (sigmaCost.allocations + sigmaCost.allocations + 3 * add32Cost.allocations),
   48 * (sigmaCost.constraints + sigmaCost.constraints + 3 * add32Cost.constraints)⟩
def sha256RoundCost : Count :=
  ⟨2*sigmaCost.allocations + ch32Cost.allocations + maj32Cost.allocations + 7*add32Cost.allocations, …⟩
def sha256RoundsCost  : Count := ⟨64 * sha256RoundCost.allocations, 64 * sha256RoundCost.constraints⟩
def compressBlockCost : Count :=
  ⟨messageScheduleCost.allocations + sha256RoundsCost.allocations + 8*add32Cost.allocations, …⟩
def selectDigestCost : Count := ⟨8, 8 * inputBufferLen⟩
```
Costs are written **symbolically in terms of sub-costs**, never as literals — so the composite `CostIs` terms elaborate by `rfl` on the arithmetic.

### M5. `costIs_sub_*` wrapper-per-gadget (heartbeat control)
- **Where**: `SHA256/Cost.lean:135-232`, docstring at :155-157.
> *"Per-gadget subcircuit-cost wrappers. Each isolates the (single) `circuit.main` unfolding into its own elaboration, so composite chains never accumulate the defeq work of many subcircuit invocations into one heartbeat budget."*
```lean
theorem costIs_sub_add32 (b : Var Add32.Inputs (F circomPrime)) :
    CostIs (subcircuit Add32.circuit b) add32Cost := CostIs.subcircuit (costIs_add32 _ _)
```
Present for: `xor32, add32, ch32, maj32, upperSigma0/1, lowerSigma0/1, scheduleStep, sha256Round, messageSchedule, sha256Rounds, checkLenFlags, bitsBool, checkPad, compressBlock, selectDigest`, plus `AssertBytes`' `costIs_assertion_num2Bits`.

### M6. `*Cost_proof` instantiation at offset 0 on `varFromOffset`
- **Where**: `SHA256/Cost.lean:240-307`.
```lean
theorem add32Cost_proof :
    circuitCount (Add32.main (varFromOffset Add32.Inputs 0 : Var Add32.Inputs (F circomPrime))) = add32Cost :=
  costIs_add32 _ _ 0
```
One per gadget (`and32, xor32, add32, ch32, maj32, lowerSigma0/1, upperSigma0/1, messageSchedule, sha256Round, sha256Rounds, compressBlock`).

### M7. `set_option maxRecDepth 8000` for deep `do`-blocks
- **Where**: `SHA256/Main.lean:637` (comment at :635-636: *"`maxRecDepth` controls elaboration stack depth only (not the trusted base and not the heartbeat budget)"*), and `CheckPad.lean:125` (`set_option maxRecDepth 8000 in` on `computableWitnesses`).

---

# 4. `isR1CS` PATTERNS

### R1. `isR1CS_of_IsR1CSCirc` two-component shape
- **Where**: `AssertBytes/Main.lean:127-132`; `SHA256/Main.lean:673-727`; every gadget-level `*_isR1CS` in `SHA256/Cost.lean`.
```lean
theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput => <IsR1CSCirc (main input)>)          -- constraint rows
    (fun _ _ => affineOutput_unit _)                          -- output affineness
```
For AssertBytes the output is `unit`, so `affineOutput_unit` closes it; for SHA256 the second component (`Main.lean:720-727`) is:
```lean
(fun input hinput n => by
  intro i hi
  have hi8 : i < 8 := by have hsz : size Output = 8 := rfl; omega
  change Affine (((main input).output n).digest[i])
  simp only [main, Circuit.bind_output_eq, Circuit.pure_output_eq]
  exact Cost.affineW_subOut_selectDigest _ _ i hi8)
```

### R2. `attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS`
- **Where**: `AssertBytes/Main.lean:111`; `AssertBytes/Cost.lean:63`; `SHA256/Cost.lean:323`; `SHA256/Main.lean:642`.
- **Documented reason** (`SHA256/Cost.lean:317-322`): *"Left reducible, the unifier tries to **evaluate** them on the asserted expressions when matching the single-row lemmas / `assertZero` / `forEach` against a goal, which loops on neutral subterms like `a[i]`. We only ever *apply* these certificates (never compute the predicates), so keep them opaque."*
- **This is the single most load-bearing performance idiom in the isR1CS obligation.**

### R3. `IsR1CSCirc` combinator chain (`bind` vs `bind_out`)
`CostR1CS.lean:416-547`. Vocabulary: `IsR1CSCirc.pure/bind/bind_out/map/witnessVector/witnessVar/witnessField/assertZero/subcircuit/assertion/forEach/mapFinRange/foldlRange/foldlRange_inv`.
- `bind_out` is used when the continuation needs the *offset* of the produced output (`fun n => …`); `bind` when it does not.
```lean
theorem r1cs_and32 (a b) (ha : AffineW a) (hb : AffineW b) : IsR1CSCirc (And32.and32 a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_sub_mul (affineW_witnessVector_output 32 _ n j.val j.isLt)
            (ha j.val j.isLt) (hb j.val j.isLt)) m)
      (fun _ => IsR1CSCirc.pure _)                     -- SHA256/Cost.lean:381-389
```

### R4. Row-shape lemma selection table (the "which `isR1CSRow_*`" decision)
`CostR1CS.lean:687-723` + `SHA256/Cost.lean:1000-1011`:
| Asserted expression shape | Lemma |
|---|---|
| affine `L` | `isR1CSRow_of_affine hL` |
| `A * B` | `isR1CSRow_mul hA hB` |
| `C - A*B` | `isR1CSRow_sub_mul hC hA hB` |
| `C + A*B` | `isR1CSRow_add_mul hC hA hB` |
| `L - (C + A*B)` | `isR1CSRow_sub_add_mul` (**defined in the solution**, `SHA256/Cost.lean:1000`) |
- Concrete uses: booleanity `z[i]*(z[i]-1)` → `isR1CSRow_mul` (`Cost.lean:430`, `AssertBytes/Cost.lean:76`); AND `z[i] - a[i]*b[i]` → `isR1CSRow_sub_mul`; XOR `z-a-b+2ab` → `isR1CSRow_add_mul (Affine.sub (Affine.sub …)) (Affine.fconst_mul _ …) …` (`Cost.lean:407-410`); Maj row 2 → `isR1CSRow_sub_mul` with an `Affine.fconst_mul` inside (`Cost.lean:498-503`); linear recomposition → `isR1CSRow_of_affine (Affine.sub … (affine_fieldFromBitsExpr …))`.
- **`isR1CSRow_sub_add_mul` proof idiom** (the only place `r1csProducts` is reasoned about directly):
```lean
rcases r1csProducts_mul_affine hA hB with h | h
· exact isR1CSRow_of_r1csProducts (k := 0)
    (by show r1csProducts (L + -(C + A * B)) = some 0
        rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add,
          r1csProducts_of_affine hL, r1csProducts_of_affine hC, h]) (by omega)
· exact isR1CSRow_of_r1csProducts (k := 1) (…) (by omega)
```

### R5. Affineness propagation lemmas (`Affine`/`AffineW`) — the "degree bookkeeping" layer
- **Atoms** (`CostR1CS.lean:591-612`): `Affine.const, Affine.var, Affine.add, Affine.neg, Affine.sub, Affine.fconst_mul, Affine.mul_fconst, Affine.zero, Affine.mul_deg0` (+ `degree_const`).
- **Vector-level**: `AffineW v := ∀ i (hi : i < m), Affine v[i]`; `AffineW.left_of_append`, `AffineW.right_of_append`, `AffineW.affineProvable`, `AffineProvable.affineW`, `affineW_varFromOffset`, `affineW_witnessVector_output`, `affine_witnessField_output`, `affineW_mapRange_var`, `affineOutput_unit`, `affineOutput_of_affineW`, `ConstW.affineW`.
- **Fold-level**: `affine_finFoldl'` — the key combinator for `Fin.foldl`-shaped expressions:
```lean
theorem affine_fieldFromBitsExpr {m} (v) (h : AffineW v) : Affine (Utils.Bits.fieldFromBitsExpr v) := by
  unfold Utils.Bits.fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))
```
  (`AssertBytes/Cost.lean:55-61` and `SHA256/Cost.lean:341-347`, duplicated verbatim). Same shape for `affine_byteFromWord` (`Cost.lean:1013-1019`, uses `Affine.mul_deg0 … (degree_const _)`) and the three folds inside `r1csRow_checkPaddedByte`.

### R6. "Projecting `AffineProvable` down to fields" (`simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz]`)
- **Where**: `SHA256/Cost.lean:53-56, 394-398, 416-419, 450-453, 473-477, 509-513, 760-765, 771-776, 951-956, 959-964, 1247-1258`; `AssertBytes/Main.lean:116-119`.
- **Idiom** (the fixed recipe):
```lean
let hflat : AffineW (input.a ++ input.b : fields 64 (Expression (F circomPrime))) := by
  intro i hi
  have hsz : size And32.Inputs = 64 := rfl
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by omega)
r1cs_and32 input.a input.b (AffineW.left_of_append hflat) (AffineW.right_of_append hflat)
```
  Three-field variant introduces an intermediate: `let htail := AffineW.right_of_append hflat` then `AffineW.left_of_append htail`, `AffineW.right_of_append htail` (`Cost.lean:478-481`).
  Single-field / scalar variant: `affineW_input_message` / `affine_input_messageLen` (`Cost.lean:1247-1258`), `affineW_input_buffer` (`AssertBytes/Main.lean:116`).

### R7. `ProvableVector`-flatten helpers (`SHA256/Cost.lean:22-68`)
Three reusable bridges for `ProvableVector (fields 32) n`:
- `affineW_varFromOffset_pvec` — `rw [varFromOffset_vector, Vector.getElem_mapRange]; exact affineW_varFromOffset _ _`
- `affineW_of_flatten_pvec` — index arithmetic (`Vector.getElem_flatten`, `hdiv : (j*32+i)/32 = j`, `hmod : (j*32+i)%32 = i`, then `simpa [hdiv, hmod] using h`)
- `affineProvable_pvec_of_affineW` — the converse (`Nat.div_lt_of_lt_mul`, `Nat.mod_lt`)

### R8. Subcircuit-output affineness one-liners
- **Where**: `SHA256/Cost.lean:351-379, 520-523, 599-629, 790-793, 939-943, 1218-1222`.
```lean
theorem affineW_subOut_add32 (b) (n : ℕ) : AffineW ((subcircuit Add32.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, Add32.circuit, Add32.elaborated]; exact Affine.var _
```
  Offset-shifted variant for Maj32 (two witness vectors): `(Maj32.maj32 a b c).output n = varFromOffset (fields 32) (n + 32)` (`Cost.lean:377`).
- **Per-word split for `SHA256Round`** (`Cost.lean:690-743`), with the documented reason:
> *"Each word's `circuit_norm` reduction is a separate declaration so it gets its own heartbeat budget (reducing all eight at once is too expensive)."*
  `affineW_sha256Round_out_w0 … _w7`, assembled by `affineW_sha256Round_output` with `rcases (by omega : j = 0 ∨ … ) with rfl|…`.

### R9. Loop R1CS with an invariant (`IsR1CSCirc.foldlRange_inv`)
- **Where**: `SHA256/Cost.lean:745-754` (rounds), `:800-821` (message schedule).
```lean
theorem r1cs_sha256Rounds (input) (hstate) (hsched) : IsR1CSCirc (SHA256Rounds.main input) := by
  refine IsR1CSCirc.foldlRange_inv (fun s => ∀ j (hj : j < 8), AffineW s[j]) hstate ?_ ?_
  · intro s i hs
    exact IsR1CSCirc.subcircuit (r1cs_sha256Round _ _ _ hs (affineW_constWord32 _) (hsched _ i.isLt))
  · intro s i n hs
    exact affineW_sha256Round_output _ n hs
```
  With an explicit `constant` instance and an init obligation (`Cost.lean:802-821`):
```lean
refine IsR1CSCirc.foldlRange_inv (constant := MessageSchedule.constantLength)
  (fun w => ∀ k (hk : k < 64), AffineW w[k]) ?_ ?_ ?_
· intro k hk
  show AffineW ((block ++ Vector.replicate 48 (Vector.replicate 32 (0 : Expression _)))[k])
  rw [Vector.getElem_append]; split
  · exact hblock _ _
  · rw [Vector.getElem_replicate]; intro j hj; rw [Vector.getElem_replicate]; exact Affine.zero (F := F circomPrime)
· intro w i hw
  exact IsR1CSCirc.bind_out (r1cs_sub_scheduleStep _ (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega))) (fun _ => IsR1CSCirc.pure _)
· intro w i n hw k hk
  simp only [circuit_norm, Vector.getElem_set]; split
  · exact affineW_varFromOffset _ _
  · exact hw _ _
```

### R10. Recursive affineness of the loop accumulator descriptions
- **Where**: `SHA256/Cost.lean:825-843` (`affineW_stateVar`), `:846-868` (`affineW_varSchedule`).
```lean
theorem affineW_stateVar (i₀) (s) (hs : ∀ j (hj : j < 8), AffineW s[j]) :
    ∀ (m j : ℕ) (hj : j < 8), AffineW ((SHA256Rounds.stateVar i₀ s m)[j]) := by
  intro m
  induction m with
  | zero => intro j hj; exact hs j hj
  | succ p ih =>
      intro j hj
      rw [SHA256Rounds.stateVar]
      rcases (by omega : j = 0 ∨ … ∨ j = 7) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact affineW_mapRange_var _        -- fresh witness word
      · exact ih 0 (by omega)               -- pass-through
      …
```
  Then `affineW_subOut_messageSchedule` / `affineW_subOut_sha256Rounds` do `have heq : (subcircuit C b).output n = <描述> := by simp only [circuit_norm, subcircuit, C, C.elaborated]; rw [heq]; exact affineW_<描述> …`.

### R11. Index-aware `forEach` R1CS combinator (bespoke, AssertBytes)
- **Where**: `AssertBytes/Cost.lean:33-40`. Docstring gives the reason: the generic `IsR1CSCirc.forEach` quantifies over **all** element values, which is too weak when the body needs `xs[i]` to be an affine witness cell.
```lean
theorem IsR1CSCirc.forEach_mem {α} {m} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit (F circomPrime) Unit} {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)
```

### R12. Top-level `isR1CS` as a `refine`-chain threading affineness (SHA256)
- **Where**: `SHA256/Main.lean:673-719`.
```lean
refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector paddedBitsLen _) fun npad => ?_
refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector inputBufferLen _) fun nflags => ?_
have hpadded : AffineW ((Circuit.witnessVector paddedBitsLen (paddedBitsWitness input)).output npad) :=
  affineW_witnessVector_output _ _ _
have hflags  : AffineW … := affineW_witnessVector_output _ _ _
refine IsR1CSCirc.bind (Cost.r1cs_sub_checkPad _ (Cost.affine_input_messageLen input hinput)
    (Cost.affineW_input_message input hinput) hflags hpadded) fun _ => ?_
refine IsR1CSCirc.bind_out (Cost.r1cs_sub_compressBlock _ Cost.affineW_state0
    (Cost.affineW_paddedBlock _ hpadded 0)) fun n1 => ?_
refine IsR1CSCirc.bind_out (Cost.r1cs_sub_compressBlock _ (Cost.affineW_subOut_compressBlock _ n1)
    (Cost.affineW_paddedBlock _ hpadded 1)) fun n2 => ?_   -- ×5, threading nᵢ
refine IsR1CSCirc.bind (Cost.r1cs_selectDigest _ hflags ?_) fun _ => ?_
· intro k hk j hj
  rcases (by omega : k = 0 ∨ … ∨ k = 4) with rfl|rfl|rfl|rfl|rfl
  · simp [SelectDigest.statesVec]; exact Cost.affineW_subOut_compressBlock _ n1 j hj
  …
exact IsR1CSCirc.pure _
```

### R13. `local irreducible` on *definitions* to keep unification syntactic
- **Where**: `SHA256/Cost.lean:1146`: `attribute [local irreducible] byteFromWord expectedPaddedByte paddedWord paddedBit paddedBlock`, documented at `:979-988`:
> *"`byteFromWord`/`expectedPaddedByte`/`paddedWord`/`paddedBit`/`paddedBlock` are made `local irreducible` before the composite proofs, so unification against `CheckPad.main` stays syntactic instead of unfolding the 256-deep `Fin.foldl` expressions. The composite proofs supply `circuit`/`b` explicitly for the same reason."*
  Hence `CostIs.assertion (circuit := CheckPaddedByte.circuit j) (b := ⟨…⟩) …` with **named arguments** (`Cost.lean:1153-1155, 1164-1166`).
- **Size-generic-then-instantiate** (`Cost.lean:1121-1142`): `costIs_sub_bitsBool (n : ℕ) [NeZero n]` proved at generic `n`, then applied at `paddedBitsLen` — *"keeps the unifier from materialising the concrete `n`-element operation list."*
- Similar `attribute [local irreducible] main …` appears in `SHA256Round.lean:211`, `MessageSchedule.lean:272`, `SHA256Rounds.lean:195`, `CompressBlock.lean:147`, `CheckPad.lean:123`, `SelectDigest.lean:170`, `SHA256/Main.lean:267` — always immediately *before* `computableWitnesses`.

### R14. The **factored-expression design trick** (circuit written to be R1CS)
- **Where**: `Common.lean:144-172` (`expectedPaddedByte` docstring).
> *"This is written in **factored** form so the asserted constraint is a single R1CS row even when `message` is a vector of input variables. The naive form `∑ lenFlags[len] · (message[j] or const)` multiplies the one-hot selector by the message in every summand, which the syntactic single-row check (`isR1CSRow`) rejects as a rank-2+ product. Here the message contribution is pulled out as one genuine product `message[j] · (∑_{len > j} lenFlags[len])`."*
- Consequence: soundness needs `eval_expectedPaddedByte` (`CheckPaddedByteTheorems.lean:52`) to prove the factored form agrees value-for-value with the naive one.

---

# 5. `computableWitness` PATTERNS

### W1. The universal opener: `change` to `forAllFlat` + `apply forAllFlat_of_structuralComputableWitnesses`
- **Where**: *every* gadget-level `computableWitnesses` (16 occurrences: `Num2Bits.lean:104`, `BitsBool.lean:60`, `And32/Xor32/Ch32/Maj32/Add32`, `LowerSigma0/1`, `UpperSigma0/1`, `ScheduleStep`, `MessageSchedule`, `SHA256Round`, `SHA256Rounds`, `SelectDigest`, `CheckPaddedByte`).
```lean
theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply
    Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main <inner>
  simp only [ …_structuralComputableWitnesses_iff … ]
  and_intros
  …
```
- **Variant for composites** (`CompressBlock.lean:161-269`, `CheckPad.lean:126-180`, `SHA256/Main.lean:284-627`): build `have hstruct : …StructuralComputableWitnesses input env env' offset ((main input).operations offset) := by …` first, then `exact …forAllFlat_of_structuralComputableWitnesses input env env' hstruct` — separating the structural proof from the flattening.

### W2. The `structuralComputableWitnesses_iff` simp set (one lemma per circuit combinator)
- **Where**: `Num2Bits.lean:112-118`, `And32.lean:107-113`, `Add32.lean:278-285`, `SelectDigest.lean:180-186`, `MessageSchedule.lean:282-287`, `SHA256/Main.lean:402-408`, etc.
```lean
simp only [
  Challenge.Utils.ComputableWitnessLemmas.Circuit.bind_structuralComputableWitnesses_iff,
  Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessVector_structuralComputableWitnesses_iff,
  Challenge.Utils.ComputableWitnessLemmas.Circuit.witnessField_structuralComputableWitnesses_iff,
  Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff,
  Challenge.Utils.ComputableWitnessLemmas.Circuit.foldlRange_structuralComputableWitnesses_iff,
  Challenge.Utils.ComputableWitnessLemmas.Circuit.mapFinRange_structuralComputableWitnesses_iff,
  Challenge.Utils.ComputableWitnessLemmas.Circuit.assertZero_structuralComputableWitnesses_iff,
  Challenge.Utils.ComputableWitnessLemmas.Circuit.pure_structuralComputableWitnesses_iff,
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
  Challenge.Utils.ComputableWitnessLemmas.FormalAssertion.assertion_structuralComputableWitnesses_iff,
  and_true, implies_true, forall_const]
```
  (Solutions include exactly the ones their `main` uses.) Then `and_intros` (or `intro i` for a loop) splits into one goal per operation.

### W3. Constraint-only circuits: `intro _; trivial`
- **Where**: `BitsBool.lean:71-72`; `CheckPaddedByte.lean:147-148`; `And32/Xor32/Ch32/Maj32/Add32/SelectDigest` trailing bullets.
```lean
simp only [ …forEach…, …assertZero… ]
intro _
trivial
```
  Assertions carry no witnesses, so the condition is vacuous.
- **Ultra-short variant** (`CheckLenFlags.lean:163-172`) — bypasses the whole framework with a raw `simp`:
```lean
unfold main
simp [Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition,
  Circuit.bind_operations_eq, Operations.forAllFlat,
  Operations.forAll_append, Circuit.forEach.forAll, Circuit.forAll, Circuit.operations,
  Circuit.assertZero, Operations.forAll]
```

### W4. Witness-generator determinism: `simp [circuit_norm] at h_input; Vector.ext; simp [ha, hb]`
- **Where**: `And32.lean:115-128`; `Xor32.lean:154-167`; `Ch32.lean:120-137`; `Maj32.lean:140-153`; `SelectDigest.lean:188-251`.
```lean
· intro _ h_input
  simp [circuit_norm] at h_input
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  have ha : Expression.eval env.toEnvironment input.a[i] =
            Expression.eval env'.toEnvironment input.a[i] := h_input.1 _ (by simp)
  have hb : … := h_input.2 _ (by simp)
  simp [ha, hb]
```
- **Field-scalar variant** (`Num2Bits.lean:120-125`):
```lean
intro _ h_input
have h_eval : Expression.eval env.toEnvironment x = Expression.eval env'.toEnvironment x := by
  rw [CircuitType.eval_var_field_prover, CircuitType.eval_var_field_prover] at h_input
  exact h_input
simpa using congrArg (fieldToBits n) h_eval
```
- **Sum-valued generator** (`Add32.lean:289-301`) — must show the *ℕ* helper agrees:
```lean
have ha : evalBitsNat env input.a = evalBitsNat env' input.a := by
  unfold evalBitsNat
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x : F p => x.val * 2^i.val) (h_input.1 _ (Vector.getElem_mem i.isLt))
simp [ha, hb]
```

### W5. Generator reading *earlier witness cells* (needs `h_agree`)
- **Where**: `Maj32.lean:154-174` (the `z` witness reads `t`).
```lean
· intro h_agree h_input
  simp [circuit_norm] at h_input
  simp [Circuit.witnessVector, circuit_norm] at h_agree ⊢
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  have ht : env.get (offset + i) = env'.get (offset + i) := h_agree (offset + i) (by omega)
  have ha := h_input.1 _ (by simp); have hb := h_input.2.1 _ (by simp); have hc := h_input.2.2 _ (by simp)
  simp [ht, ha, hb, hc]
```

### W6. Subcircuit at a *known-input* offset: `subcircuit_flatStructuralComputableWitnesses`
- **Where**: `ScheduleStep.lean:123-136`; `SHA256Round.lean:275-288, 332-345`; `LowerSigma*/UpperSigma*` (first Xor); `CompressBlock.lean:192-199`.
- **Signature use**: `(circuit) (parent input) (sub input expr) (offset) (proof: eval env parentInput = eval env' parentInput → <sub input agrees>) (sub.computableWitnesses) env env'`
```lean
exact Challenge.Utils.ComputableWitnessLemmas.FormalCircuit.subcircuit_flatStructuralComputableWitnesses
  LowerSigma1.circuit input input.wm2 offset
  (by intro env env' h_input; simp [circuit_norm] at h_input ⊢; exact h_input.1)
  LowerSigma1.computableWitnesses env env'
```

### W7. Subcircuit whose input depends on *witnessed* values: `…_of_condition` + `eval_mem_varFromOffset_fields_of_agreesBelow`
- **Where**: `LowerSigma0.lean:99-119`; `ScheduleStep.lean:137-178`; `SHA256Round.lean:289-381`; `SHA256Rounds.lean:235-274`; `MessageSchedule.lean:290-319`; `CompressBlock.lean:200-266`; `SHA256/Main.lean:424-589`.
- **Signature use**: the condition takes `(k env env' hle h_agree h_input)`.
```lean
exact …FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
  Xor32.circuit input ⟨r1, shr32 3 input⟩ n1
  (by
    intro k env env' hle h_agree h_input
    simp [circuit_norm] at h_input
    simp [circuit_norm]
    constructor
    · exact …eval_mem_varFromOffset_fields_of_agreesBelow
        h_agree (by
          have hlen : first.localLength offset = 32 := by
            dsimp [first, firstInput, Xor32.circuit]; rfl
          omega)
    · intro a ha
      simp [shr32] at ha
      rcases ha with ⟨i, rfl⟩
      by_cases h : i.val + 3 < 32
      · simp [h]; exact h_input _ (Vector.getElem_mem h)
      · simp [h, Expression.eval])
  Xor32.computableWitnesses env env'
```
- **Offset bookkeeping style** (`ScheduleStep.lean:99-118`): pre-`let` the circuits/offsets and pre-prove the lengths:
```lean
let s1Circuit : Circuit (F p) (Var (fields 32) (F p)) := LowerSigma1.circuit input.wm2
let s1 := s1Circuit.output offset
let n1 := offset + s1Circuit.localLength offset
…
have h_s1_len   : s1Circuit.localLength offset = 64 := by simp [s1Circuit, LowerSigma1.circuit, circuit_norm]
have h_sum0_len : sum0Circuit.localLength n2 = 33 := by simp [sum0Circuit, Add32.circuit, circuit_norm]
```
  then bounds are `by simp [sum0Circuit, n3, n2, n1, h_s1_len, Add32.circuit, circuit_norm] at hle ⊢; omega`.
- **Literal-offset style** (`SHA256Round.lean:289-381`): offsets written as raw constants (`offset + 32`, `+96`, `+129`, `+162`, `+195`, `+228`, `+260`, `+292`, `+324`, `+356`, `+389`, `+422`) with `simpa [circuit_norm, Add32.circuit, Add32.elaborated] using (…_of_condition … )`, plus four reusable local `have`s: `hstate_eval`, `hstate_eq`, `hk_eq`, `hw_eq`, `hgenerated_eq`.

### W8. Loop `computableWitnesses`: `foldlRange_..._iff` + `intro i` + accumulator rewrite
- **Where**: `MessageSchedule.lean:282-319`; `SHA256Rounds.lean:220-274`.
```lean
simp only [ …foldlRange_structuralComputableWitnesses_iff, …subcircuit_…_iff ]
intro i
rw [foldlAcc_eq_varSchedule_main offset input i.val i.isLt]    -- or `have hacc := …; rw [hacc]`
exact …subcircuit_flatStructuralComputableWitnesses_of_condition
  ScheduleStep.circuit input ⟨(varSchedule offset input i.val).get ⟨…⟩, …⟩
  (offset + i.val * (ScheduleStep.circuit (p := p)).localLength ⟨…⟩)
  (by
    intro k env env' hle h_agree h_input
    have hstep : env.AgreesBelow (offset + i.val * 227) env' :=
      ProverEnvironment.agreesBelow_of_le h_agree (by
        simp [ScheduleStep.circuit, circuit_norm] at hle
        simpa [ScheduleStep.circuit, circuit_norm] using hle)
    simp [circuit_norm]
    constructor
    · exact eval_mem_varSchedule_of_agreesBelow (offset := offset) (k := i.val)
        (by omega) hstep h_input (i.val + 16 - 2) (by omega) (by omega)
    · …)
  ScheduleStep.computableWitnesses env env'
```
- **Required support lemma**: `eval_mem_varSchedule_of_agreesBelow` / `eval_mem_stateVar_of_agreesBelow` — an induction over the accumulator description showing every slot below the current step is `env`/`env'`-invariant (`MessageScheduleTheorems.lean:188-236`, `SHA256RoundsTheorems.lean:96-138`).

### W9. Nested-vector eval extensionality (double `Vector.ext` + `ProvableType.getElem_eval_fields`)
- **Where**: `SHA256Rounds.lean:252-265`; `CompressBlock.lean:219-233, 292-300`; `MainTheorems.lean:205-216`.
```lean
apply Vector.ext
intro j hj
rw [← getElem_eval_vector env.toEnvironment (stateVar offset input.state i.val) j hj,
  ← getElem_eval_vector env'.toEnvironment (stateVar offset input.state i.val) j hj]
apply Vector.ext
intro b hb
rw [← ProvableType.getElem_eval_fields env.toEnvironment ((stateVar …)[j]'hj) b hb,
  ← ProvableType.getElem_eval_fields env'.toEnvironment ((stateVar …)[j]'hj) b hb]
exact eval_mem_stateVar_of_agreesBelow (offset := offset) (k := i.val) (by omega) hround h_input.1 j hj
  (((stateVar …)[j]'hj)[b]'hb) (Vector.getElem_mem _)
```

### W10. Private re-exports of sub-`computableWitnesses` before the composite proof
- **Where**: `CompressBlock.lean:149-159`; `SHA256/Main.lean:269-279`.
```lean
attribute [local irreducible] main MessageSchedule.circuit SHA256Rounds.circuit Add32.circuit

private theorem messageScheduleComputableWitnesses :
    (MessageSchedule.circuit (p := p)).ComputableWitnesses := MessageSchedule.computableWitnesses
```
  Purpose: force the instance/implicit resolution once, and keep the circuits irreducible in the big proof.

### W11. The top-level `computableWitness` bridge (the ONE hand-rolled induction, duplicated verbatim in both solutions)
- **Where**: `AssertBytes/Main.lean:66-104` **≡** `SHA256/Main.lean:590-627` (character-for-character apart from the prime).
- **Goal before**: `hflat` has the parent's `computableWitnessCondition` (which requires `eval env input = eval env' input` as an extra antecedent), but the challenge statement wants the plain `targetCondition` (only `AgreesBelow`).
- **Idiom**:
```lean
have hflat := …FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses input env env' hstruct
unfold Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition at hflat
rw [← Operations.forAll_toFlat_iff] at hflat ⊢
let targetCondition : Condition (F circomPrime) :=
  { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
apply FlatOperation.forAll_implies (F := F circomPrime) n ?_ hflat
have himplies : ∀ (ops : List (FlatOperation (F circomPrime))) (off : ℕ), n ≤ off →
    FlatOperation.forAll off
      (Condition.implies (…computableWitnessCondition input env env') targetCondition).ignoreSubcircuit ops := by
  intro ops off hoff
  induction ops generalizing off with
  | nil => simp [FlatOperation.forAll]
  | cons op ops ih =>
    cases op with
    | witness m compute =>
        simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
        constructor
        · intro hparent hagree
          exact hparent hagree (hinput env env' (ProverEnvironment.agreesBelow_of_le hagree hoff))
        · exact ih (m + off) (by omega)
    | assert e     => simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
                      exact ⟨by intro _; trivial, ih off hoff⟩
    | lookup l     => … ⟨by intro _; trivial, ih off hoff⟩
    | interact i   => … ⟨by intro _; trivial, ih off hoff⟩
exact himplies ((main input).operations n).toFlat n (le_refl n)
```
- **Why it closes**: the `witness` case discharges the parent-input equality from `hinput : OnlyAccessedBelow n (fun env => eval env input)` plus `agreesBelow_of_le`; the other three flat-operation constructors are vacuous.
- **This block is the single most copy-pasteable artifact in the corpus** — identical in both challenges.

### W12. Assertion subcircuits inside `Circuit.forEach` (AssertBytes-specific)
- **Where**: `AssertBytes/Main.lean:55-65`.
```lean
unfold main
simp only [Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff]
intro i
exact …FormalAssertion.assertion_structuralComputableWitnesses_of_condition
  (Num2Bits.circuit 8) input (input.buffer[i.val]) _
  (by
    intro k e1 e2 _ _ h_input
    have h_buffer : (eval e1 input).buffer[i.val] = (eval e2 input).buffer[i.val] := by rw [h_input]
    simpa [circuit_norm] using h_buffer)
  (Num2Bits.computableWitnesses 8) env env'
```

### W13. `FormalCircuitBase.computableWitnesses_implies` shortcut
- **Where**: `Num2Bits.lean:127-138`.
```lean
theorem computableWitness (n : ℕ) : ∀ offset x,
    ProverEnvironment.OnlyAccessedBelow offset (fun env => eval env x) →
    (main n x).ComputableWitnesses offset :=
  FormalCircuitBase.computableWitnesses_implies (computableWitnesses n)
```
  (plus a named alias `computableWitnesses_of_onlyAccessedBelow`) — the gadget-level form of the top-level obligation, derived instead of hand-rolled.

---

# 6. GADGET STRUCTURE

## 6.1 `FormalCircuit` vs `FormalAssertion` vs `GeneralFormalCircuit`
| Kind | Used for | Fields | Obligations |
|---|---|---|---|
| `GeneralFormalCircuit F Input Output` | **only** the two top-level `main`s | `main, Assumptions, Spec, ProverAssumptions, ProverSpec, soundness, completeness` (`Challenge.lean:36-45`) | `GeneralFormalCircuit.Soundness/Completeness` |
| `FormalCircuit F Input Output` | value-producing gadgets: `And32, Xor32, Ch32, Maj32, Add32, LowerSigma0/1, UpperSigma0/1, ScheduleStep, MessageSchedule, SHA256Round, SHA256Rounds, CompressBlock, SelectDigest` | `main; elaborated; Assumptions; Spec; soundness; completeness` | `Soundness (F p) main Assumptions Spec`, `Completeness (F p) main Assumptions` (**no `Spec` argument**) |
| `FormalAssertion F Input` | constraint-only gadgets: `Num2Bits`, `BitsBool`, `CheckLenFlags`, `CheckPaddedByte`, `CheckPad` | `main, elaborated, Assumptions, Spec, soundness, completeness, exposedChannels_eq` | `FormalAssertion.Soundness/Completeness (F p) main Assumptions Spec` (**both take `Spec`**) |

**Anonymous-field construction** (`And32.lean:96-97` and 10 others):
```lean
def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness
```
**When theorem statement ≠ field type**, wrap in `by simp only [thm]` (`BitsBool.lean:56-57`, `MessageSchedule.lean:270`, `SHA256Rounds.lean:192`, `CheckLenFlags.lean:158-159`, `CheckPad.lean:118-119`):
```lean
soundness := by simp only [soundness]
completeness := by simp only [completeness]
exposedChannels_eq := by intro _ _ exposed h; simp at h
```

## 6.2 `elaborate_circuit` vs `elaborate_circuit_with`
- Default: `instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by elaborate_circuit`.
- Underscore form for structural inference: `@[reducible] instance elaborated : ElaboratedCircuit (F p) _ _ main := by elaborate_circuit` (`Maj32.lean:55`, `SHA256Round.lean:79`).
- **Explicit output description** for loop circuits (`MessageSchedule.lean:58-64`, `SHA256Rounds.lean:53-60`):
```lean
@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit_with { output input i₀ := stateVar i₀ input.state 64 } using by
    simp only [circuit_norm]
    intros
    apply fin_foldl_eq_stateVar
```
```lean
elaborate_circuit_with { output input i₀ := varSchedule i₀ input 48 } using by
  simp only [circuit_norm]; intros; exact finFoldl_eq_varSchedule_48 _ _
```

## 6.3 `Num2Bits` (AssertBytes) — definition
`Solution/AssertBytes/Num2Bits.lean:32-102`. A `FormalAssertion (F circomPrime) field` on a **single field element**, parameterized by bit-count `n`:
```lean
def main (n : ℕ) (x : Expression (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let bits ← witnessVector n (fun env => fieldToBits n (x.eval env))
  Circuit.forEach bits (fun b => assertZero (b * (b - 1)))
  assertZero (x - fieldFromBitsExpr bits)

def Assumptions (_x : F circomPrime) : Prop := True
def Spec (n : ℕ) (x : F circomPrime) : Prop := x.val < 2 ^ n

def circuit (n : ℕ) : FormalAssertion (F circomPrime) field where
  main := main n; elaborated := elaborated n; Assumptions := Assumptions
  Spec := Spec n; soundness := soundness n; completeness := completeness n
```
Cost `⟨n, n+1⟩`. Built only from `witnessVector` / `Circuit.forEach` / `assertZero` — no prebuilt Clean gadget — but reuses `Clean.Utils.Bits`: `fieldToBits`, `fieldFromBitsExpr`, `fieldFromBits`, and inversion lemmas `fieldToBits_bits`, `fieldFromBits_eval`, `fieldFromBits_lt`, `fieldFromBits_fieldToBits`.

## 6.4 How subcircuits are invoked from `main`
Three surface syntaxes, all present:
1. **`do`-bind on the `circuit` value** (implicit `subcircuit`): `let r1 ← Xor32.circuit ⟨rotr32 7 x, rotr32 18 x⟩` (`LowerSigma0.lean:23`), `let state1 ← CompressBlock.circuit ⟨state0, paddedBlock padded 0⟩` (`SHA256/Main.lean:23`).
2. **Statement position for assertions**: `CheckPad.circuit ⟨input.messageLen, input.message, lenFlags, padded⟩` (`SHA256/Main.lean:20`), `CheckLenFlags.circuit (p := p) ⟨…⟩` (`CheckPad.lean:40`).
3. **Inside a loop combinator**: `Circuit.forEach input.buffer (fun x => Num2Bits.circuit 8 x)` (`AssertBytes/Main.lean:25`); `Circuit.foldlRange 64 input.state (fun s i => SHA256Round.circuit ⟨s, constWord32 Specs.SHA256.K[i].toNat, input.schedule[i]⟩)` (`SHA256Rounds.lean:36`); `Circuit.mapFinRange 8 fun i => Add32.circuit ⟨input.state[i], state'[i]⟩` (`CompressBlock.lean:36`); `Circuit.foldlRange 48 init (fun w i => do let wj ← ScheduleStep.circuit ⟨…⟩; return w.set (i.val+16) wj (by omega)) constantLength` (`MessageSchedule.lean:44-48`).

Cost/R1CS proofs address the same invocations as `subcircuit C b` (value-returning) or `assertion C b` (assertion) — see `Cost.lean` `costIs_sub_*` / `costIs_sub_checkPad` etc.

## 6.5 How a subcircuit's spec is consumed in the parent's soundness
Uniformly: **`simp only [Sub.Assumptions, Sub.Spec, and_imp] at h_holds` → `obtain ⟨c₁,…,cₖ⟩ := h_holds` → apply each `cᵢ` to the normalization facts from parent assumptions / earlier outputs → `rw [chain of .1 equations]`, `refine ⟨?_, last.2⟩`.** (S5/S6). For loop bodies, the same but *inside* the inductive step, after `rw [foldlAcc_eq_<desc> …] at h_holds` and `simp only [circuit_norm, Sub.circuit, Sub.elaborated, Sub.Spec, Sub.Assumptions] at h_holds` (S11).

## 6.6 `Circuit.ConstantLength` naming for the fold body
`MessageSchedule.lean:28-39` — the only place a `ConstantLength` instance is *named*:
```lean
/-- Naming it lets `Cost.lean` pass the same instance `main` folds with. -/
def constantLength : Circuit.ConstantLength (fun (x : SHA256Schedule (Expression (F p)) × Fin 48) => do …) where
  localLength := 227
  localLength_eq _ _ := by simp [circuit_norm, ScheduleStep.circuit, ScheduleStep.elaborated]
```
Consumed as `CostIs.foldlRange (constant := MessageSchedule.constantLength) …` (`Cost.lean:215`) and `IsR1CSCirc.foldlRange_inv (constant := MessageSchedule.constantLength) …` (`Cost.lean:802`).

---

# 7. RECURRING HELPER LEMMAS DEFINED IN THE SOLUTIONS

### `Solution/AssertBytes/Cost.lean`
| Name | Statement | Role |
|---|---|---|
| `IsR1CSCirc.forEach_mem` | index-aware `forEach` R1CS (`:33`) | lets booleanity rows use `AffineW xs[i]` |
| `costIs_num2Bits` | `CostIs (Num2Bits.main n x) ⟨n, n+1⟩` | cost leaf |
| `affine_fieldFromBitsExpr` | `AffineW bits → Affine (fieldFromBitsExpr bits)` | recomposition row is affine |
| `isR1CS_num2Bits` | `Affine x → IsR1CSCirc (Num2Bits.main n x)` | R1CS leaf |
| `costIs_assertion_num2Bits` / `isR1CS_assertion_num2Bits` | `assertion (Num2Bits.circuit n) x` wrappers | consumed by `mainCost` / `isR1CS` |
| `affineW_input_buffer` (in `Main.lean:116`) | `AffineProvable input → AffineW input.buffer` | projects the challenge's affine hypothesis |

### `Solution/SHA256/Theorems.lean` — SHARED across ≥2 gadgets
| Name | Statement | Role |
|---|---|---|
| `sum_bool_lt_two_pow n f (hf : ∀ i, f i ≤ 1)` | `∑ f i · 2ⁱ < 2ⁿ` | bound for out-of-range `testBit` branches; induction + `nlinarith [Nat.two_pow_pos m]` + `omega` |
| `testBit_binary_sum n f hf k` | `(∑ f i · 2ⁱ).testBit k = decide (f k = 1)` | **the** bit-extraction workhorse; `Nat.testBit_two_pow_mul_add` |
| `valueBits_testBit` | ditto specialized to `fields 32` | |
| `bool_finsum_xor_eq` | `∑ (f i ^^^ g i)·2ⁱ = (∑f)^^^(∑g)` | |
| `valueBits_lt_two_pow x hx` | `Normalized x → valueBits x < 2^32` | used by `Add32`, `SelectDigestTheorems` |
| `rotRight32_fin_testBit` | testBit of `rotRight32` | |
| `valueBits_rotr32_sum` / `valueBits_rotr32_eq` / `valueBits_rotate` / `Normalized_rotate` | rotation ↔ `rotRight32` | |
| `valueBits_shr32_eq` | shift ↔ `/2^k` | |
| `eval_rotr32`, `eval_shr32`, `eval_rotr32_vec` | eval commutes with the pure combinators | |
| `shr_isbool` | shifted-in zeros are boolean | |
| **`Normalized_eval_rotr32`, `valueBits_eval_rotr32`, `Normalized_eval_shr32`, `valueBits_eval_shr32`** | the four "eval-bridges" | **the entire soundness/completeness of `LowerSigma0/1`, `UpperSigma0/1` is 4 lines of these** (docstring at `:290-295`) |

### `Solution/SHA256/*Theorems.lean` — GADGET-PRIVATE
| File | Lemmas |
|---|---|
| `And32Theorems` | `bool_finsum_and` |
| `Ch32Theorems` | `field_ch_val`, `ch_finsum_eq`, `spec_of_constraint` |
| `Maj32Theorems` | `maj_eq_val_maj`, `maj_is_bool`, `bool_finsum_maj`, `spec_of_constraint` |
| `Add32Theorems` | `evalBitsNat` (**a `def` used by the circuit itself**), `fromBits_map_val_eq_valueBits`, `fieldFromBits_eq_valueBits`, `fromBitsExpr_eval_normalized`, `fromBitsExpr_val_eq`, `z_var_eval`, `isbool_of_bool_constraint`, `normalized_of_bool_holds`, `evalBitsNat_eq_valueBits`, `testBit_ite_eq`, `bit_decomp_sum`, `fieldFromBits_bit_decomp` |
| `MessageScheduleTheorems` | `varSchedule`, `valSchedule` (defs), `messageSchedule_eq_valSchedule`, `@[simp] scheduleStep_localLength` (`= 227 := rfl`), `@[simp] scheduleStep_output` (`= varFromOffset (fields 32) (n+194) := rfl`), `finFoldl_eq_varSchedule_48`, `foldlAcc_eq_varSchedule`, `foldlAcc_eq_varSchedule_main`, `eval_mem_varSchedule_of_agreesBelow` |
| `SHA256RoundsTheorems` | `stateVar`, `valStateAfterRound` (defs), `fin_foldl_eq_stateVar`, `foldlAcc_eq_stateVar`, `foldlAcc_eq_stateVar_main`, `eval_mem_stateVar_of_agreesBelow`, `normalized_constWord32`, `valueBits_constWord32`, `valueBits_constWord32_of_lt`, `sha256Compress_eq_valStateAfterRound` |
| `CheckPaddedByteTheorems` | `inputBufferLen_lt`, `eval_byteFromWord`, `eval_expectedPaddedByte`, `natCast_inj_lt_256`, `rhs_term_eq_specPaddedByte` |
| `CheckLenFlagsTheorems` | `eval_foldl_sum`, `isBool_val`, `natCast_eq_one_of_lt`, `exists_unique_of_sum_eq_one`, `inputBufferLen_lt`, `natSum_eq_one_of_cast`, **`onehot_from_constraints`** (the whole soundness math, isolated) |
| `SelectDigestTheorems` | `stateForLen_map`, `stateForLen_mem`, `valueBits_lt`, `val_fieldFromBits` |
| `PaddingTheorems` (shared, 430 lines) | `numBlocksForLen_pos/_le`, `getElem_toChunks`, `getElem_toChunks64`, `specBlock`, `chainState` (defs), `truncate_getElem`, `pad_byte_eq`, `pad_getElem_eq_specBlock`, `foldl_eq_chainState`, **`sha256_eq_chainState`**, `stateForLen_eq`, **`eval_finFoldl_add`**, **`oneHot_mul_sum`**, `specPaddedByteConst_lt`, `specPaddedByte_lt`, `wordByteVal_lt`, `valueBits_eq_bytesToWord32BE`, `paddedBitsValue_isBool`, `lenFlagsValue_oneHotAt`, `bit_recompose`, `byteIdx_paddedBitIndex`, `paddedBitIndex_mod_eight`, `paddedBitsValue_at_paddedBitIndex`, `paddedByteVal_paddedBitsValue`, `getElem_index_eq`, `paddedWord_getElem`, **`wordByteVal_paddedWord`**, **`paddedWord_isBool`** |
| `MainTheorems` | `hCircomPrimeLarge` (instance, `by norm_num [circomPrime]`), `paddedBitsWitness`, `lenFlagsWitness` (**witness generator defs used by `main`**), `normalized_constWord32`, `valueBits_constWord32(_of_lt)` (re-proved at `circomPrime`), `H0_lt`, `state0_getElem`, `state0_value`, `state0_normalized`, `paddedBytes_idx_lt`, `getElem_index_eq`, `paddedBlock_word_eq`, `wordByteVal_block`, **`paddedBlock_value`**, **`paddedBlock_normalized`**, `paddedBlock_varFromOffset_eval_eq_of_agreesBelow`, **`digest_final`** |

### `Solution/SHA256/Cost.lean` — helper lemmas defined for the cost/R1CS obligations
`affineW_varFromOffset_pvec`, `affineW_of_flatten_pvec`, `affineProvable_pvec_of_affineW`, `affineW_rotr32`, `affineW_shr32`, `affine_fieldFromBitsExpr`, `affineW_{xor32,and32,add32,ch32,maj32}_output`, `affineW_constWord32`, `affineW_mapRange_var`, `affineW_subOut_{xor32,add32,ch32,maj32,upperSigma0,upperSigma1,lowerSigma0,lowerSigma1,scheduleStep,messageSchedule,sha256Rounds,compressBlock,selectDigest}`, `affineW_sha256Round_out_w0..w7` + `affineW_sha256Round_output`, `affineW_rounds_input_state/_sched`, `affineW_stateVar`, `affineW_varSchedule`, **`isR1CSRow_sub_add_mul`**, `affine_byteFromWord`, **`r1csRow_checkPaddedByte`**, `affineW_paddedWord`, `affineW_paddedBlock`, `affine_selectedWordExpr`, `affineW_state0`, `affineW_input_message`, `affine_input_messageLen`.

### Recurring "instance-derivation" boilerplate
```lean
instance : Fact (p > 2) := .mk (by
  have h : (2 : ℕ) < 2^33 := by norm_num
  exact h.trans h_large.out)
```
appears in `CheckPaddedByteTheorems.lean:8`, `CheckLenFlagsTheorems.lean:8`, `CheckPad.lean:11`, `PaddingTheorems.lean:10`; the `decide` variant at `SHA256Rounds.lean:9-11` (`instance fact_p_gt_2_of_2_pow_33`, uses `by decide` instead of `norm_num`).

---

# 8. COST BOOKKEEPING STYLE (`Cost.lean` files)

## AssertBytes (`Solution/AssertBytes/Cost.lean`, 94 lines)
Flat, single-gadget. Order: bespoke combinator (`IsR1CSCirc.forEach_mem`) → cost leaf (`costIs_num2Bits`) → affineness helper (`affine_fieldFromBitsExpr`) → `attribute [local irreducible] …` → R1CS leaf (`isR1CS_num2Bits`) → assertion wrappers. `Main.lean` then does `CostIs.forEach (fun a n => costIs_assertion_num2Bits 8 a n)` — a one-line `mainCost`. Decomposition: `16 × ⟨8, 9⟩ = ⟨128, 144⟩`.

## SHA256 (`Solution/SHA256/Cost.lean`, 1262 lines) — five bands
1. **`ProvableVector` affineness plumbing** (`:22-68`).
2. **Named `Count` constants** (`:70-96`) — symbolic, compositional (M4).
3. **`CostIs` band** (`:98-307`):
   - primitives → `costIs_{and32,xor32,ch32,add32,maj32}` (structural `CostIs.bind` chains over the gadget's own `do`-block);
   - `costIs_sub_*` wrappers (one per gadget, heartbeat isolation);
   - composites → `costIs_{lowerSigma0/1,upperSigma0/1}` (`bind` of two `costIs_sub_xor32`), `costIs_sha256Round` (11 `bind`s), `costIs_scheduleStep` (5), `costIs_messageSchedule` (`CostIs.foldlRange (constant := …)`), `costIs_sha256Rounds` (`CostIs.foldlRange`), `costIs_compressBlock` (`bind`+`bind`+`CostIs.mapFinRange`);
   - `*Cost_proof` instantiations at offset 0 (M6).
4. **`IsR1CSCirc` band** (`:309-972`): `attribute [local irreducible]` → affine propagation lemmas → `r1cs_<gadget>` leaves → `<gadget>_isR1CS` full-statement wrappers (`isR1CS_of_IsR1CSCirc`) → subcircuit-output affineness → `r1cs_sub_*` wrappers → loop variants (`foldlRange_inv`) → recursive accumulator affineness.
5. **Padding band** (`:974-1258`): `isR1CSRow_sub_add_mul`, `r1csRow_checkPaddedByte`, `costIs_{checkLenFlags,bitsBool,checkPaddedByte}`, `r1cs_{checkLenFlags,bitsBool,checkPaddedByte}`, size-generic `*_sub_bitsBool`, `attribute [local irreducible] byteFromWord expectedPaddedByte paddedWord paddedBit paddedBlock`, `costIs_checkPad`/`r1cs_checkPad` (`⟨0, 3138⟩`), `costIs_sub_checkPad`/`r1cs_sub_checkPad`, `costIs_selectDigest`/`r1cs_selectDigest`/`costIs_sub_selectDigest`/`affineW_subOut_selectDigest`, `costIs_sub_compressBlock`/`r1cs_sub_compressBlock`, `affineW_state0`, top-level input projections.

**Chaining discipline**: every `CostIs` fact appears in *two* forms — the raw `costIs_X : CostIs (X.main …) XCost` and the wrapped `costIs_sub_X : CostIs (subcircuit X.circuit b) XCost := CostIs.subcircuit (costIs_X _)`. Parents only ever use the wrapped form. Identical for `r1cs_X` / `r1cs_sub_X`. `CostIs.assertion` is the assertion-flavored analogue of `CostIs.subcircuit`.

**Concrete SHA256 numbers** (derivable from the defs): `add32Cost = ⟨33,34⟩`; `sigmaCost = ⟨64,64⟩`; `sha256RoundCost = ⟨455, 458⟩`; `sha256RoundsCost = 64 ×`; `messageScheduleCost = 48 × ⟨227,230⟩`; `compressBlockCost = 48·227 + 64·455 + 8·33` allocations; `selectDigestCost = ⟨8, 2048⟩`; `checkPad = ⟨0, 3138⟩`; total `⟨204224, 209586⟩`.

---

# 9. TACTIC FREQUENCY BY OBLIGATION

| Tactic / simp set | soundness | completeness | mainCost | isR1CS | computableWitness |
|---|---|---|---|---|---|
| `circuit_proof_start [...]` | ✅ universal opener | ✅ universal opener | — | — | — |
| `circuit_norm` (simp set) | ✅ (`simp only [circuit_norm, Sub.circuit, Sub.elaborated, Sub.Spec, Sub.Assumptions]`) | ✅ same | ✅ (in `simp [X, circuit_norm]` length proofs) | ✅ (`simp only [circuit_norm, subcircuit, C, C.elaborated]`) | ✅ (`simp [circuit_norm] at h_input ⊢`) — the dominant simp set here |
| `omega` | ✅ (`ScheduleStep.lean:74` add32 reassociation; index arith) | ✅ (index bounds) | — | ✅ (`(by omega)` in `rcases`/`isR1CSRow_of_r1csProducts`) | ✅ **everywhere** (offset bounds: `by omega`, `by simp […] at hle ⊢; omega`) |
| `decide` | — | — | — | — | — (only `by decide` for `2 < 2^33` at `SHA256Rounds.lean:10` and `⟨64, by decide⟩` in `PaddingTheorems.lean:66`) |
| `native_decide` | **absent by design** (docstrings repeatedly say "no `native_decide`, no large `decide`") | | | | |
| `linear_combination` | **absent** — its role is played by `ring_nf; ring_nf at h; exact h` and `sub_eq_zero.mp` | | | | |
| `ring` / `ring_nf` | ✅ (S3 tier 2) | ✅ (C2 closer, ~15×) | — | — | — |
| `norm_num` | ✅ (`Ch32Theorems.lean:36`, bit-bound `2^n ≤ 2^j`, `Maj32Theorems.lean:24,31`) | ✅ | — | ✅ (`hCircomPrimeLarge := ⟨by norm_num [circomPrime]⟩`) | — |
| `push_cast` | — | ✅ (`Add32.lean:114,186,252`) | — | — | — |
| `fin_cases` | ✅ (`SHA256Round.lean:141`, `SHA256/Main.lean:111,124`) | ✅ (`SHA256/Main.lean:260`) | — | — | — |
| `rcases … with rfl\|…\|rfl` (omega-driven case split) | ✅ | ✅ | — | ✅ (`Cost.lean:734,834,1198`) | ✅ (`SHA256RoundsTheorems.lean:126`) |
| `induction … with \| zero \| succ` | ✅ (S11, S9's `sum_bool_lt_two_pow`/`testBit_binary_sum`) | ✅ (C7) | — | ✅ (R10) | ✅ (W11's `induction ops generalizing off`) |
| `nlinarith` | ✅ (`Theorems.lean:32`, `PaddingTheorems.lean:123`) | — | — | — | — |
| `linarith` | ✅ (`Add32.lean:135,144,145`, `Add32Theorems.lean:58`) | ✅ (`Add32.lean:175,198`) | — | — | — |
| `and_intros` | — | — | — | — | ✅ **the splitter** after the `*_iff` simp set |
| `simp_all` / `simp_all only` | ✅ (`CompressBlock.lean:111`, `SHA256Round.lean:205`) | — | — | — | — |
| `Vector.ext` / `apply Vector.ext; intro i hi` | ✅ | ✅ | — | — | ✅ (W4, W9) |
| `convert … using n` | ✅ (`SHA256Round.lean:142-157`, `SHA256/Main.lean:60`, `MainTheorems.lean:148`) | — | — | — | — |
| `attribute [local irreducible]` | — | — | — | ✅ **essential** (R2, R13) | ✅ (before every composite `computableWitnesses`) |
| `set_option maxRecDepth 8000` | — | — | ✅ (`Main.lean:637`) | ✅ (same section) | ✅ (`CheckPad.lean:125`) |
| `omit … in` | ✅ | ✅ (C9) | — | — | — |
| `trivial` | — | — | — | — | ✅ (W3 closer for assertion ops) |
| `dsimp [x, y, z]` | — | — | — | — | ✅ (offset unfolds, `SHA256/Main.lean:334-399`) |
| `show … from …` / `change` | ✅ | ✅ | ✅ (`show CostIs (main input) ⟨…⟩ from`) | ✅ (`show isR1CSRow (_ * (_ - 1))`, `change Affine (…)`) | ✅ (W1's `change Operations.forAllFlat …`) |

**Recurring named-lemma toolbox** (cross-obligation):
`getElem_eval_vector`, `CircuitType.eval_var_fields`, `CircuitType.eval_var_fields_prover`, `CircuitType.eval_var_field_prover`, `CircuitType.eval_expression_prover_to_verifier`, `ProvableType.getElem_eval_fields`, `ProvableType.varFromOffset_fields`, `eval_vector`, `Vector.getElem_map`, `Vector.getElem_ofFn`, `Vector.getElem_mapRange`, `Vector.getElem_mapFinRange`, `Vector.getElem_finRange`, `Vector.getElem_set_self`, `Vector.getElem_set_ne`, `Vector.getElem_append_left/right`, `Vector.getElem_replicate`, `Vector.getElem_rotate`, `Vector.getElem_flatten`, `Vector.getElem_mem`, `Vector.mem_iff_getElem`, `Vector.ext_iff`, `Vector.inductPush`, `Fin.foldl_succ_last`, `Fin.foldl_zero`, `Fin.sum_univ_castSucc`, `Fin.foldl_to_sum`, `Fin.ext`, `Finset.sum_congr`, `Finset.sum_eq_single`, `Finset.sum_ite_eq'`, `Finset.sum_pair`, `Finset.sum_le_sum_of_subset`, `Nat.eq_of_testBit_eq`, `Nat.testBit_{and,xor,div_two_pow,mod_two_pow,two_pow_mul_add,two_pow_sub_one,eq_false_of_lt}`, `Nat.mod_pow_succ`, `Nat.mod_add_div`, `ZMod.{val_add,val_mul,val_zero,val_one,val_natCast_of_lt,natCast_val,cast_id}`, `IsBool.{iff_mul_sub_one,and_is_bool,xor_is_bool,and_eq_val_and,xor_eq_val_xor,val_of_IsBool,zero,one}`, `add_neg_eq_zero`, `sub_eq_zero`, `eq_of_sub_eq_zero`, `ProverEnvironment.agreesBelow_of_le`.

---

# 10. SHA256 FILE LAYERING (what each layer proves)

```
Challenge/Specs/SHA256                        (trusted spec: Ch, Maj, σ/Σ, K, H0, messageSchedule,
                                               sha256Round, sha256Compress, compressBlock, pad,
                                               truncate, sha256, bytesToBlock, bytesToWord32BE, Spec)
Challenge/Instances/SHA256/Interface          Input/Output structs, circomPrime, Assumptions, Spec,
                                               ProverAssumptions, ProverSpec, fieldElemsToNat
Challenge/Instances/SHA256/{Challenge,Cost}   the six `sorry`'d signatures + the 42/42 stub

── LAYER 0: pure defs, no proofs ─────────────────────────────────────────────
BitwiseOps.lean      SHA256State/Block/Schedule abbrevs, valueBits, Normalized,
                     fromBitsExpr, constWord32, not32, rotr32, shr32  (no constraints)
Common.lean          paddedBlocksLen/BitsLen/BytesLen, numBlocksForLen, specPaddedByteConst,
                     specPaddedByte, paddedBitIndex(_lt), paddedByteVal, wordByteVal, OneHotAt,
                     byteFromWord, paddedBit, paddedBlock, paddedWord, expectedPaddedByte (factored!),
                     stateForLen, lenFlagsValue, paddedBitsValue

── LAYER 1: shared math ──────────────────────────────────────────────────────
Theorems.lean        valueBits/testBit/rotr/shr lemmas reused by ≥2 gadgets
PaddingTheorems.lean specBlock, chainState, sha256_eq_chainState, stateForLen_eq,
                     eval_finFoldl_add, oneHot_mul_sum, paddedWord/paddedByteVal bridges

── LAYER 2: leaf gadgets (each = <Gadget>.lean + optional <Gadget>Theorems.lean) ─
And32 / Xor32 / Ch32 / Maj32 / Add32          FormalCircuit (fields 32)-valued
BitsBool                                      FormalAssertion (fields n), generic in n

── LAYER 3: pure-combinator compositions of Xor32 ────────────────────────────
LowerSigma0/1, UpperSigma0/1                  2 × Xor32.circuit over rotr32/shr32; soundness is
                                              4 lines using Theorems' eval-bridges

── LAYER 4: per-step / per-round gadgets ─────────────────────────────────────
ScheduleStep      LowerSigma1 + LowerSigma0 + 3×Add32; 227 witnesses, output at rel. offset 194;
                  Spec stated in BALANCED add32 form, reassociation done inside soundness
SHA256Round       UpperSigma1 + Ch32 + 4×Add32 + UpperSigma0 + Maj32 + 3×Add32; 455 witnesses

── LAYER 5: loops (gadget + *Theorems with the accumulator descriptions) ─────
MessageSchedule   + MessageScheduleTheorems (varSchedule/valSchedule, foldlAcc_eq_*,
                    messageSchedule_eq_valSchedule, eval_mem_varSchedule_of_agreesBelow,
                    finFoldl_eq_varSchedule_48 for the elaborated instance)
SHA256Rounds      + SHA256RoundsTheorems (stateVar/valStateAfterRound, fin_foldl_eq_stateVar,
                    foldlAcc_eq_stateVar(_main), eval_mem_stateVar_of_agreesBelow,
                    sha256Compress_eq_valStateAfterRound, constWord32 lemmas)

── LAYER 6: block compression ────────────────────────────────────────────────
CompressBlock     MessageSchedule ▸ SHA256Rounds ▸ mapFinRange 8 Add32 (Davies–Meyer);
                  also exports eval_mem_output_of_agreesBelow / eval_output_of_agreesBelow /
                  eval_circuit_output_of_agreesBelow — consumed ONLY by Main's computableWitness

── LAYER 7: padding & selection ──────────────────────────────────────────────
CheckLenFlags (+Thms)     assertion: flags boolean, sum = 1, weighted sum = messageLen
                          ⟹ messageLen.val < 256 ∧ OneHotAt
CheckPaddedByte (+Thms)   assertion FAMILY indexed by j : Fin paddedBytesLen
CheckPad                  bundles CheckLenFlags ▸ BitsBool paddedBitsLen ▸ forEach CheckPaddedByte
SelectDigest (+Thms)      witness 8 words + 8×256 one-hot rows selecting stateForLen

── LAYER 8: top level ────────────────────────────────────────────────────────
MainTheorems.lean  witness generators (paddedBitsWitness/lenFlagsWitness), H0-state lemmas,
                   paddedBlock ↦ specBlock bridge, digest_final, hCircomPrimeLarge instance
Cost.lean          ALL CostIs + IsR1CSCirc certificates, bottom-up (see §8)
Main.lean          main (2 witnessVectors + CheckPad + 5×CompressBlock + SelectDigest),
                   elaborated, soundness, completeness, computableWitness  [section 1]
                   allocations/constraints, mainCost, isR1CS                [section 2]
```

**Layering invariant visible throughout**: a gadget file `X.lean` keeps **exactly six declarations** (`main`, `elaborated`, `Assumptions`/`Spec`, `soundness`, `completeness`, `circuit`, `computableWitnesses`); *all* supporting math is exiled to `XTheorems.lean`. Docstrings state this explicitly (`SHA256RoundsTheorems.lean:15-16`: *"These are gadget support for `SHA256Rounds`; the gadget file keeps the six required declarations."*; `MessageScheduleTheorems.lean:16`: same).

**Layering invariant for cost/R1CS**: cost & R1CS never live in gadget files (except `AssertBytes`, where the whole solution is 3 files). `Cost.lean` imports the gadgets, never the reverse; `Main.lean` imports `Cost.lean`.
