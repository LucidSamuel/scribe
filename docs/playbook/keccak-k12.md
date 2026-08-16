# zkGolf Reference-Solution Proof-Pattern Catalog
## Corpus: `Solution/KeccakF1600/` (21 files), `Solution/KangarooTwelveGF2/` (5 files), matching `Challenge/Instances/*`

All paths below are absolute-relative to `/Users/lucidsamuel/experiments/scribe/corpus/zk-golf-challenges/`.
Root prefix: `R = /Users/lucidsamuel/experiments/scribe/corpus/zk-golf-challenges`

---

## 0. Obligation surface (what must be discharged)

### KeccakF1600 — `R/Challenge/Instances/KeccakF1600/Challenge.lean`
```lean
def main : Var Input (F circomPrime) → Circuit (F circomPrime) (Var Output (F circomPrime))   -- :12
instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main                      -- :14
theorem soundness   : GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec     -- :16
theorem completeness: GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec -- :17
theorem mainCost    : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩           -- :19
theorem isR1CS      : Challenge.CostR1CS.isR1CS main                                           -- :20
theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env => eval env input) →
  Circuit.ComputableWitnesses (main input) n                                                    -- :22-24
```
- `Interface.lean:41-49`: state is `Vector F 1600`, one **field element per bit**; `fieldElemsToNat := xs.map ZMod.val`; `Spec` = `Specs.Keccak.Spec (fieldElemsToNat input.state) (fieldElemsToNat output.state)`; `Assumptions` = `Specs.Keccak.Assumptions` = `IsBitString` = `∀ i, xs[i] < 2`.
- `ProverSpec := True` (`Interface.lean:57-60`) → completeness has an almost-trivial output obligation.
- Field: `circomPrime` (BN254 scalar), `axiom hCircomPrime` (`Interface.lean:33-36`).

### KangarooTwelveGF2 — `R/Challenge/Instances/KangarooTwelveGF2/Challenge.lean`
Same five, except the R1CS obligation is the **canonical** variant:
```lean
theorem isR1CS_Cidentity : Challenge.CostR1CS.isR1CS_Cidentity main   -- :22
```
- `Interface.lean:22-26`: `Assumptions := True`; `Spec input output := output.state = Specs.KangarooTwelve.keccakP1600_12 input.state` — a **direct vector equality over `F 2`**, no `ℕ`/value abstraction at all.
- Field: `Challenge.F2Bits.p2 = 2` (`R/Challenge/Utils/F2Bits.lean:17`), so `+` is XOR and `*` is AND natively.

**This difference is the single largest structural driver**: KeccakF1600 must transport between `F p` bit vectors and `ℕ` lane values (`valueBits`, `Normalized`), KangarooTwelveGF2 does not.

Score numbers: Keccak `allocations = constraints = 153600` (`Solution/KeccakF1600/Main.lean:148-149`), K12 `= 19200` (`Solution/KangarooTwelveGF2/Main.lean:11-13`). Challenge placeholder Cost files both say `42` (`Challenge/Instances/*/Cost.lean:1-2`).

---

## 1. 64-bit lane representation (KeccakF1600)

`R/Solution/KeccakF1600/BitwiseOps.lean`

| Decl | Line | Statement / role |
|---|---|---|
| `KeccakBitState` | 13 | `abbrev KeccakBitState := ProvableVector (fields 64) 25` — 25 lanes × 64 one-bit field elements |
| `KeccakBitRow` | 32 | `ProvableVector (fields 64) 5` — the θ parity row |
| `valueBits` | 16 | `def valueBits (bits : Vector (F p) 64) : ℕ := Finset.univ.sum fun (i : Fin 64) => bits[i].val * 2^i.val` — LSB-first weighted sum, **the** abstraction function |
| `Normalized` | 20 | `∀ i : Fin 64, w[i] = 0 ∨ w[i] = 1` — booleanity, carried as a conjunct in **every** gadget Spec |
| `stateValue` | 24 | `s.map valueBits : Vector ℕ 25` |
| `StateNormalized` / `RowNormalized` | 28 / 39 | `∀ i : Fin 25/5, Normalized s[i.val]` |
| `rotl` | 44 | `a.rotate (64 - k % 64)` — ρ as **pure index wiring, zero constraints** |
| `notBits` | 48 | `a.map fun ai => 1 - ai` — free (affine) |
| `xorConst` | 52 | `Vector.ofFn fun i => if c.testBit i.val then 1 - a[i] else a[i]` — ι as free wiring |
| `piSource` | 57 | `⟨(j%5 + 3*(j/5))%5 + 5*(j%5), by omega⟩` — π index permutation as a `Fin 25 → Fin 25` |
| `chiSource1/2` | 61 / 65 | `(x+1,y)` and `(x+2,y)` row neighbours, `by omega` for the bound |
| `iotaWire` | 70 | `Vector.mapFinRange 25 fun j => xorConst (if j.val = 0 then rc else 0) s[j.val]` — **per-lane map, not `Vector.set`**, deliberately so the χ-output var is never indexed at lane 0 |
| `rhoPiWire` | 76 | `Vector.ofFn fun j => rotl rhoOffsets[(piSource j).val] s[(piSource j).val]` — ρ∘π fused, free |
| `toLanes` / `fromLanes` | 81 / 85 | 1600-bit ↔ 25×64 slicing/flattening |
| `thetaCSpec`,`thetaDSpec`,`thetaXorSpec`,`rhoPiSpec`,`chiSpec`,`iotaSpec` | 89–114 | ℕ-level step functions mirroring the circuit decomposition exactly (each a `Vector.ofFn`, so `... = .ofFn ...` is `rfl`) |

**Key design rule visible in the corpus: ρ, π, ι, ¬ cost zero.** Only XOR and AND witness/constrain. This is why cost is exactly `24 × 6400`.

---

## 2. Lane-level gadget pattern (XorLane / AndLane / Xor5Lane / ChiLane)

### 2.1 Canonical gadget skeleton (identical in all four)
```
def <op>Lane (a b : Var (fields 64) (F p)) : Circuit (F p) (Var (fields 64) (F p)) := do
  let z ← witnessVector 64 fun env => Vector.ofFn fun (i : Fin 64) => <compute>
  Circuit.forEach (Vector.finRange 64) fun i => assertZero (<row i>)
  return z
structure Inputs (F : Type) where ... deriving ProvableStruct
def main / def Assumptions / def Spec
instance elaborated : ElaboratedCircuit ... := by elaborate_circuit
theorem soundness : Soundness (F p) main Assumptions Spec
theorem completeness : Completeness (F p) main Assumptions
def circuit : FormalCircuit (F p) Inputs (fields 64) where main; elaborated; Assumptions; Spec; soundness; completeness
theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses
```
Note the **anonymous field-punning structure instance** `where main; elaborated; Assumptions; Spec; soundness; completeness` (`XorLane.lean:101-102`, `AndLane.lean:81-82`, `Xor5Lane.lean:59-60`, `ChiLane.lean:57-58`).

### 2.2 Constraint rows
- XOR (`XorLane.lean:23`): `assertZero (z[i] - a[i] - b[i] + 2 * a[i] * b[i])` — one R1CS row, product `a·b`.
- AND (`AndLane.lean:19`): `assertZero (z[i] - a[i] * b[i])`.
- Witness computation for XOR uses the ℕ-level xor cast back into the field: `((env a[i]).val ^^^ (env b[i]).val : F p)` (`XorLane.lean:21`).

### 2.3 Spec shape — always `value ∧ Normalized`
```lean
def Spec (input : Inputs (F p)) (z : fields 64 (F p)) : Prop :=
  valueBits z = valueBits input.a ^^^ valueBits input.b ∧ Normalized z   -- XorLane.lean:37-38
  valueBits z = valueBits input.a &&& valueBits input.b ∧ Normalized z   -- AndLane.lean:33-34
  valueBits z = (valueBits a ^^^ (Specs.Keccak.notLane 64 (valueBits b) &&& valueBits c)) ∧ Normalized z -- ChiLane.lean:24-28
```
`Normalized z` in the *conclusion* is what makes composition possible: the next gadget's `Assumptions` are exactly `Normalized` of its inputs, so the caller feeds the callee's output-normalization straight into the callee's precondition. This is the single most reused compositional invariant.

---

## 3. SOUNDNESS — pattern catalog

### S1. **Leaf-gadget bit-level soundness** (witness ⇒ arithmetic ⇒ value)
- Where: `Solution/KeccakF1600/XorLane.lean:43-80`, `AndLane.lean:39-72`
- Goal before: after `circuit_proof_start [xorLane]` the context has `i₀, env, input_var, input, h_input, h_assumptions, h_holds`; goal is `Spec` with the output expressed as `Vector.map (Expression.eval env) (Vector.mapRange 64 fun i => var {index := i₀ + i})`.
- Idiom (five sub-steps, verbatim):
  1. `circuit_proof_start [xorLane]` then `obtain ⟨ha, hb⟩ := h_assumptions; obtain ⟨h_input_a, h_input_b⟩ := h_input`
  2. **input-transport lemma per component** (`XorLane.lean:47-54`):
     ```lean
     have h_ai : ∀ i : Fin 64, Expression.eval env input_var_a[i.val] = input_a[i] := by
       intro i
       have := Vector.ext_iff.mp h_input_a i i.isLt
       simp [Vector.getElem_map] at this; exact this
     ```
  3. **row ⇒ closed form** (`XorLane.lean:56-62`):
     ```lean
     have key : env.get (i₀ + i.val) - (input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i]) = 0 := by
       ring_nf; ring_nf at h; exact h
     exact sub_eq_zero.mp key
     ```
     AND variant is shorter (`AndLane.lean:54`): `exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact this)`
  4. **output reification** (`XorLane.lean:63-67`, `AndLane.lean:55-59`):
     ```lean
     have h_z : Vector.map (Expression.eval env) (Vector.mapRange 64 fun i => (var {index := i₀ + i} : Expression (F p)))
         = Vector.ofFn fun i : Fin 64 => env.get (i₀ + i.val) := by
       ext i; simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
     rw [h_z]
     ```
  5. **value transfer via the ℕ-bit lemma**:
     ```lean
     simp only [valueBits]
     simp_rw [show ∀ i : Fin 64, (Vector.ofFn fun j : Fin 64 => env.get (i₀ + j.val))[i] = env.get (i₀ + i.val) from fun i => by simp [Vector.getElem_ofFn]]
     simp_rw [h_eq, IsBool.xor_eq_val_xor (ha _) (hb _)]
     exact (bool_finsum_xor_eq 64 (fun i => (input_a[i] : F p).val) (fun i => (input_b[i] : F p).val)
       (fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]) ...)
     ```
     AND uses `bool_finsum_and ... .symm` (`AndLane.lean:67-69`, note the trailing `.symm` because the lemma is oriented the other way).
- Normalization branch: `exact IsBool.xor_is_bool (ha i) (hb i)` / `IsBool.and_is_bool` (`XorLane.lean:69`, `AndLane.lean:61`).
- Why it closes: `bool_finsum_xor_eq` / `bool_finsum_and` (see §8) transport a bitwise op on 0/1 coefficients through the weighted-sum abstraction, reducing everything to `Nat.eq_of_testBit_eq`.

### S2. **Sequential-composition soundness (`obtain` chain + `rw` chain)**
- Where: `Xor5Lane.lean:37-47`, `Theta.lean:27-36`, `ChiLane.lean:33-43`, `KeccakRound.lean:27-41`
- Goal before: `h_holds` is an n-tuple of implications `Assumptions_sub → Spec_sub`.
- Idiom (`Xor5Lane.lean:38-47`):
  ```lean
  circuit_proof_start [XorLane.circuit]
  simp only [XorLane.Assumptions, XorLane.Spec, and_imp] at h_holds
  obtain ⟨ha, hb, hc, hd, he⟩ := h_assumptions
  obtain ⟨c1, c2, c3, c4⟩ := h_holds
  obtain ⟨v1, n1⟩ := c1 ha hb
  obtain ⟨v2, n2⟩ := c2 n1 hc      -- feeds previous *normalization* as next precondition
  obtain ⟨v3, n3⟩ := c3 n2 hd
  obtain ⟨v4, n4⟩ := c4 n3 he
  refine ⟨?_, n4⟩
  rw [v4, v3, v2, v1]
  ```
- Why it closes: `rw [v4, v3, v2, v1]` unfolds the value equations right-to-left until both sides are the same ℕ expression; `and_imp` is essential to curry the sub-Assumptions.
- Theta variant (`Theta.lean:31-36`): `obtain ⟨h_c, h_d, h_x⟩ := h_holds` then `h_c h_assumptions`, `h_d c_norm`, `h_x ⟨h_assumptions, d_norm⟩`, closing with `rw [out_val, d_val, c_val]`.

### S3. **Loop-gadget soundness via `*_value_ext` + per-index spec instantiation**
- Where: `ThetaC.lean:28-51`, `ThetaD.lean:26-51`, `ThetaXor.lean:33-53`, `Chi.lean:27-45`
- Goal before: `StateNormalized out ∧ stateValue out = <ofFn spec>` where `out` is a `mapFinRange` output.
- Idiom:
  ```lean
  circuit_proof_start [Xor5Lane.circuit, Xor5Lane.Assumptions, Xor5Lane.Spec]
  have hs := h_input
  apply rowNormalized_value_ext                       -- or stateNormalized_value_ext
  simp only [thetaCSpec_loop, circuit_norm, eval_vector, stateValue]
  intro x
  have hb : ∀ j (hj : j < 25), Vector.map (Expression.eval env) input_var[j] = input[j] := by
    intro j hj
    have h := getElem_eval_vector (α := fields 64) env input_var j hj
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  have harg : Normalized ... ∧ ... := by rw [hb _ (by omega), ...]; exact ⟨h_assumptions ⟨x.val, by omega⟩, ...⟩
  obtain ⟨h_val, h_norm⟩ := h_holds x harg
  refine ⟨h_norm, ?_⟩
  rw [Vector.getElem_ofFn, h_val, hb _ (by omega), ...]
  ```
- Two reusable pieces here:
  - **`hb` "getElem-of-eval" transport lemma**, re-derived inline in every loop gadget: `getElem_eval_vector` + `CircuitType.eval_var_fields` + `rw [hs]`. Appears at `ThetaC.lean:34-38`, `ThetaD.lean:32-36`, `ThetaXor.lean:40-47`, `Chi.lean:33-37`, and their completeness twins.
  - **`*Spec_loop` `rfl` lemmas** (`ThetaC.lean:24-26`, `ThetaD.lean:22-24`, `ThetaXor.lean:30-31`, `Chi.lean:22-25`) — restate the ℕ spec as literally the `Vector.ofFn` the loop produces, all proved `:= rfl`. They exist purely so `simp only [thetaCSpec_loop, ...]` puts the goal into per-index form.
- Why it closes: `rowNormalized_value_ext`/`stateNormalized_value_ext` (`Theorems.lean:313-334`) converts an ∧-of-vector-equalities goal into `∀ i, Normalized s[i] ∧ valueBits s[i] = rhs[i]`, which is exactly what the sub-circuit's `Spec` gives per index.

### S4. **Wiring-commutation soundness (free ρ/π/ι)**
- Where: `KeccakRound.lean:27-41`
- Goal before: χ subcircuit's hypothesis mentions `eval env (rhoPiWire θvar)`; the ℕ-goal mentions `Specs.Keccak.keccakRound 64 rc`.
- Idiom (verbatim):
  ```lean
  rw [eval_keccakState, eval_rhoPiWire_vec, ← eval_keccakState] at h_chi
  obtain ⟨chi_norm, chi_val⟩ := h_chi (StateNormalized_rhoPiWire _ theta_norm)
  rw [stateValue_rhoPiWire _ theta_norm, theta_val] at chi_val
  rw [eval_keccakState] at chi_norm chi_val
  rw [keccakRound_decompose rc, eval_keccakState, map_iotaWire]
  refine ⟨StateNormalized_iotaMap rc _ chi_norm, ?_⟩
  rw [stateValue_iotaMap rc hrc _ chi_norm, chi_val]
  ```
- The `rw [eval_X, eval_wire_vec, ← eval_X]` **push-eval-through-wiring sandwich** is the signature move. `eval_keccakState` (`KeccakRoundTheorems.lean:17`) is the bridge `eval env X = Vector.map (Vector.map (Expression.eval env)) X`.
- Why it closes: `keccakRound_decompose` (`KeccakRoundTheorems.lean:142-146`) rewrites the *trusted* spec into the composition of the solution's own step functions; then each `stateValue_*`/`StateNormalized_*` lemma discharges one layer.

### S5. **Spec-decomposition by `interval_cases` (bridging trusted spec ↔ gadget spec)**
- Where: `KeccakRoundTheorems.lean:112-138` — `theta_eq`, `rhoPi_eq`, `chi_eq`
- Goal before: `Specs.Keccak.theta 64 A = thetaXorSpec A (thetaDSpec (thetaCSpec A))` (both `Vector ℕ 25`).
- Idiom (verbatim, three times):
  ```lean
  set_option maxRecDepth 4000 in
  lemma theta_eq (A : Vector ℕ 25) : ... := by
    apply Vector.ext
    intro i hi
    interval_cases i <;>
      simp [Specs.Keccak.theta, Specs.Keccak.ofLanes, Specs.Keccak.lane, thetaXorSpec, thetaDSpec, thetaCSpec]
  ```
- Why it closes: brute-force all 25 lane indices; each becomes a closed `Nat` xor identity that `simp` finishes. Requires `set_option maxRecDepth 4000`.

### S6. **Top-level 24-round soundness by induction on the fold accumulator**
- Where: `PermutationSound.lean:8-39` (whole file). See §5.

### S7. **Serialization-boundary soundness (`toLanes`/`fromLanes` sandwich)**
- Where: `Main.lean:24-46`
- Goal before: `Spec` in `fieldElemsToNat`/`Specs.Keccak.keccakF1600` terms.
- Idiom (verbatim):
  ```lean
  circuit_proof_start [Permutation.circuit, Permutation.Assumptions, Permutation.Spec]
  have h_bits : ∀ i : Fin 1600, (input_state[i.val] : F circomPrime).val < 2 := by
    intro i; have := h_assumptions i; simpa [fieldElemsToNat, Vector.getElem_map] using this
  have init_norm : StateNormalized (Vector.map (Vector.map (Expression.eval env)) (toLanes input_var_state)) := by
    rw [eval_toLanes_vec, h_input]; exact StateNormalized_toLanes input_state fun i => h_bits i
  have init_val : stateValue (...) = Specs.Keccak.bitsToState (fieldElemsToNat input_state) := by
    rw [eval_toLanes_vec, h_input, stateValue_toLanes]; rfl
  rw [eval_keccakState, eval_keccakState] at h_holds
  obtain ⟨out_norm, out_val⟩ := h_holds init_norm
  rw [init_val] at out_val
  show fieldElemsToNat _ = Specs.Keccak.keccakF1600 (fieldElemsToNat input_state)
  unfold Specs.Keccak.keccakF1600
  show Vector.map ZMod.val (Vector.map (Expression.eval env) (fromLanes _)) = _
  rw [eval_fromLanes_vec, fieldElems_fromLanes _ out_norm, out_val]
  ```
- Note the two `show` steps used as **definitional re-typings** instead of `simp`, to avoid unfolding `fieldElemsToNat` into an unmanageable form.

### S8. **K12 flat-row soundness via a custom `forAllNoOffset` characterization**
- Where: `KangarooTwelveGF2/Round.lean:55-89`
- Goal before: `Soundness (F p2) (main r) Assumptions (Spec r)`.
- Idiom:
  ```lean
  circuit_proof_start_core                                   -- NOTE: _core, not the full tactic
  simp only [ConstraintsHold.Soundness, forAllNoOffset_main] at h_holds
  obtain ⟨-, h_rows⟩ := h_holds
  simp only [circuit_norm] at h_input
  refine ⟨?_, ?_⟩
  ```
  then per-row extraction with `linear_combination`:
  ```lean
  have hrow := h_rows ⟨i, hi⟩
  simp only [circuit_norm] at hrow
  rw [← hinput, ← eval_preChi env input_var, ← eval_chiProduct env (preChi input_var) ⟨i, hi⟩]
  change env.get (i₀ + i) = Expression.eval env (chiProduct (preChi input_var) ⟨i, hi⟩)
  linear_combination hrow
  ```
  and a **`calc` chain** to reach the trusted spec (`Round.lean:77-87`):
  ```lean
  calc Vector.map (Expression.eval env) (roundOut r (preChi input_var) (...))
      = roundOut r (Vector.map (Expression.eval env) (preChi input_var)) (...) := eval_roundOut env r _ _
    _ = roundOut r (preChi input) (chiProducts (preChi input)) := by rw [eval_preChi, hinput, hproducts]
    _ = Specs.KangarooTwelve.round r input := roundOut_products r input
  ```
- Second bullet of the `refine` is the **channel/requirements obligation**: `simp only [Operations.Requirements, forAllNoOffset_main]; exact ⟨trivial, fun _ => trivial⟩` (`Round.lean:88-89`).
- Why `linear_combination` works and `sub_eq_zero` isn't needed: over `F 2` the row `products[i] - chiProduct = 0` is a linear identity in the target equality.

### S9. **Straight-line 12-round soundness by hypothesis rewriting**
- Where: `KangarooTwelveGF2/Main.lean:33-48`
- Idiom (verbatim):
  ```lean
  circuit_proof_start [main, Spec, Round.circuit, Round.Assumptions, Round.Spec]
  obtain ⟨h0, h1, h2, ..., h11⟩ := h_holds
  simp only [Specs.KangarooTwelve.keccakP1600_12]
  rw [h0] at h1
  rw [h1] at h2
  ... (11 rewrites) ...
  exact h11
  ```
- Why it closes: `Spec r input output := output = round r input` is an *equation*, so `rw [hk] at h(k+1)` telescopes the 12 rounds into a single nested `round 11 (round 10 (... input))`, which is definitionally `keccakP1600_12`. **Contrast with KeccakF1600's induction** — K12 unrolls because its Spec has no `Normalized` side-condition and 12 (not 24) rounds are affordable.

---

## 4. COMPLETENESS — pattern catalog

Completeness goals after `circuit_proof_start` have `h_env : env.UsesLocalWitnesses...` and the goal is the sub-circuits' `Assumptions` (plus witness-consistency rows for leaf gadgets).

### C1. **Leaf gadget: witness-value ⇒ row holds**
- Where: `XorLane.lean:82-99`, `AndLane.lean:74-79`
- AndLane is the minimal form (3 tactic lines, `AndLane.lean:76-79`):
  ```lean
  intro i
  have := h_env i
  simp only [Vector.getElem_ofFn] at this
  rw [this]; ring
  ```
- XorLane needs a **cast lemma** because the witness is computed in ℕ (`XorLane.lean:94-99`):
  ```lean
  have hcast : ((input_a[i].val ^^^ input_b[i].val : ℕ) : F p) = input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i] := by
    rw [← IsBool.xor_eq_val_xor (ha i) (hb i)]
    have := ZMod.natCast_val (R := ZMod p) (input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i])
    rw [this]; exact ZMod.cast_id p _
  rw [henv, hcast, h_ai i, h_bi i]; ring
  ```
- Why it closes: `ring` after substituting the witness definition; the whole content is the ℕ→`F p` cast round-trip (`ZMod.natCast_val` + `ZMod.cast_id`).

### C2. **Composition: discharge each sub-circuit's `Assumptions` from the previous one's `Normalized`**
- Where: `Xor5Lane.lean:49-57`, `ChiLane.lean:45-55`, `Theta.lean:38-45`
- Idiom (`Xor5Lane.lean:50-57`):
  ```lean
  circuit_proof_start [XorLane.circuit]
  simp only [XorLane.Assumptions, XorLane.Spec, and_imp] at h_env ⊢
  obtain ⟨ha, hb, hc, hd, he⟩ := h_assumptions
  obtain ⟨c1, c2, c3, _⟩ := h_env          -- last component dropped: nothing follows it
  obtain ⟨_, n1⟩ := c1 ha hb               -- keep only the *normalization* halves
  obtain ⟨_, n2⟩ := c2 n1 hc
  obtain ⟨_, n3⟩ := c3 n2 hd
  exact ⟨⟨ha, hb⟩, ⟨n1, hc⟩, ⟨n2, hd⟩, n3, he⟩
  ```
- **Signature: the value halves are discarded (`⟨_, n1⟩`) — only `Normalized` propagates.** Same at `Theta.lean:42-45` (`exact ⟨h_assumptions, c_norm, h_assumptions, d_norm⟩`).

### C3. **Loop gadget completeness = per-index precondition supply**
- Where: `ThetaC.lean:53-65`, `ThetaD.lean:53-67`, `ThetaXor.lean:55-69`, `Chi.lean:47-57`
- Idiom: same `hb` transport lemma as S3 but with `env.toEnvironment`, then
  ```lean
  intro x
  rw [hb _ (by omega), ...]
  exact ⟨h_assumptions ⟨x.val, by omega⟩, ...⟩
  ```
  ThetaD adds `hrot_norm := Normalized_eval_rotl env.toEnvironment _ input[...] (hb _ (by omega)) (h_assumptions ⟨...⟩) 1` (`ThetaD.lean:62-65`), Chi supplies three `h_assumptions j / (chiSource1 j) / (chiSource2 j)`.

### C4. **Round completeness = only the wiring commutation**
- Where: `KeccakRound.lean:43-49`, whole body:
  ```lean
  obtain ⟨h_theta, h_chi⟩ := h_env
  obtain ⟨theta_norm, _⟩ := h_theta h_assumptions
  rw [eval_keccakState, eval_rhoPiWire_vec, ← eval_keccakState] at h_chi ⊢
  exact ⟨h_assumptions, StateNormalized_rhoPiWire _ theta_norm⟩
  ```
  Note `at h_chi ⊢` — the same sandwich applied to hypothesis and goal simultaneously.

### C5. **Top-level completeness (`ProverSpec := True`) reduces to input normalization**
- Where: `Main.lean:48-61` — after establishing `init_norm`, the whole proof is `rw [eval_keccakState]; exact init_norm`.
- K12 version is **two lines** (`KangarooTwelveGF2/Main.lean:50-53`):
  ```lean
  circuit_proof_start
  simp only [Round.circuit, Round.Assumptions, and_self]
  ```
  because `Round.Assumptions := True` (`Round.lean:49`).

### C6. **K12 round completeness via `bind_usesLocalWitnesses` destructuring**
- Where: `KangarooTwelveGF2/Round.lean:91-103`
  ```lean
  circuit_proof_start_core
  unfold main at h_env
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env
  obtain ⟨h_wit, -⟩ := h_env
  simp only [circuit_norm] at h_wit
  simp only [ConstraintsHold.Completeness, forAllNoOffset_main]
  refine ⟨trivial, fun i => ?_⟩
  have henv := h_wit i
  simp only [circuit_norm, Vector.getElem_ofFn] at henv ⊢
  rw [henv]; ring
  ```

### C7. **Permutation completeness = induction supplying `StateNormalized` only**
- `PermutationComplete.lean:13-25`. See §5.

---

## 5. The 24-round permutation: structure and derivation

### 5.1 Round function composition
`Solution/KeccakF1600/KeccakRound.lean:12-16`
```lean
def main (rc : ℕ) (state : Var KeccakBitState (F p)) : Circuit (F p) (Var KeccakBitState (F p)) := do
  let state ← Theta.circuit state
  let state ← Chi.circuit (rhoPiWire state)     -- ρ,π applied as *wiring on the variable*, no subcircuit
  return iotaWire rc state                       -- ι as wiring on the output, no subcircuit
```
Only 2 subcircuits per round. Costs: `Theta = 3200` (`Cost.lean:122-126` = 1280+320+1600), `Chi = 3200` (`Cost.lean:132-134` = 25×128), total `6400` per round.

### 5.2 Fold construction (`PermutationDefs.lean`)
```lean
lemma keccakRound_localLength (c hc s n) : (KeccakRound.circuit c hc s).localLength n = 6400 := by
  simp only [circuit_norm, KeccakRound.circuit, KeccakRound.elaborated]              -- :16-19
def rcN (i : ℕ) : ℕ := if h : i < 24 then rc ⟨i, h⟩ else 0                            -- :22  (total-ize the round constant)
lemma rcN_eq (i : Fin 24) : rcN i.val = rc i := by rw [rcN, dif_pos i.isLt]           -- :24
def body (state) (i : Fin 24) := KeccakRound.circuit (rc i) (rc_lt i) state           -- :28-30
def foldConstant : Circuit.ConstantLength (fun t => body t.1 t.2) :=
  Circuit.ConstantLength.fromConstantLength' _ (fun acc i i' n => by
    rw [body, body, keccakRound_localLength, keccakRound_localLength])                -- :34-37
def main (state) := Circuit.foldlRange 24 state body foldConstant                     -- :40-42
```
**Critical comment at `PermutationDefs.lean:32-33`:** the `ConstantLength` instance is supplied *explicitly* because the default `by infer_constant_length` would try to reduce a round's length through a symbolic `rc i`.

### 5.3 The symbolic-state calculus (the core enabler)
```lean
def stateVar (n i : ℕ) : Var KeccakBitState (F circomPrime) :=
  iotaWire (rcN i)
    (Vector.mapFinRange 25 fun j => Vector.mapRange 64 fun z =>
      Expression.var ⟨n + i * 6400 + 3200 + j.val * 128 + 64 + z⟩)                    -- :46-49
abbrev acc (n init) (k : Fin 24) := Circuit.FoldlM.foldlAcc n (Vector.finRange 24) body init k  -- :52-54
lemma body_output (init n) (k : Fin 24) : (body (acc n init k) k).output (n + k.val * 6400) = stateVar n k.val := by
  simp only [body, stateVar, circuit_norm, KeccakRound.circuit, KeccakRound.elaborated]
  congr 1; exact (rcN_eq k).symm                                                      -- :57-61
lemma foldAcc_succ ... := by
  show Circuit.FoldlM.foldlAcc n (Vector.finRange 24) body init ⟨k+1, hk⟩ = _
  simp only [Circuit.FoldlM.foldlAcc, Fin.foldl_succ_last, Fin.val_last, Vector.getElem_finRange,
             Fin.val_castSucc, body, keccakRound_localLength]                         -- :64-69
lemma acc_succ (init n k hk) : acc n init ⟨k+1, hk⟩ = stateVar n k := by
  rw [foldAcc_succ init n k hk, body_output init n ⟨k, by omega⟩]                     -- :71-73
lemma acc_zero : acc n init ⟨0, h⟩ = init := Circuit.FoldlM.foldlAcc_zero             -- :75-77
```
The address arithmetic `n + i*6400 + 3200 + j*128 + 64 + z` encodes: round base + θ's 3200 + lane `j`'s ChiLane block (128 wide) + the XorLane half (offset 64) — i.e. **the χ output witnesses**, with ι applied as free wiring on top.

`elaborated` must be given by hand with the output supplied (`PermutationDefs.lean:84-95`):
```lean
instance elaborated : ElaboratedCircuit ... main := by
  elaborate_circuit_with { output _ i0 := stateVar i0 23 } using by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a; simp only [circuit_norm]
    · intro a n
      simp only [Fin.foldl_succ_last, circuit_norm, stateVar, Fin.val_last, Vector.mapRange_eq_mapFinRange]
      congr 1
    · simp only [circuit_norm]
    · simp only [circuit_norm]
```

### 5.4 The ℕ-side fold, mirroring the circuit fold
```lean
def vfold (X : Vector ℕ 25) (k : ℕ) : Vector ℕ 25 :=
  Fin.foldl k (fun A (j : Fin k) => Specs.Keccak.keccakRound 64 (rcN j.val) A) X       -- :98-99
lemma vfold_succ : vfold X (k+1) = keccakRound 64 (rcN k) (vfold X k) := by
  rw [vfold, Fin.foldl_succ_last]; simp only [Fin.val_last, Fin.val_castSucc, vfold]   -- :101-104
lemma vfold_24 : vfold X 24 = Specs.Keccak.keccakF 6 X := by
  rw [keccakF6_eq_rounds, vfold]; simp only [Fin.foldl_succ, Fin.foldl_zero, Fin.isValue]; rfl  -- :106-109
```
`keccakF6_eq_rounds` (`MainTheorems.lean:27-44`) is the **24× fully-unrolled** statement of the trusted `keccakF 6`, proved by
```lean
show Fin.foldl 24 (fun A i => Specs.Keccak.keccakRound 64 (rc i) A) A = _
simp only [Fin.foldl_succ, Fin.foldl_zero]
rfl
```
with `set_option maxRecDepth 4000 in`.

### 5.5 **Answer: soundness of the full permutation is INDUCTION on `k` over the fold accumulator, not an iterate lemma.**
`PermutationSound.lean:8-39`:
```lean
set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [KeccakRound.circuit, KeccakRound.Assumptions, KeccakRound.Spec]
  simp only [body, KeccakRound.circuit, circuit_norm, KeccakRound.Assumptions, KeccakRound.Spec] at h_holds ⊢
  have key : ∀ (k : ℕ) (hk : k < 24),
      StateNormalized (eval env (acc i₀ input_var ⟨k, hk⟩)) ∧
      stateValue (eval env (acc i₀ input_var ⟨k, hk⟩)) = vfold (stateValue input) k := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [acc_zero, h_input]
      exact ⟨h_assumptions, by simp only [vfold, Fin.foldl_zero]⟩
    | succ k ih =>
      intro hk
      have hk1 : k < 24 := by omega
      obtain ⟨nk, vk⟩ := ih hk1
      have hh := h_holds ⟨k, hk1⟩ nk
      rw [acc_succ input_var i₀ k hk, stateVar, show rcN k = rc ⟨k, hk1⟩ from rcN_eq ⟨k, hk1⟩] at *
      refine ⟨hh.1, ?_⟩
      rw [hh.2, vk, vfold_succ, show rcN k = rc ⟨k, hk1⟩ from rcN_eq ⟨k, hk1⟩]
  obtain ⟨n23, v23⟩ := key 23 (by norm_num)
  have hh := h_holds ⟨23, by norm_num⟩ n23
  have h24 : vfold (stateValue input) 24 = Specs.Keccak.keccakRound 64 (rcN 23) (vfold (stateValue input) 23) :=
    vfold_succ (stateValue input) 23
  refine ⟨hh.1, Eq.trans hh.2 ?_⟩
  rw [v23, ← vfold_24 (stateValue input), h24]
  congr 1
```
Notable micro-idioms:
- **`intro k; induction k with` (introducing the bound `hk` *inside* each branch)** — the induction is on the raw ℕ with the `< 24` proof introduced afterwards, so the IH is usable at `k` with a fresh `by omega` bound.
- `rw [...] at *` with an inline `show rcN k = rc ⟨k, hk1⟩ from rcN_eq ⟨k, hk1⟩` term.
- The **off-by-one tail**: `key` only covers accumulators *entering* rounds 0..23, so the output (round 23's result) is obtained by one extra `h_holds ⟨23, _⟩ n23` application, then `vfold_succ ... 23` + `vfold_24`, closed by `congr 1`.
- `set_option maxHeartbeats 4000000 in` is required.

`PermutationComplete.lean:8-25` is the same induction with the value component deleted:
```lean
have key : ∀ (k : ℕ) (hk : k < 24), StateNormalized (eval env.toEnvironment (acc i₀ input_var ⟨k, hk⟩)) := by
  intro k
  induction k with
  | zero => intro hk; rw [acc_zero, h_input]; exact h_assumptions
  | succ k ih => intro hk; have hk1 : k < 24 := by omega
                 rw [acc_succ input_var i₀ k hk, stateVar, show rcN k = rc ⟨k, hk1⟩ from rcN_eq ⟨k, hk1⟩]
                 exact (h_env ⟨k, hk1⟩ (ih hk1)).1
intro i
exact key i.val i.isLt
```

### 5.6 Cost of the iterated composition — `CostIs.foldlRange`, **no induction**
`PermutationCost.lean:14-19`:
```lean
theorem costIs (state) : CostIs (main state) ⟨153600, 153600⟩ := by
  have h : CostIs (main state) ⟨24 * 6400, 24 * 6400⟩ :=
    CostIs.foldlRange (constant := foldConstant) (fun s i n => costIs_sub_round (rc i) (rc_lt i) s n)
  exact h
```
- Why it closes: `CostIs.foldlRange` (`Challenge/Utils/CostR1CS.lean:391-398`) says `CostIs (foldlRange m init body constant) ⟨m*K.allocations, m*K.constraints⟩` given a per-body offset-independent count. The `have h : ... ⟨24*6400, ...⟩ ... exact h` step is a **deliberate defeq launder** so `24*6400` reduces to `153600` at `exact`-time rather than in the unifier.

R1CS of the fold uses the **invariant-threading** variant (`PermutationCost.lean:22-26`):
```lean
theorem r1cs (state) (hs : StateAffine state) : IsR1CSCirc (main state) :=
  IsR1CSCirc.foldlRange_inv (constant := foldConstant) StateAffine hs
    (fun s i hsa => r1cs_sub_round (rc i) (rc_lt i) s hsa)
    (fun s i n _ => stateAffine_subOut_round (rc i) (rc_lt i) s n)
```
`IsR1CSCirc.foldlRange_inv` (`CostR1CS.lean:519-537`) takes `P : β → Prop`, `hinit`, `hbody : ∀ s i, P s → IsR1CSCirc (body s i)`, `hstep : ∀ s i n, P s → P ((body s i).output n)` — here `P := StateAffine`. This is *the* pattern for cost/R1CS of an iterated circuit: **cost is compositional (no invariant), R1CS needs an affineness invariant on the accumulator.**

Whole file preamble that makes it tractable (`PermutationCost.lean:9-11`, mirrored at `Cost.lean:153` and `Main.lean:146`):
```lean
set_option maxHeartbeats 4000000
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS
```
Comment at `Cost.lean:150-152` explains why: "otherwise the unifier evaluates `r1csProducts` on the 64-bit asserted expressions and loops."

---

## 6. The Permutation* split and top-level glue

| File | Contains | Lines |
|---|---|---|
| `PermutationDefs.lean` | `keccakRound_localLength`, `rcN`, `rcN_eq`, `body`, `foldConstant`, `main`, `stateVar`, `acc`, `body_output`, `foldAcc_succ`, `acc_succ`, `acc_zero`, `Assumptions`, `Spec`, `elaborated` (via `elaborate_circuit_with`), `vfold`, `vfold_succ`, `vfold_24` | 111 |
| `PermutationSound.lean` | **only** `theorem soundness`, `maxHeartbeats 4000000` | 41 |
| `PermutationComplete.lean` | **only** `theorem completeness`, `maxHeartbeats 4000000` | 27 |
| `Permutation.lean` | `def circuit : FormalCircuit`, `body_eq_subcircuit`, `eval_stateVar_of_agreesBelow`, `theorem computableWitnesses`; imports Defs+Sound+Complete; `maxHeartbeats 1000000` | 80 |
| `PermutationCost.lean` | `theorem costIs`, `theorem r1cs`; imports `Permutation` + `Solution.KeccakF1600.Cost` | 28 |

The split's purpose is **elaboration-budget isolation**: each of the two 4M-heartbeat proofs lives alone in its own file, and `Permutation.lean` (the assembly point) runs at 1M.

**The `FormalCircuit` assembly carries a documented workaround** (`Permutation.lean:12-22`):
```lean
def circuit : FormalCircuit (F circomPrime) KeccakBitState KeccakBitState where
  main := main; elaborated := elaborated; Assumptions := Assumptions; Spec := Spec
  -- `soundness := soundness` / `completeness := completeness` trigger a `whnf`
  -- timeout while checking the term against the structure's `base.main`
  -- projection (the same quirk noted in clean's own Keccak Permutation); routing
  -- through `simp only` matches the goal syntactically and sidesteps it.
  soundness := by simp only [soundness]
  completeness := by simp only [completeness]
```
**This is a high-value, reusable trick: `field := by simp only [thm]` instead of `field := thm` when structure-field defeq checking times out.**

### Top-level glue in `Main.lean` (KeccakF1600)
```lean
def main (input) := do let state ← Permutation.circuit (toLanes input.state); return { state := fromLanes state }  -- :17-19
theorem costIs_sub_permutation (b) : CostIs (subcircuit Permutation.circuit b) ⟨153600,153600⟩ :=
  CostIs.subcircuit (fun n => Permutation.costIs b n)                                                              -- :151-153
theorem mainCost : circuitCost main ⟨allocations, constraints⟩ :=
  fun input => (CostIs.bind (costIs_sub_permutation _) fun _ => CostIs.pure _
                : CostIs (main input) ⟨allocations, constraints⟩)                                                  -- :155-159
theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput => by ... IsR1CSCirc.bind_out (r1cs_sub_permutation _ h0) fun _ => IsR1CSCirc.pure _)
    (fun input hinput => by ... exact affine_fromLanes (stateAffine_subOut_permutation _ _) i hi1600)               -- :175-191
```
- **`mainCost` idiom**: `fun input => (<CostIs term> : CostIs (main input) ⟨allocations, constraints⟩)` — the type ascription forces the `Count` addition `⟨153600,153600⟩ + ⟨0,0⟩` to reduce against the reducible `allocations`/`constraints`.
- `isR1CS` is a **pair** of obligations: (a) all rows R1CS for affine input, (b) all *outputs* affine. `isR1CS_of_IsR1CSCirc` at `CostR1CS.lean:742`.
- Input-affineness extraction idiom (`Main.lean:180-183`):
  ```lean
  have hsz : size Input = 1600 := rfl
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by omega)
  ```
  (K12 twin at `Cost.lean:154-159` and `Main.lean:299-303`.)

---

## 7. COMPUTABLEWITNESS — pattern catalog

### CW0. **Universal gadget-level preamble** (verbatim in 9 files)
`XorLane.lean:104-110`, `AndLane.lean:84-90`, `Xor5Lane.lean:64-70`, `ChiLane.lean:60-66`, `ThetaC.lean:77-83`, `ThetaD.lean:77-83`, `ThetaXor.lean:81-87`, `Theta.lean:103-109`, `Chi.lean:67-73`, `KeccakRound.lean:91-98`, `Permutation.lean:52-58`, `KangarooTwelveGF2/Round.lean:121-127`:
```lean
theorem computableWitnesses : (circuit (p := p)).ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
```
The `change ...` is essential: it re-types the goal into the *structural* form for which the `_iff` rewrite lemmas exist.

### CW1. **Leaf: `simp only` with the five structural `_iff` lemmas, then `and_intros`**
- Where: `XorLane.lean:112-135`, `AndLane.lean:92-115`
- Idiom:
  ```lean
  simp only [
    ...Circuit.bind_structuralComputableWitnesses_iff,
    ...Circuit.witnessVector_structuralComputableWitnesses_iff,
    ...Circuit.forEach_structuralComputableWitnesses_iff,
    ...Circuit.assertZero_structuralComputableWitnesses_iff,
    ...Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    simp [circuit_norm] at h_input
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_ofFn]
    have ha : Expression.eval env.toEnvironment input.a[i] = Expression.eval env'.toEnvironment input.a[i] := h_input.1 _ (by simp)
    have hb : ... := h_input.2 _ (by simp)
    simp [ha, hb]
  · intro _; trivial
  ```
- Why it closes: the only real content is that the witness *computation function* depends on the input only through evaluations of `input.a`/`input.b`, so equal-input-evaluations ⇒ equal witnesses.

### CW2. **Sequential composition: `let`-bound offsets + `subcircuit_flatStructuralComputableWitnesses(_of_condition)`**
- Where: `Xor5Lane.lean:71-133` (4 rounds), `ChiLane.lean:67-102`, `Theta.lean:110-158`, `KeccakRound.lean:99-134`, `Main.lean:70-94`, `KangarooTwelveGF2/Main.lean:90-211` (12 rounds)
- Idiom (Xor5Lane, the template):
  ```lean
  let firstInput : Var XorLane.Inputs (F p) := ⟨input.a, input.b⟩
  let first : Circuit (F p) (Var (fields 64) (F p)) := XorLane.circuit firstInput
  let n1 := offset + first.localLength offset
  let t1 := first.output offset
  ... (repeat for second/third) ...
  have hlen1 : first.localLength offset = 64 := by simp [first, firstInput, XorLane.circuit, circuit_norm]
  have hn1 : n1 = offset + 64 := by simp only [n1, hlen1]
  simp only [...bind_structuralComputableWitnesses_iff, ...FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  and_intros
  · exact ...subcircuit_flatStructuralComputableWitnesses XorLane.circuit input ⟨input.a, input.b⟩ offset
      (by intro env env' h_input; simp [circuit_norm] at h_input ⊢; exact ⟨h_input.1, h_input.2.1⟩)
      XorLane.computableWitnesses env env'
  · exact ...subcircuit_flatStructuralComputableWitnesses_of_condition XorLane.circuit input ⟨t1, input.c⟩ n1
      (by intro k env env' hle h_agree h_input
          simp [circuit_norm] at h_input ⊢
          refine ⟨?_, ?_⟩
          · exact ...eval_mem_varFromOffset_fields_of_agreesBelow h_agree (by omega)
          · exact h_input.2.2.1)
      XorLane.computableWitnesses env env'
  ```
- **The two-variant rule:** use `subcircuit_flatStructuralComputableWitnesses` when the sub-input is a pure function of the parent input (first subcircuit); use `..._of_condition` when the sub-input contains *previously witnessed variables* — then you additionally get `h_agree : env.AgreesBelow k env'` and `hle : n ≤ k` to prove those variables agree.
- The leaf tool for "these are fresh witness vars below `k`": `Challenge.Utils.ComputableWitnessLemmas.eval_mem_varFromOffset_fields_of_agreesBelow h_agree (by omega)` (`ComputableWitnessLemmas.lean:54-66`).

### CW3. **`attribute [local irreducible] main` before the CW proof**
- Where: `Xor5Lane.lean:62`, `ThetaC.lean:75`, `ThetaXor.lean:79` (`main XorLane.circuit`), `Theta.lean:101`, `KeccakRound.lean:89`, `Permutation.lean:50`, `Main.lean:63` (`attribute [local irreducible] Permutation.circuit in`).
- Purpose: prevent `simp`/unifier from unfolding the whole nested circuit while the structural rewrites fire.

### CW4. **`mapFinRange` loops: `intro x` then one `refine ... subcircuit_flat...` + a `hword`/`hmem` pair**
- Where: `ThetaC.lean:85-112`, `ThetaD.lean:85-116`, `ThetaXor.lean:89-121`, `Chi.lean:75-109`
- Idiom (`ThetaC.lean:85-112`):
  ```lean
  simp only [...Circuit.mapFinRange_structuralComputableWitnesses_iff,
             ...FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
  intro x
  refine ...subcircuit_flatStructuralComputableWitnesses Xor5Lane.circuit input
    ⟨input[x.val], input[x.val+5], ..., input[x.val+20]⟩ _ ?_ Xor5Lane.computableWitnesses env env'
  intro e1 e2 h_input
  simp [circuit_norm] at h_input ⊢
  have hword : ∀ (j : ℕ) (hj : j < 25),
      Vector.map (Expression.eval e1.toEnvironment) (input[j]'hj) = Vector.map (Expression.eval e2.toEnvironment) (input[j]'hj) := by
    intro j hj
    rw [← CircuitType.eval_var_fields e1.toEnvironment (input[j]'hj), ← CircuitType.eval_var_fields e2.toEnvironment (input[j]'hj),
        getElem_eval_vector e1.toEnvironment input j hj, getElem_eval_vector e2.toEnvironment input j hj]
    exact congrArg (fun v : KeccakBitState (F p) => v[j]'hj) h_input
  have hmem : ∀ (j : ℕ) (hj : j < 25), ∀ a ∈ (input[j]'hj), Expression.eval e1.toEnvironment a = Expression.eval e2.toEnvironment a := by
    intro j hj a ha
    simp only [Vector.mem_iff_getElem] at ha
    rcases ha with ⟨b, hb, hget⟩
    rw [← hget]
    simpa [Vector.getElem_map] using Vector.ext_iff.mp (hword j hj) b hb
  exact ⟨hmem _ (by omega), hmem _ (by omega), hmem _ (by omega), hmem _ (by omega), hmem _ (by omega)⟩
  ```
- The `hword` → `hmem` two-step (**lane equality ⇒ membership-wise bit equality**) is the recurring bridge, appearing 4× in KeccakF1600 with the same body.
- ThetaD's second argument is `rotl 1 c[...]`, handled by additionally rewriting through the rotation index (`ThetaD.lean:112-115`):
  ```lean
  rw [← hget, rotl, Vector.getElem_rotate hb]
  simpa [Vector.getElem_map] using Vector.ext_iff.mp (hword ((↑x + 1) % 5) (by omega)) ((b + (64 - 1 % 64)) % 64) (Nat.mod_lt _ (by norm_num))
  ```
- ChiLane's first argument is `notBits input.b`, handled by (`ChiLane.lean:82-87`):
  ```lean
  intro a ha
  simp only [firstInput, notBits, Vector.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have heq := h_input.2.1 b hb
  simp [Expression.eval, heq]
  ```

### CW5. **The `*_of_agreesBelow` family — reified symbolic outputs**
Three near-identical lemmas, differing only in shape:

| Lemma | Where | Shape |
|---|---|---|
| `eval_varFromOffset_of_agreesBelow` | `Theta.lean:59-69` | generic `ProvableType α`, `env.AgreesBelow (n + size α) env'` |
| `eval_row_of_agreesBelow` | `Theta.lean:75-99` | `Var KeccakBitRow` assembled from 5 `varFromOffset (fields 64) (base i)` |
| `eval_state_of_agreesBelow` | `KeccakRound.lean:63-87` | 25-lane analogue |
| `eval_stateVar_of_agreesBelow` | `Permutation.lean:32-48` | the ι-wired `stateVar n i`, bound `n + i*6400 + 6400 ≤ k` |
| `Round.eval_subOut_of_agreesBelow` | `KangarooTwelveGF2/Round.lean:165-186` | K12 round output, bound `n + 1600 ≤ k` |

Common body skeleton (`Theta.lean:81-99`):
```lean
simp only [CircuitType.eval_var_prover_to_verifier]
rw [hv]
apply Vector.ext; intro i hi
rw [← getElem_eval_vector env.toEnvironment (...) i hi, ← getElem_eval_vector env'.toEnvironment (...) i hi, Vector.getElem_mapFinRange]
apply Vector.ext; intro j hj
rw [← ProvableType.getElem_eval_fields env.toEnvironment (varFromOffset (fields 64) (base ⟨i, hi⟩)) j hj, ...,
    ProvableType.varFromOffset_fields, Vector.getElem_mapRange]
simp only [Expression.eval]
exact h (base ⟨i, hi⟩ + j) (by have := hbound ⟨i, hi⟩; omega)
```
`eval_stateVar_of_agreesBelow` is shorter because `stateVar` is a `mapFinRange`/`mapRange` of raw vars (`Permutation.lean:41-48`), ending in `exact h (n + i*6400 + 3200 + j*128 + 64 + z) (by omega)`.

### CW6. **The permutation's CW: `foldlRange_structuralComputableWitnesses_iff` + case-split on `acc`**
`Permutation.lean:59-78`:
```lean
unfold main
simp only [...Circuit.foldlRange_structuralComputableWitnesses_iff]
intro i
rw [show (body default i).localLength = 6400 from keccakRound_localLength (rc i) (rc_lt i) default 0,
  body_eq_subcircuit (acc offset input i) i,
  ...FormalCircuit.subcircuit_structuralComputableWitnesses_iff]
exact ...subcircuit_flatStructuralComputableWitnesses_of_condition
  (KeccakRound.circuit (rc i) (rc_lt i)) input (acc offset input i) (offset + i.val * 6400)
  (by intro kk e e' hle h_agree h_input
      obtain ⟨_ | k', hiv⟩ := i                          -- split Fin 24 into 0 vs succ
      · rw [acc_zero input offset hiv]; exact h_input
      · rw [acc_succ input offset k' hiv]
        exact eval_stateVar_of_agreesBelow offset k'
          (by rw [show (⟨k'+1, hiv⟩ : Fin 24).val = k'+1 from rfl] at hle; omega) h_agree)
  (KeccakRound.computableWitnesses (rc i) (rc_lt i)) env env'
```
Enablers: `body_eq_subcircuit : body s i = subcircuit (KeccakRound.circuit (rc i) (rc_lt i)) s := rfl` (`Permutation.lean:26-27`, marked `private`) — "exposing the `subcircuit` head lets the structural-computable-witnesses rewrites fire".

### CW7. **Top-level `computableWitness`: the flat `Condition.implies` induction** (identical in both challenges)
`Main.lean:64-132` and `KangarooTwelveGF2/Main.lean:81-247`. After building `hstruct`, the two proofs share this **verbatim boilerplate**:
```lean
have hflat := ...FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses input env env' hstruct
unfold ...FormalCircuitBase.computableWitnessCondition at hflat
rw [← Operations.forAll_toFlat_iff] at hflat ⊢
let targetCondition : Condition (F _) := { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
apply FlatOperation.forAll_implies (F := F _) n ?_ hflat
have himplies : ∀ (ops : List (FlatOperation (F _))) (off : ℕ), n ≤ off →
    FlatOperation.forAll off (Condition.implies (...computableWitnessCondition input env env') targetCondition).ignoreSubcircuit ops := by
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
    | assert e => simp only [...]; exact ⟨by intro _; trivial, ih off hoff⟩
    | lookup l => simp only [...]; exact ⟨by intro _; trivial, ih off hoff⟩
    | interact i => simp only [...]; exact ⟨by intro _; trivial, ih off hoff⟩
exact himplies ((main input).operations n).toFlat n (le_refl n)
```
This is **~35 lines of copy-paste boilerplate that converts the parent-input-relative condition into the absolute `OnlyAccessedBelow`-based one demanded by the challenge statement.** It is the single most mechanically reusable block in the whole corpus.

K12 avoids it at the *round* level via a one-liner (`KangarooTwelveGF2/Round.lean:152-157`):
```lean
theorem computableWitness (r) : ∀ n input, ProverEnvironment.OnlyAccessedBelow n (fun env => eval env input) →
    Circuit.ComputableWitnesses (main r input) n :=
  FormalCircuitBase.computableWitnesses_implies (circuit := (circuit r).base) (computableWitnesses r)
```
— i.e. `computableWitnesses_implies` (`ComputableWitnessLemmas.lean:376`) exists and does exactly the boilerplate, but only when the parent input *is* the circuit input. At `Main` level the input types differ (`Input` vs `fields n`), so the manual version is used.

---

## 8. MAINCOST — pattern catalog

### MC1. **Bottom-up `CostIs` certificate ladder** (`Solution/KeccakF1600/Cost.lean`)
Every gadget gets two theorems — one for `main`, one for `subcircuit`:
```lean
theorem costIs_xorLane (a b) : CostIs (XorLane.xorLane a b) ⟨64, 64⟩ :=
  CostIs.bind (CostIs.witnessVector 64 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z          -- :59-62
theorem costIs_sub_xorLane (b) : CostIs (subcircuit XorLane.circuit b) ⟨64,64⟩ :=
  CostIs.subcircuit (fun n => costIs_xorLane b.a b.b n)                                        -- :69-71
```
Full ladder with values:

| Theorem | Line | Count | Built from |
|---|---|---|---|
| `costIs_xorLane` / `costIs_andLane` | 59 / 64 | `⟨64,64⟩` | `bind`+`witnessVector`+`forEach`+`assertZero`+`pure` |
| `costIs_sub_xorLane` / `costIs_sub_andLane` | 69 / 73 | `⟨64,64⟩` | `CostIs.subcircuit` |
| `costIs_xor5Lane` | 77 | `⟨256,256⟩` | 4× `costIs_sub_xorLane` via nested `CostIs.bind` |
| `costIs_chiLane` | 88 | `⟨128,128⟩` | `bind (costIs_sub_andLane _) fun _ => costIs_sub_xorLane _` |
| `costIs_thetaC` | 96 | `⟨1280,1280⟩` | `CostIs.mapFinRange fun _ n => (costIs_sub_xor5Lane _ : CostIs _ ⟨256,256⟩) n` |
| `costIs_thetaD` | 100 | `⟨320,320⟩` | `CostIs.mapFinRange` × `⟨64,64⟩` |
| `costIs_thetaXor` | 104 | `⟨1600,1600⟩` | needs `obtain ⟨state, d⟩ := b; unfold ThetaXor.main` first (pattern-matching `main`) |
| `costIs_theta` | 122 | `⟨3200,3200⟩` | 3 binds |
| `costIs_chi` | 132 | `⟨3200,3200⟩` | `mapFinRange` × `⟨128,128⟩` |
| `costIs_round` | 140 | `⟨6400,6400⟩` | `bind theta, bind chi, pure` |
| `costIs_sub_round` | 146 | `⟨6400,6400⟩` | `CostIs.subcircuit` |
| `Permutation.costIs` | `PermutationCost.lean:14` | `⟨153600,153600⟩` | `CostIs.foldlRange` |
| `Main.costIs_sub_permutation` / `mainCost` | `Main.lean:151` / `:155` | `⟨153600,153600⟩` | `CostIs.subcircuit` then `bind`+`pure` |

- **Recurring type-ascription trick inside `mapFinRange`**: `fun _ n => (costIs_sub_xor5Lane _ : CostIs _ ⟨256, 256⟩) n` — the ascription pins `K` so `CostIs.mapFinRange`'s `⟨m*K.allocations, m*K.constraints⟩` computes.
- These are **all term-mode proofs**, no tactic blocks except `costIs_thetaXor` (needs the pattern-match destructuring).

### MC2. **K12 `costIs` with an explicit `Count` normalization**
`KangarooTwelveGF2/Cost.lean:13-23`:
```lean
theorem costIs_main (r) (s : StateVar) : CostIs (Round.main r s) ⟨1600, 1600⟩ := by
  unfold Round.main
  have hcount : (⟨1600, 0⟩ + (⟨1600 * 0, 1600 * 1⟩ + ⟨0, 0⟩) : Count) = ⟨1600, 1600⟩ := by
    show (⟨_, _⟩ : Count) = _
    congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector permutationBits _) fun products => ?_
  refine CostIs.bind (CostIs.forEach fun i n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.pure _
```
The `rw [← hcount]` **pre-normalizes the goal count into the exact un-summed shape the `bind` chain produces** — an alternative to KeccakF1600's type-ascription approach.

### MC3. **Top-level `mainCost` as an explicit 12-fold `bind` with a giant type ascription**
`KangarooTwelveGF2/Main.lean:55-75`:
```lean
theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := by
  intro input
  exact (CostIs.bind (Cost.costIs_sub _ _) fun _ => ... (12×) ... CostIs.pure _
    : CostIs (main input) (⟨1600,1600⟩ + (⟨1600,1600⟩ + (... + ⟨0,0⟩))))
```
The ascribed type is the *un-normalized* right-nested `Count` sum; defeq to `⟨19200,19200⟩` via `@[reducible] def allocations := 19200`.

---

## 9. isR1CS / isR1CS_Cidentity — pattern catalog

### R1. **Affineness predicates and their closure lemmas** (`Solution/KeccakF1600/Cost.lean`)
```lean
def StateAffine (s : Var KeccakBitState (F circomPrime)) : Prop := ∀ j (hj : j < 25), AffineW (s[j]'hj)   -- :16
def RowAffine  (s : Var KeccakBitRow   (F circomPrime)) : Prop := ∀ j (hj : j < 5),  AffineW (s[j]'hj)   -- :20
```
| Closure lemma | Line | Proof idiom |
|---|---|---|
| `affineW_rotl` | 23 | `intro i hi; show Affine ((x.rotate (64 - k % 64))[i]); rw [Vector.getElem_rotate]; exact hx _ (Nat.mod_lt _ (by norm_num))` |
| `affineW_notBits` | 30 | `show Affine ((x.map fun ai => 1 - ai)[i]); rw [Vector.getElem_map]; exact Affine.sub (Affine.const 1) (hx i hi)` |
| `affineW_xorConst` | 37 | `show Affine ((Vector.ofFn fun w => if c.testBit w.val then 1 - x[w] else x[w])[i]); rw [Vector.getElem_ofFn]; split; · Affine.sub ...; · hx i hi` |
| `stateAffine_rhoPiWire` | 46 | `rw [rhoPiWire_getElem s j hj]; exact affineW_rotl (hs _ (piSource ⟨j,hj⟩).isLt) _` |
| `stateAffine_toLanes` | 52 | `rw [toLanes_getElem bits j hj, Vector.getElem_ofFn]; exact h _ (by omega)` |
| `stateAffine_iotaWire` | 311 | `rw [show (iotaWire c s)[j] = xorConst (if j = 0 then c else 0) s[j] from by rw [iotaWire, Vector.getElem_mapFinRange]]; exact affineW_xorConst (hs j hj) _` |
| `affine_fromLanes` | 331 | `rw [fromLanes_getElem s i hi]; exact hs (i/64) (by omega) (i%64) (by omega)` |

**The `show ... ; rw [Vector.getElem_*] ; exact/split` shape appears in every one.** The `show` forces the definitional unfolding without `simp`.

### R2. **Sub-circuit output affineness by `rfl`-witnessed offset**
```lean
theorem affineW_subOut_xorLane (b) (n) : AffineW ((subcircuit XorLane.circuit b).output n) := by
  rw [show (subcircuit XorLane.circuit b).output n = varFromOffset (fields 64) n from rfl]
  exact affineW_varFromOffset 64 n                                                        -- Cost.lean:155-158
theorem affineW_subOut_xor5Lane ... = varFromOffset (fields 64) (n + 192) from rfl ...     -- :165-168 (offset 192 = 3×64)
theorem affineW_subOut_chiLane  ... = varFromOffset (fields 64) (n + 64)  from rfl ...     -- :170-173
```
For state-typed outputs, the `simp only [X.circuit, X.elaborated, circuit_norm]; exact Affine.var _` variant (`rowAffine_subOut_thetaC` :230, `rowAffine_subOut_thetaD` :237, `stateAffine_subOut_theta` :244, `stateAffine_subOut_chi` :303).

For a round (ι-wired): `stateAffine_subOut_round` (`Cost.lean:319-328`):
```lean
rw [show (subcircuit (KeccakRound.circuit c hc) b).output n = (KeccakRound.circuit c hc).output b n from rfl]
simp only [KeccakRound.circuit, KeccakRound.elaborated, circuit_norm]
apply stateAffine_iotaWire
intro j hj i hi
rw [Vector.getElem_mapFinRange, Vector.getElem_mapRange]
exact Affine.var _
```

### R3. **Per-row R1CS certificates from `isR1CSRow_*` builders**
```lean
theorem r1cs_xorLane (a b) (ha : AffineW a) (hb : AffineW b) : IsR1CSCirc (XorLane.xorLane a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 64 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_add_mul
            (Affine.sub (Affine.sub (affineW_witnessVector_output 64 _ n j.val j.isLt) (ha j.val j.isLt)) (hb j.val j.isLt))
            (Affine.fconst_mul _ (ha j.val j.isLt)) (hb j.val j.isLt)) m)
      (fun _ => IsR1CSCirc.pure _)                                                          -- Cost.lean:175-185
theorem r1cs_andLane ... isR1CSRow_sub_mul (affineW_witnessVector_output 64 _ n j.val j.isLt) (ha ...) (hb ...) -- :187-195
```
- `isR1CSRow_add_mul` matches `C + A*B`; `isR1CSRow_sub_mul` matches `C - A*B` (`CostR1CS.lean:691-712`).
- The XOR row `z - a - b + 2*a*b` is parsed as `C = ((z - a) - b)`, `A = 2*a` (hence `Affine.fconst_mul`), `B = b`.
- **`IsR1CSCirc.bind_out` (not `bind`) is used whenever the continuation needs the actual `varFromOffset` output** (`CostR1CS.lean:539-547`).

### R4. **Composite R1CS: thread affineness through `bind_out`**
```lean
theorem r1cs_xor5Lane (input) (ha hb hc hd he) : IsR1CSCirc (Xor5Lane.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_xorLane _ ha hb) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_xorLane _ (affineW_subOut_xorLane _ _) hc) fun _ =>
  ... (4 total)                                                                             -- :205-212
theorem r1cs_theta (state) (hs : StateAffine state) : IsR1CSCirc (Theta.main state) :=
  IsR1CSCirc.bind_out (r1cs_sub_thetaC state hs) fun n1 =>
  IsR1CSCirc.bind_out (r1cs_sub_thetaD _ (rowAffine_subOut_thetaC state n1)) fun n2 =>
  r1cs_sub_thetaXor _ hs (rowAffine_subOut_thetaD _ n2)                                     -- :283-287
theorem r1cs_round (c) (state) (hs) : IsR1CSCirc (KeccakRound.main c state) :=
  IsR1CSCirc.bind_out (r1cs_sub_theta state hs) fun n1 =>
  IsR1CSCirc.bind_out (r1cs_sub_chi _ (stateAffine_rhoPiWire (stateAffine_subOut_theta state n1))) fun _ =>
  IsR1CSCirc.pure _                                                                         -- :336-341
```
Loop version: `IsR1CSCirc.mapFinRange fun x n => (r1cs_sub_xor5Lane _ (hs _ (by omega)) ×5) n` (`:251-255`), `r1cs_thetaD` (`:257-260`, with `affineW_rotl (hc _ (by omega)) 1`), `r1cs_chi` (`:289-292`, with `(chiSource1 j).isLt`).

### R5. **K12 canonical-identity R1CS (`isR1CS_Cidentity`) — a different, stronger obligation**
- `isCidentityRowAt k e` means the row is literally `var k − A·B` with the *witness pin index* `k` matching position (`CostR1CSCanonicalSpec.lean:28-40`). This forces a **pin-counter discipline**: 1 fresh witness per constraint, in order.
- Core certificate (`KangarooTwelveGF2/Cost.lean:105-132`):
  ```lean
  attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid   -- NOTE: semireducible, the OPPOSITE of Keccak's irreducible
  set_option maxRecDepth 8000 in
  theorem isCidentity_ops (r) (s) (hs : AffineW s) : ∀ n, operationsIsCid n ((Round.main r s).operations n) := by
    intro n
    unfold Round.main
    rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector permutationBits _ n]
    refine ⟨operationsIsCid_witnessVector permutationBits _ _ _, ?_⟩
    rw [Circuit.bind_operations_eq, operationsIsCid_append, (CostIs.forEach fun i m => CostIs.assertZero _ m) _]
    refine ⟨?_, operationsIsCid_pure _ _ _⟩
    rw [Circuit.forEach.operations_eq]
    refine operationsIsCid_flatten_ofFn (L := 1) (fun i => (CostIs.assertZero _).constraints _) fun i => ?_
    simp only [Vector.getElem_finRange]; simp only [Nat.mul_one]
    refine ⟨?_, trivial⟩
    rw [wv_getElem]
    unfold chiProduct
    exact isCidentityRowAt_var_sub_mul
      (Affine.add (Affine.const _) (preChi_affine hs _ (Specs.KangarooTwelve.bitIndex _ _ _).isLt))
      (preChi_affine hs _ (Specs.KangarooTwelve.bitIndex _ _ _).isLt)
  ```
- **`wv_getElem`** (`Cost.lean:99-103`, duplicated at `Round.lean:27-32`) is the key: it names the witness pin without materializing the vector:
  ```lean
  theorem wv_getElem {n} (c) (w i) (h : i < n) : ((Circuit.witnessVector n c).output w)[i]'h = Expression.var ⟨w + i⟩ := by
    rw [show (Circuit.witnessVector n c).output w = varFromOffset (fields n) w from rfl]
    simp only [varFromOffset, instProvableTypeFields, size, Vector.getElem_mapRange]
  ```
- **`Balanced`** is an extra obligation the canonical path needs (`Cost.lean:143-147`):
  ```lean
  theorem balanced_sub (r) (s) : Balanced (subcircuit (Round.circuit r) s) :=
    Balanced.of_costIs (costIs_sub r s) fun n => by
      simp [circuit_norm, subcircuit, Round.circuit, Round.elaborated]; rfl
  ```
- Top-level (`KangarooTwelveGF2/Main.lean:252-303`) chains `IsCidCirc.bind_out (Cost.isCidentity_sub _ _ hsk) (Cost.balanced_sub _ _) fun nk => ...` 12 times, each preceded by `have hsk1 := Cost.affineW_subOut k _ hsk nk`. The output-affineness half is 12 stacked `apply Cost.affineW_subOut` then `exact hs0` (`Main.lean:285-298`) — a neat trick exploiting that the goal shape is unified by unification.
- `set_option maxRecDepth 8000 in` on both the `isCidentity_ops` and the top-level `isR1CS_Cidentity`.

### R6. **`Affine` structural derivation on a spec-level (non-gadget) expression tree** — K12 only
`KangarooTwelveGF2/Cost.lean:29-97`: `bit_affine`, `columnParity_affine` (nested `apply Affine.add` × 4), `theta_affine`, `rhoPi_affine`, `preChi_affine`, `chiFromProducts_affine`, `roundOut_affine` (with `split` on the ι lane-0 test and `unfold Specs.KangarooTwelve.roundConstantBit; split <;> exact Affine.const _`).
This exists because **K12 does θ/ρ/π/ι as raw expression algebra inside a single circuit**, so affineness must be proved about the *spec functions themselves* applied to expression vectors.

---

## 10. KangarooTwelveGF2: what is reused vs. KeccakF1600

### Reused (structurally identical, often verbatim)
1. `circuit_proof_start` / `circuit_proof_start_core` opening.
2. `def circuit : FormalCircuit ... where main := ...; soundness := ...; completeness := ...`.
3. The CW0 preamble (`change Operations.forAllFlat ... ; apply ...forAllFlat_of_structuralComputableWitnesses; unfold main`).
4. `Circuit.{bind,witnessVector,forEach,assertZero,pure}_structuralComputableWitnesses_iff` rewrite set.
5. `FormalCircuit.subcircuit_flatStructuralComputableWitnesses{,_of_condition}` for each subcircuit position, with `_of_condition` from round 2 on.
6. The ~35-line `Condition.implies` / `FlatOperation.forAll` induction boilerplate in `Main.computableWitness` (byte-for-byte the same modulo the field).
7. `CostIs.{bind,witnessVector,forEach,assertZero,pure,subcircuit}` ladder.
8. `AffineW` / `Affine.{add,const,sub,var}` for the R1CS obligation; `affineW_input_state` extraction via `simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by omega)`.
9. `eval_X` push-through-map lemma family (`eval_theta`, `eval_rhoPi`, `eval_preChi`, `eval_chiProduct`, `eval_chiFromProducts`, `eval_iota`, `eval_roundOut` ≙ Keccak's `eval_rhoPiWire_vec`, `map_iotaWire`, `eval_toLanes_vec`, `eval_notBits_vec`, `eval_xorConst_vec`, `eval_rotl_vec`).
10. `wv_getElem` ≙ Keccak's `affineW_subOut_*` `rfl`-shows.
11. `*_of_agreesBelow` output-stability lemma (`Round.eval_subOut_of_agreesBelow` ≙ `eval_stateVar_of_agreesBelow`).

### NOT reused / genuinely different
| Aspect | KeccakF1600 | KangarooTwelveGF2 |
|---|---|---|
| Bit abstraction | `valueBits : Vector (F p) 64 → ℕ` + `Normalized` invariant everywhere | **none** — `F 2` elements *are* bits; `Spec` is direct vector equality |
| Booleanity | must be proved & propagated (`IsBool.*`, `bool_finsum_*`) | free (`ZMod 2`) |
| XOR gadget | witness + `z - a - b + 2ab = 0`, 1 constraint/bit | **XOR is `+`, costs 0 constraints** — never gadgetized |
| Nonlinearity | one AND per χ bit, gadgetized as `AndLane` | one product per χ bit, inlined as `chiProduct` in a single `witnessVector`+`forEach` |
| Gadget count | 9 nested `FormalCircuit`s (XorLane, AndLane, Xor5Lane, ChiLane, ThetaC, ThetaD, ThetaXor, Theta, Chi, KeccakRound, Permutation) | **1** (`Round.circuit`) |
| Round loop | `Circuit.foldlRange 24` + induction | **fully unrolled 12× `do`-block** + `rw` chain |
| Cost/round | 6400 | 1600 (exactly 1 witness+1 row per state bit) |
| R1CS obligation | `isR1CS` (row-level) | `isR1CS_Cidentity` (row-level **+ pin-index alignment + `Balanced`**) |
| Opacity control | `attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS` | `attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid` (opposite direction!) |
| Constraint extraction | `sub_eq_zero.mp` + `ring_nf` | `linear_combination hrow` |
| Sub-circuit condition characterization | rely on `circuit_norm` | custom `forAllNoOffset_main` iff-lemma (`Round.lean:34-47`) proved by `rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append, ..., Circuit.forEach.forAllNoOffset]; simp only [..., wv_getElem, and_true]` |
| Extra `FormalCircuit` field | — | `exposedChannels_eq := by intro _ _ _ h; exact (List.not_mem_nil h).elim` (`Round.lean:109-111`) |

### Sponge / serialization patterns
- **Neither challenge is a sponge.** Both are the bare permutation (see `Challenge/Instances/KeccakF1600/COMPARISON.md:10-12`: "the challenge is the bare **permutation** … no padding/absorb/squeeze").
- Serialization exists only in KeccakF1600, as `toLanes` / `fromLanes` (`BitwiseOps.lean:81-86`) and its four supporting lemmas (`toLanes_getElem`, `fromLanes_getElem`, `stateValue_toLanes`, `fieldElems_fromLanes`, `eval_toLanes_vec`, `eval_fromLanes_vec` — `MainTheorems.lean:57-138`). Zero-cost (pure indexing).
- K12 needs **no serialization at all**: `Input.state : Vector F 1600` is already the spec's `State (F p2)`. Its only "boundary" lemma is `eval_input_state` (`MainTheorems.lean:8-13`), 6 lines.
- `Challenge/Utils/F2Bits.lean` provides `bitAt`/`wordAt`/`toWords`/`toNat` for GF(2) word-packing, but the KangarooTwelveGF2 solution **never uses them** (only `p2`).

---

## 11. Recurring helper-lemma index

### 11.1 Pure ℕ / bit arithmetic — `R/Solution/KeccakF1600/Theorems.lean`
| Name | Line | Statement | Role |
|---|---|---|---|
| `sum_bool_lt_two_pow` | 9 | `(∀ i, f i ≤ 1) → ∑ i : Fin n, f i * 2^i.val < 2^n` | bounds every `valueBits`; base of all `testBit_eq_false_of_lt` steps |
| `testBit_binary_sum` | 23 | `Nat.testBit (∑ f i * 2^i) k = decide (f k = 1)` | the workhorse: bit-index of a weighted sum |
| `valueBits_testBit` | 46 | `(valueBits x).testBit i = decide (x[i].val = 1)` | specialization to lanes |
| `bool_finsum_xor_eq` | 54 | `∑ (f i ^^^ g i)*2^i = (∑ f i*2^i) ^^^ (∑ g i*2^i)` | closes XorLane soundness |
| `bool_finsum_and` | 75 | `(∑ f*2^i) &&& (∑ g*2^i) = ∑ (f&&&g)*2^i` | closes AndLane soundness |
| `valueBits_lt_two_pow` | 95 | `Normalized x → valueBits x < 2^64` | side condition for rotations/xorConst |
| `Normalized.val_bool` | 104 | `Normalized x → ∀ i, x[i].val = 0 ∨ = 1` | ℕ-level restatement of `Normalized` |
| `rotLeft_testBit` | 112 | `(rotLeft 64 x k).testBit j = (decide (j<64) && x.testBit ((j + (64 - k%64)) % 64))` | the only nontrivial `Specs.Keccak` bit lemma; ~28 lines |

### 11.2 Lane-wiring correctness — `Theorems.lean` (continued)
| Name | Line | Role |
|---|---|---|
| `valueBits_rotl` / `Normalized_rotl` | 143 / 171 | ρ is value-correct + normalization-preserving |
| `valueBits_xorConst` / `Normalized_xorConst` | 178 / 212 | ι + ¬ |
| `notBits_eq_xorConst` | 223 | `notBits x = xorConst (2^64 - 1) x` — collapses ¬ into the xorConst theory |
| `valueBits_notBits` / `Normalized_notBits` | 233 / 240 | derived from the above two |
| `eval_rotl_vec`, `eval_notBits_vec`, `eval_xorConst_vec` | 246, 252, 261 | `Vector.map (eval env)` commutes with each wiring |
| `valueBits_eval_rotl`, `Normalized_eval_rotl`, `valueBits_eval_notBits`, `Normalized_eval_notBits`, `valueBits_eval_xorConst`, `Normalized_eval_xorConst` | 271–310 | **fused "eval + value/normalized" combinators**, each 2–3 lines (`rw [eval_X_vec, h, base_lemma]`); these are what gadget soundness proofs actually call |
| `stateNormalized_value_ext` | 313 | `(∀ i, Normalized s[i] ∧ valueBits s[i] = rhs[i]) → StateNormalized s ∧ stateValue s = rhs` |
| `rowNormalized_value_ext` | 325 | 5-lane twin |

### 11.3 Round-level bridging — `KeccakRoundTheorems.lean`
| Name | Line | Role |
|---|---|---|
| `map_rotate` | 9 | `(v.rotate off).map g = (v.map g).rotate off` |
| `eval_keccakState` | 17 | `eval env X = Vector.map (Vector.map (Expression.eval env)) X` — the single most-used bridge in the whole solution |
| `rhoPiWire_getElem` | 25 | `rfl`-level getElem, `:= Vector.getElem_ofFn ..` |
| `eval_rhoPiWire_vec` | 31 | eval commutes with ρπ |
| `StateNormalized_rhoPiWire` / `stateValue_rhoPiWire` | 47 / 54 | ρπ preserves normalization / matches `rhoPiSpec` |
| `stateValue_iotaMap` / `StateNormalized_iotaMap` / `map_iotaWire` | 69 / 93 / 102 | ι triple |
| `theta_eq`, `rhoPi_eq`, `chi_eq` | 112, 122, 132 | trusted-spec ↔ gadget-spec, by `interval_cases` |
| `keccakRound_decompose` | 142 | `keccakRound 64 rc A = iotaSpec rc (chiSpec (rhoPiSpec (thetaXorSpec A (thetaDSpec (thetaCSpec A)))))`; proof `rw [keccakRound, theta_eq, rhoPi_eq, chi_eq]; rfl` |

### 11.4 Boundary / global — `MainTheorems.lean`
`bit_of_val_lt_two`(11), `rc`(21), `rc_lt`(23), `keccakF6_eq_rounds`(27), `finFoldl_add_eq_sum`(47), `toLanes_getElem`(57), `stateValue_toLanes`(63), `StateNormalized_toLanes`(84), `valueBits_div_mod`(93), `fromLanes_getElem`(99), `fieldElems_fromLanes`(105), `eval_toLanes_vec`(119), `eval_fromLanes_vec`(131).

### 11.5 KangarooTwelveGF2 — `RoundTheorems.lean`
`StateVar`(10), `preChi`(12), `chiProduct`(16), `chiProducts`(24), `chiFromProducts`(28), `roundOut`(36); correctness `chiFromProducts_products`(41), `roundOut_products`(47); eval-commutation `eval_bit`(53), `eval_roundConstantBit`(61), `eval_columnParity`(68), `eval_theta`(74), `eval_rhoPi`(85), `eval_preChi`(96), `eval_chiProduct`(102), `eval_chiFromProducts`(109), `eval_iota`(122), `eval_roundOut`(138).

Every `eval_*` in this file has the identical 6-line body:
```lean
refine Vector.ext fun i hi => ?_
rw [Vector.getElem_map]
change Expression.eval env ((F s)[i]'hi) = (F (Vector.map (Expression.eval env) s))[i]'hi
unfold Specs.KangarooTwelve.F
rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
simp only [circuit_norm, <inner eval lemma>]
```
The **`change ... ; unfold ... ; rw [getElem_ofFn, getElem_ofFn]`** triple is the reusable shape for "eval commutes with a `Vector.ofFn` spec function".

---

## 12. Tactic vocabulary, by obligation

### soundness
```
circuit_proof_start [C.circuit, C.Assumptions, C.Spec]   -- ALWAYS the opener; list every subcircuit
circuit_proof_start_core                                 -- K12 variant when the auto-simp is unwanted
simp only [X.Assumptions, X.Spec, and_imp] at h_holds    -- currying subcircuit hypotheses
obtain ⟨c1, c2, ...⟩ := h_holds ; obtain ⟨v_k, n_k⟩ := c_k <args>
rw [v_n, v_{n-1}, ..., v_1]                              -- telescope value equations
apply stateNormalized_value_ext / rowNormalized_value_ext
simp only [<spec>_loop, circuit_norm, eval_vector, stateValue]
rw [eval_keccakState, eval_<wire>_vec, ← eval_keccakState] at h ⊢
getElem_eval_vector + CircuitType.eval_var_fields + rw [hs]
Vector.ext_iff.mp h i i.isLt ; simp [Vector.getElem_map] at this
sub_eq_zero.mp ; ring_nf ; ring_nf at h
linear_combination hrow                                  -- K12
IsBool.xor_is_bool / and_is_bool / xor_eq_val_xor / and_eq_val_and
bool_finsum_xor_eq / bool_finsum_and
interval_cases i <;> simp [...]                          -- spec-equality lemmas, with maxRecDepth 4000
induction k with | zero => ... | succ k ih => ...        -- 24-round fold
calc ... := eval_roundOut ...  _ = ... := by rw [...]  _ = ... := roundOut_products r input   -- K12
show <definitional retyping>                             -- used instead of simp at type boundaries
congr 1 ; Eq.trans ; omega ; norm_num
set_option maxHeartbeats 4000000 in
```

### completeness
```
circuit_proof_start [...]                                -- context has h_env instead of h_holds
simp only [X.Assumptions, X.Spec, and_imp] at h_env ⊢
obtain ⟨_, n1⟩ := c1 ha hb                               -- discard values, keep Normalized
exact ⟨⟨ha, hb⟩, ⟨n1, hc⟩, ...⟩                          -- supply each subcircuit's Assumptions
intro i ; have := h_env i ; simp only [Vector.getElem_ofFn] at this ; rw [this] ; ring
ZMod.natCast_val / ZMod.cast_id                          -- ℕ→F cast round-trip
rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_env  -- K12
simp only [ConstraintsHold.Completeness, forAllNoOffset_main]  -- K12
refine ⟨trivial, fun i => ?_⟩
simp only [Round.circuit, Round.Assumptions, and_self]   -- K12 top-level, whole proof
```

### mainCost
```
CostIs.bind / CostIs.pure / CostIs.witnessVector / CostIs.assertZero
CostIs.forEach / CostIs.mapFinRange / CostIs.foldlRange (constant := foldConstant)
CostIs.subcircuit (fun n => costIs_X b n)
(costIs_sub_X _ : CostIs _ ⟨256, 256⟩) n                 -- type ascription to pin K
have h : CostIs (main state) ⟨24 * 6400, 24 * 6400⟩ := ... ; exact h   -- defeq launder
rw [← hcount]                                            -- K12 pre-normalization of the Count sum
obtain ⟨state, d⟩ := b ; unfold ThetaXor.main            -- destructure pattern-matching `main`
fun input => (<term> : CostIs (main input) ⟨allocations, constraints⟩)
```

### isR1CS / isR1CS_Cidentity
```
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS   -- Keccak
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid          -- K12
IsR1CSCirc.bind_out / .bind / .pure / .witnessVector / .assertZero
IsR1CSCirc.forEach / .mapFinRange / .subcircuit
IsR1CSCirc.foldlRange_inv (constant := foldConstant) StateAffine hs hbody hstep
isR1CSRow_add_mul / isR1CSRow_sub_mul / isR1CSRow_mul
Affine.{const,var,add,sub,neg,fconst_mul,mul_fconst}
affineW_varFromOffset / affineW_witnessVector_output / affineW_mapRange_var
rw [show (subcircuit C b).output n = varFromOffset (fields 64) (n + k) from rfl]
simp only [X.circuit, X.elaborated, circuit_norm] ; exact Affine.var _
show Affine (<unfolded>) ; rw [Vector.getElem_ofFn / getElem_map / getElem_rotate] ; split
isR1CS_of_IsR1CSCirc (fun input hinput => ...) (fun input hinput => ...)
isR1CS_Cidentity_of_IsCidCirc ; IsCidCirc.bind_out ... (Cost.balanced_sub _ _) ; Balanced.of_costIs
isCidentityRowAt_var_sub_mul ; operationsIsCid_{append,witnessVector,pure,flatten_ofFn}
simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by omega)
set_option maxRecDepth 8000 in
```

### computableWitness
```
intro offset input env env'
change Operations.forAllFlat offset (FormalCircuitBase.computableWitnessCondition input env env') ((main input).operations offset)
apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
unfold main
attribute [local irreducible] main    -- BEFORE the theorem
simp only [Circuit.{bind,pure,witnessVector,witnessVar,assertZero,forEach,mapFinRange,foldlRange}_structuralComputableWitnesses_iff,
           FormalCircuit.subcircuit_structuralComputableWitnesses_iff, and_true]
and_intros / refine ⟨?_, ?_, ...⟩ / intro i
FormalCircuit.subcircuit_flatStructuralComputableWitnesses C parentInput subInput off hinput C.computableWitnesses env env'
FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition C parentInput subInput off
  (by intro k e e' hle h_agree h_input ; ...) C.computableWitnesses env env'
eval_mem_varFromOffset_fields_of_agreesBelow h_agree (by omega)
let first := C input ; let n1 := offset + first.localLength offset ; have hlen1 : ... := by simp [first, C, circuit_norm]
have hword : ... := by rw [← CircuitType.eval_var_fields, ..., getElem_eval_vector, ...] ; exact congrArg (fun v => v[j]'hj) h_input
have hmem : ... := by simp only [Vector.mem_iff_getElem] at ha ; rcases ha with ⟨b, hb, hget⟩ ; rw [← hget] ; simpa [Vector.getElem_map] using Vector.ext_iff.mp (hword ...) b hb
obtain ⟨_ | k', hiv⟩ := i                    -- Fin 24 zero/succ split at the fold
Operations.forAll_toFlat_iff ; FlatOperation.forAll_implies ; Condition.implies ; Condition.ignoreSubcircuit
induction ops generalizing off with | nil => simp [FlatOperation.forAll] | cons op ops ih => cases op with | witness | assert | lookup | interact
ProverEnvironment.agreesBelow_of_le hagree hoff
FormalCircuitBase.computableWitnesses_implies (circuit := C.base) C.computableWitnesses   -- when types allow
```

---

## 13. Cross-cutting engineering notes (high signal for a proof loop)

1. **Two-file rule for heavy proofs.** Any proof needing `maxHeartbeats 4000000` lives alone in its own file (`PermutationSound.lean`, `PermutationComplete.lean`). The assembly file re-imports both.
2. **`field := by simp only [thm]` instead of `field := thm`** when a structure field's defeq check `whnf`-loops (`Permutation.lean:21-22`, with an explanatory comment naming clean's own Keccak as precedent).
3. **Opacity is directional per obligation.** R1CS predicates must be `irreducible` for the Keccak path (`Cost.lean:150-153`: prevents `r1csProducts` from unfolding on 64-bit expressions), but `semireducible` for the K12 canonical path (`Cost.lean:107`: the pin-counter recursion must compute).
4. **`attribute [local irreducible] main` immediately before every `computableWitnesses`** so the structural rewrites don't race the unifier.
5. **Spec functions written as `Vector.ofFn` so their per-index restatement is `rfl`.** Six `*Spec_loop` lemmas exist for this reason alone.
6. **Explicit `ConstantLength` for parameterized fold bodies.** The default `by infer_constant_length` fails on `KeccakRound.circuit (rc i)`; the manual `ConstantLength.fromConstantLength' _ (fun acc i i' n => by rw [body, body, keccakRound_localLength, keccakRound_localLength])` is required.
7. **Total-ize `Fin`-indexed constants** for induction: `rcN : ℕ → ℕ` (`if h : i < 24 then rc ⟨i,h⟩ else 0`) with `rcN_eq`. Without this the `succ` case of the induction cannot state `stateVar n k`.
8. **Cost is compositional; R1CS needs an invariant; soundness needs induction.** All three iterate over the same fold but use three different techniques (`CostIs.foldlRange`, `IsR1CSCirc.foldlRange_inv`, hand-rolled `induction k`).
9. **`allocations`/`constraints` are declared in two places for KeccakF1600** — `Main.lean:148-149` (`@[reducible] def allocations : Nat := 153600` in `namespace Solution.KeccakF1600`) and `Challenge/Instances/KeccakF1600/Cost.lean:1` (`Solution.KeccakF1600.allocations := 42`, the placeholder the submission overwrites). K12 does the same at `Main.lean:11-13`. Worth flagging as a build-integration wrinkle.
10. **`COMPARISON.md` sets the bar**: vocdoni/keccak256-circom scores exactly `307,200 = 153,600 + 153,600` — i.e. **this reference solution ties the Circom baseline exactly**, one witness + one constraint per XOR/AND bit, with ρ/π/ι/¬ free. The ~38k "essential-χ floor" is noted as unreachable in pure R1CS.
