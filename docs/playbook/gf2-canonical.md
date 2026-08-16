# zkGolf GF(2) Canonical Reference Solutions — Proof Pattern Catalog

Raw retrieval data. All paths absolute. All identifiers verbatim from source.

---

## 0. Corpus map

| File | Lines | Role |
|---|---|---|
| `/Users/lucidsamuel/experiments/scribe/corpus/zk-golf-challenges/Challenge/Utils/F2Bits.lean` | 36 | `p2`, `bitAt`, `wordAt`, `toWords`, `toNat` |
| `.../Challenge/Utils/CostR1CS.lean` | ~850 | `Affine`, `AffineW`, `AffineProvable`, `AffineOutput`, `Count`, `CostIs`, `circuitCost`, `IsR1CSCirc`, `isR1CS` |
| `.../Challenge/Utils/CostR1CSCanonicalSpec.lean` | 94 | **trusted surface**: `isCidentityRowAt`, `flatOperationsIsCid`, `IsCidCirc`, `isR1CS_Cidentity` (4 defs, 0 theorems) |
| `.../Challenge/Utils/CostR1CSCanonical.lean` | 306 | machinery: `operationsIsCid`, append/flatten laws, `Balanced`, `IsCidCirc.bind/bind_out/subcircuit/pure` |
| `.../Challenge/Utils/CostR1CSCanonicalGuarantees.lean` | 120 | reviewer-facing: `assertExprs`, `flatOperationsIsCid.pin`, `IsCidCirc.row_pins`, 2 sanity `example`s |
| `.../Challenge/Instances/SHA256CompressGF2Canonical/{Interface,Challenge,Cost}.lean` | 61/35/2 | contract |
| `.../Challenge/Instances/Blake3CompressGF2Canonical/{Spec,Interface,Challenge,Cost}.lean` | 201/43/37/2 | contract + `Blake3Bits` bit semantics |
| `.../Solution/SHA256CompressGF2/` (18 files) | 3 862 | **shared gadget library** (no `main`): general-C `IsR1CSCirc` certificates + all pure/bit lemmas |
| `.../Solution/SHA256CompressGF2Canonical/` (12 files) | 2 601 | canonical `main` + `*Canon` gadgets + `Cost.lean` (725 L) |
| `.../Solution/Blake3CompressGF2Canonical/` (13 files) | 4 149 | canonical `main`, `Cost.lean` (546), `Canonical.lean` (803), `Witness.lean` (1086) |

Note: `Solution/SHA256CompressGF2/` has **no `Main.lean` and no matching `Challenge/Instances` dir**. It is a library: it holds `Add32`, `Ch32`, `Maj32`, `Pin32`, `Pin256`, `ScheduleStep`, `Round`, `Sched16`, `Rounds16` in *general-C* (linear rows allowed) form plus every `Spec`, every pure-ℕ lemma, and every `eval_*_congr`. The canonical solution imports it, reuses the `Spec`s/`Assumptions` verbatim, and swaps in `*Canon` circuits.

---

## 1. What "GF2" means for the obligation set

### 1.1 Field
`Challenge/Utils/F2Bits.lean:17-19`:
```lean
@[reducible] def p2 : ℕ := 2
instance : Fact (Nat.Prime p2) := ⟨Nat.prime_two⟩
```
`F p2 = ZMod 2` is a **prime field**, so the entire Clean prime-field machinery (`FormalCircuit`, `Soundness`, `Completeness`, `CostIs`, `IsR1CSCirc`, `subcircuit`) applies **unchanged**. GF(2) is not a different obligation *shape*; it changes the *semantics layer* only.

### 1.2 Consequences vs. prime-field challenges

| Aspect | Prime-field (e.g. `SHA256`, `Secp256k1ScalarMul`) | GF(2) |
|---|---|---|
| **Range/bit assumptions** | need `ByteVector`/`isBit` preconditions | **none**: `def Assumptions (_input) := True`. Doc: *"There are no assumptions because every element of `F 2` is already a bit."* (`Interface.lean:15`) |
| `+` | field add | **XOR** |
| `*` | field mul | **AND** |
| squaring | nontrivial | `a² = a` — exploited in the carry form |
| rotation/shift | needs decomposition gadgets | **free re-indexing of a `Vector.ofFn`, zero constraints** |
| Word ↔ ℕ bridge | `ByteVector.value` | `toNat`/`wordAt` (`Finset.range`-sum), + `Utils.Bits.fromBits` |
| Boolean facts | `omega`/`decide` on `Fin p` | **`by decide` over all of `F 2`** (2 or 8 cases) |

### 1.3 The word ↔ ℕ bridge (F2Bits.lean:22-34)
```lean
@[reducible] def bitAt {N : ℕ} (v : Vector (F p2) N) (k : ℕ) : ℕ := ZMod.val ((v[k]?).getD 0)
def wordAt (w : ℕ) {N : ℕ} (v : Vector (F p2) N) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range w, bitAt v (w * i + j) * 2 ^ j
def toWords (w n : ℕ) {N : ℕ} (v : Vector (F p2) N) : Vector ℕ n := Vector.ofFn fun i : Fin n => wordAt w v i.val
def toNat {N : ℕ} (v : Vector (F p2) N) : ℕ := wordAt N v 0
```
Out-of-range reads are **0** (`getElem?`+`getD`), making `bitAt` total — this is why `Add32.bitAt_eq` (below) is needed to convert to `ZMod.val v[j]`.

---

## 2. What "Canonical" means for the obligation set

### 2.1 The five obligations, verbatim (`Challenge/Instances/SHA256CompressGF2Canonical/Challenge.lean:20-33`)
```lean
def main : Var Input (F p2) → Circuit (F p2) (Var Output (F p2)) := sorry
instance elaborated : ElaboratedCircuit (F p2) Input Output main := sorry
theorem soundness : GeneralFormalCircuit.Soundness (F p2) main Assumptions Spec := sorry
theorem completeness : GeneralFormalCircuit.Completeness (F p2) main ProverAssumptions ProverSpec := sorry
theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := sorry
theorem isR1CS_Cidentity : Challenge.CostR1CS.isR1CS_Cidentity main := sorry
theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F p2) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := sorry
```
**The only obligation that differs from the general challenges is #4**: `isR1CS_Cidentity` replaces `isR1CS`. Everything else (`soundness`, `completeness`, `mainCost`, `computableWitness`) is bit-for-bit the same *statement form*.

### 2.2 The canonical predicate (`CostR1CSCanonicalSpec.lean:37-76`)
```lean
def isCidentityRowAt (k : ℕ) (e : Expression F) : Prop :=
  ∃ (A B : Expression F), Affine A ∧ Affine B ∧
    e = (Expression.var ⟨k⟩ : Expression F) - A * B

def flatOperationsIsCid : ℕ → List (FlatOperation F) → Prop
  | _, [] => True
  | k, .witness _ _ :: ops => flatOperationsIsCid k ops
  | k, .assert e :: ops => isCidentityRowAt k e ∧ flatOperationsIsCid (k + 1) ops
  | _, .lookup _ :: _ => False
  | _, .interact _ :: _ => False

def IsCidCirc (c : Circuit F α) : Prop := ∀ n, flatOperationsIsCid n (Operations.toFlat (c.operations n))

def isR1CS_Cidentity {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (main : Var Input F → Circuit F (Var Output F)) : Prop :=
  ∀ input : Var Input F, AffineProvable input → IsCidCirc (main input) ∧ AffineOutput (main input)
```

**Three strengthenings over `isR1CS`:**

1. **Ordered, not existential.** `k` is an *argument*, not `∃`. Row `t` (in `toFlat` emission order) must pin *exactly* variable `n₀ + t`. Hence C = identity matrix, not a permutation. Guarantee: `IsCidCirc.row_pins` (`CostR1CSCanonicalGuarantees.lean:63-67`).
2. **No linear-row case.** Spec doc: *"a copy or sum row must be written as an explicit product `var k − A·1`"*. Contrast general `isR1CSRow` which accepts `isR1CSRow_of_affine`. This forces the `* 1` in every pin gadget.
3. **Refinement.** `isR1CS_Cidentity.isR1CS` (`CostR1CSCanonical.lean:298-300`) + `guarantee_obligation_refines`.

### 2.3 Extra (non-trusted, solution-side) obligations that canonicality induces

These do **not** appear in `Challenge.lean` but are forced by the composition machinery:

- **`Balanced`** (`CostR1CSCanonical.lean:229-234`):
  ```lean
  def Balanced (c : Circuit F α) : Prop := ∀ n, (operationCount (c.operations n)).constraints = c.localLength n
  theorem Balanced.of_costIs {c : Circuit F α} {K : Count} (hc : CostIs c K)
      (hL : ∀ n, c.localLength n = K.constraints) : Balanced c := fun n => by rw [hc n, hL n]
  ```
  Every gadget needs `balanced_sub`. **This is the single biggest structural difference from the general-C solutions**: `IsR1CSCirc.bind` needs no side condition; `IsCidCirc.bind` needs `Balanced f` because the pin counter and the allocation offset must advance in lockstep.
- **`operationsIsCid`** — the ops-level (nested-aware) mirror, bridged by `isCidCirc_iff_ops`.
- **`CostIs` is a *prerequisite* for `IsCidCirc`, not an independent obligation.** In the general solutions `Cost.lean` and R1CS certs are independent; canonically `isCidentity_ops` proofs literally `rw [... , CostIs.witnessVector 31 _ n]` and `(CostIs.forEach ...) _` to compute the append split point.
- **`affineW_subOut` / `output_*_eq` per gadget** — needed to feed `AffineW` into the next `isCidentity_sub`.

### 2.4 Cost penalty of canonicality (measured)

| Gadget | general-C | canonical | factor |
|---|---|---|---|
| `Add32` → `Add32Canon` | 31/31 | **62/62** | 2× (split into product row + carry row) |
| `Ch32` → `Ch32Canon` | 32/32 | 32/32 | 1× (output inlined as `zxorOut` instead of witnessed) |
| `Maj32` → `Maj32Canon` | 32/32 | 32/32 | 1× |
| `Pin32` → `Pin32Canon` | 32/32 | 32/32 | 1× (only `* 1` added) |
| `ScheduleStep` → `ScheduleStepCanon` | 125 | **218** | |
| `Round` → `RoundCanon` | 345 | **562** | |
| `Sched16` → `Sched16Canon` | 2000 | **3488** | |
| `Rounds16` → `Rounds16Canon` | 5776 | **9248** | |
| `main` | — | **47 952** | `3·3488 + 4·9248 + 8·62` |
| Blake3 `main` | — | **86 880** | `1024 + 85344 + 512` |

---

## 3. Obligation-by-obligation pattern catalog

### 3.1 `soundness`

#### S1 — `circuit_proof_start [main, Spec, <every subcircuit>, <every Assumptions>, <every Spec>]`
Universal opener. Unfolds the do-block into `h_holds` conjunction, `h_input` (eval bridge), `env`, `i₀`, `input_var`.
- `SHA256CompressGF2Canonical/RoundCanon.lean:51-54`:
  ```lean
  circuit_proof_start [main, Spec, Add32Canon.circuit, Pin32Canon.circuit,
    Ch32Canon.circuit, Maj32Canon.circuit,
    Add32.Assumptions, Pin32.Assumptions, Ch32Canon.Assumptions, Maj32Canon.Assumptions,
    Add32.Spec, Pin32.Spec, Ch32Canon.Spec, Maj32Canon.Spec]
  ```
- `Blake3CompressGF2Canonical/Circuit.lean:243-245` (top-level `main`).
- Variant with extra `eval_*` rewrites baked in: `Blake3.../Circuit.lean:38-40` `circuit_proof_start [main, Spec, PinStateCanon.circuit, PinStateCanon.Assumptions, PinStateCanon.Spec, eval_splitWords, eval_initialState, eval_initialBlock]`.

#### S2 — `obtain ⟨…⟩ := h_holds` — destructure the per-subcircuit hypotheses
`RoundCanon.lean:55`: `obtain ⟨hch, hmaj, ht1a, ht1b, ht1c, ht1, ht2, hen, han, hA, hE⟩ := h_holds`
`Add32Canon.lean:55`: `obtain ⟨h_prod, h_carry⟩ := h_holds` (two `forEach` families).
`Blake3/G.lean:170`: `obtain ⟨ha0, hav, hdv, hcv, hbv, hpin⟩ := h_holds`.

#### S3 — **Pointwise input-evaluation bridge** `hv`
Goal shape before: hypothesis `h_input : Vector.map (Expression.eval env) input_var = input`. Need `Expression.eval env (input_var[m]) = input[m]`.
Idiom (`RoundCanon.lean:56-60`, identical in `ScheduleStepCanon.lean:48-52`, `Round.lean:281-285`):
```lean
have hv : ∀ (m : ℕ) (hm : m < 288),
    Expression.eval env (input_var[m]'hm) = input[m]'hm := by
  intro m hm
  have h := Vector.ext_iff.mp h_input m hm
  rwa [Vector.getElem_map] at h
```
With a mod-accessor (`a96`/`b32`/`b256`) the shape gains a `Nat.mod_eq_of_lt` step (`Ch32Canon.lean:40-46`):
```lean
have hv : ∀ (m : ℕ) (hm : m < 96), Expression.eval env (a96 input_var m) = input[m]'hm := by
  intro m hm
  unfold a96
  have h2 := Vector.ext_iff.mp h_input (m % 96) (Nat.mod_lt _ (by norm_num))
  rw [Vector.getElem_map] at h2
  simp only [Nat.mod_eq_of_lt hm] at h2 ⊢
  exact h2
```
**Why it closes:** `Vector.ext_iff.mp` turns vector equality into indexed equality; `Vector.getElem_map` commutes `getElem` past `Vector.map`.

#### S4 — **Windowed word bridge** `hw` via `toNat_map_eval_window`
Goal: `toNat (Vector.map (Expression.eval env) (w288 input_var l)) = wordAt 32 input l`.
`RoundCanon.lean:61-70` / `ScheduleStepCanon.lean:53-62`:
```lean
have hw : ∀ l : ℕ, 32 * l + 32 ≤ 288 →
    toNat (Vector.map (Expression.eval env) (w288 input_var l)) = wordAt 32 input l := by
  intro l hl
  refine toNat_map_eval_window _ input l hl ?_
  intro j hj
  unfold w288 a288
  rw [Vector.getElem_ofFn]
  have hlt : 32 * l + j < 288 := by omega
  simp only [Nat.mod_eq_of_lt hlt]
  exact hv _ hlt
```
Backing lemma `SHA256CompressGF2/Theorems.lean:199-207`:
```lean
theorem toNat_map_eval_window {N : ℕ} {env : Environment (F p2)}
    (w : Var (fields 32) (F p2)) (v : fields N (F p2)) (k : ℕ) (hk : 32 * k + 32 ≤ N)
    (hw : ∀ (j : ℕ) (hj : j < 32), Expression.eval env (w[j]'hj) = v[32 * k + j]'(by omega)) :
    toNat (Vector.map (Expression.eval env) w) = wordAt 32 v k := by
  rw [toNat_eq_fromBits, wordAt_eq_fromBits v k hk]; apply congrArg
  refine Vector.ext fun j hj => ?_
  rw [Vector.getElem_map, Vector.getElem_map, windowVals_getElem v k hk j hj, hw j hj]
```

#### S5 — **Chain-rewriting subcircuit specs** (linear substitution of `toNat` equations)
`RoundCanon.lean:71-81` — the canonical dataflow spine:
```lean
rw [wordAt_eval_c96_0, wordAt_eval_c96_1, wordAt_eval_c96_2,
    hw 4 (by norm_num), hw 5 (by norm_num), hw 6 (by norm_num)] at hch
rw [toNat_eval_upperSigma1E, hw 4 (by norm_num), hw 7 (by norm_num)] at ht1a
rw [ht1a, hch] at ht1b
rw [ht1b, toNat_eval_constW, Nat.add_mod_mod] at ht1c
rw [ht1c, hw 8 (by norm_num)] at ht1
rw [toNat_eval_upperSigma0E, hw 0 (by norm_num), hmaj] at ht2
rw [ht1, hw 3 (by norm_num)] at hen
rw [ht1, ht2] at han
```
**Why it closes:** each subcircuit's `Spec` is a `toNat out = f(wordAt …)` equation; substituting them in dependency order collapses to the round formula.
BLAKE3 analogue, `Blake3/G.lean:170-176` (bit-vector-level, no `toNat`):
```lean
obtain ⟨ha0, hav, hdv, hcv, hbv, hpin⟩ := h_holds
rw [ha0] at hav; rw [hav] at hdv; rw [hdv] at hcv; rw [hcv] at hbv
rw [hpin, hav, hbv, hcv, hdv]; rfl
```

#### S6 — `interval_cases` + explicit `#v[…]` getElem lemmas
`RoundCanon.lean:82-96` (and `Round.lean:307-321`):
```lean
rw [sha256Round_eq]
simp only [Vector.getElem_ofFn]
refine Vector.ext fun i hi => ?_
simp only [Vector.getElem_ofFn]
interval_cases i
· rw [vec8_0, wordAt_eval_outState_0, hA, han]
  simp only [show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
· rw [vec8_1, wordAt_eval_outState_pass env _ _ _ input hv 1 (by omega) (by omega) (by omega)]
…
```
Supporting kernel-friendly lemmas `Round.lean:127-134`:
```lean
theorem vec8_0 (x0 … x7 : ℕ) : (#v[x0,x1,x2,x3,x4,x5,x6,x7])[0] = x0 := rfl   -- …through vec8_7
theorem sha256Round_eq (state : Vector ℕ 8) (k w : ℕ) : Specs.SHA256.sha256Round state k w = #v[…] := rfl
```
**Why:** `#v[…]` indexing does not reduce fast under `simp`; the 8 `rfl` lemmas make it a rewrite.

#### S7 — the `add32` unfolding idiom
Recurring exact text (`Main.lean:83`, `RoundCanon.lean:88,93`):
```lean
simp only [show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
```
Bridges the `Add32.Spec` (`(x+y) % 2^32`) to `Specs.SHA256`'s `add32`.

#### S8 — **`Nat.eq_of_testBit_eq` + `decide` bit identity** (the GF(2) signature move)
Used for every *bitwise* gadget spec. `SHA256CompressGF2/Theorems.lean:318-338` (`ch_words`):
```lean
apply Nat.eq_of_testBit_eq
intro i
by_cases hi : i < 32
· have h1 : (toNat out).testBit i = decide (ZMod.val (out[i]'hi) = 1) := testBit_toNat out i hi
  have h2 : decide (ZMod.val (out[i]'hi) = 1) = decide (ZMod.val ((v[64+i]) + (v[i]) * ((v[32+i]) + (v[64+i]))) = 1) := by rw [hout i hi]
  have h3 := ch_bit (v[i]'…) (v[32+i]'…) (v[64+i]'…)
  have h4 := testBit_Ch (wordAt 32 v 0) (wordAt 32 v 1) (wordAt 32 v 2) i hi
  rw [h1, h2, h3, h4, testBit_w96_0 v i hi, testBit_w96_1 v i hi, testBit_w96_2 v i hi]
· push_neg at hi
  rw [testBit_toNat_ge out i hi, testBit_Ch_ge _ _ _ i (wordAt_lt v 1 (by omega)) (wordAt_lt v 2 (by omega)) hi]
```
**Why it closes:** below 32 both sides reduce to the *same boolean expression* in three `decide (ZMod.val … = 1)` atoms; at/above 32 both sides are `false`.

#### S9 — `linear_combination` for GF(2) constraint arithmetic
Everywhere a constraint hypothesis must be turned into a value equation.
- `Ch32Canon.lean:53-57`: `have hc := h_holds ⟨j, hj⟩ … congr 1; linear_combination hc`
- `Pin32Canon.lean:47`: `linear_combination hc`
- `Add32Canon.lean:75`: **`linear_combination hc0 + hp0`** (two rows: carry row + product row summed)
- `Add32Canon.lean:96`: `linear_combination hc + hp`
- `Add32.lean:174,194` (general-C, one row): `linear_combination h0` / `linear_combination hc`

**This is the exact canonical/general delta in the adder soundness proof:** the canonical adder splits one row into two, so `linear_combination` takes the *sum of the two hypotheses*.

#### S10 — `have hunf : carryVal … = <explicit> := rfl` (defeq unfolding of a recursive def under a binder)
Appears 4× in `SHA256CompressGF2Canonical/Add32Canon.lean` (lines 68-72, 84-94, 194-204) and identically in `Blake3CompressGF2Canonical/Add32Canon.lean` and `SHA256CompressGF2/Add32.lean:167-171,182-192,263-267,275-285`. Verbatim shape:
```lean
have hunf : carryVal (fun j => Expression.eval env (input_var_x[j % 32]'(Nat.mod_lt _ (by norm_num))))
           (fun j => Expression.eval env (input_var_y[j % 32]'(Nat.mod_lt _ (by norm_num)))) (n + 1 + 1)
    = (Expression.eval env (input_var_x[(n+1) % 32]'…) + carryVal … (n + 1))
      * (Expression.eval env (input_var_y[(n+1) % 32]'…) + carryVal … (n + 1))
      + carryVal … (n + 1) := rfl
rw [hunf]
```
**Why:** `carryVal` is defined by structural recursion with a `let`; `simp` will not unfold it under the eval-closures, but the equation is `rfl`. Stating it explicitly and `rw`-ing is the reliable idiom.

#### S11 — **Fold invariant induction** `have Q : ∀ k, k ≤ 16 → …`
The universal loop-soundness pattern.
- `Sched16Canon.lean:86-133`:
  ```lean
  have Q : ∀ k, k ≤ 16 → ∀ j (hj : j < 32),
      toNat (Vector.map (Expression.eval env) ((varBuf i₀ input_var k)[j]'hj)) = (PureSchedule.ext32 x k)[j]'hj := by
    intro k; induction k with
    | zero => … by_cases hj16 : j < 16 … Vector.getElem_append_left / Vector.getElem_append_right
    | succ k ih =>
      have hvb : varBuf i₀ input_var (k + 1) = (varBuf i₀ input_var k).set (16 + k) (stepWord i₀ k) (by omega) := by
        conv_lhs => rw [varBuf]; rw [dif_pos hk16]
      have hstep := h_holds ⟨k, hk16⟩
      rw [foldlAcc_eq_varBuf i₀ input_var k hk16] at hstep
      replace hstep := hstep (by simp only [ScheduleStepCanon.circuit, ScheduleStepCanon.Assumptions])
      rw [show ScheduleStepCanon.circuit.Spec = ScheduleStepCanon.Spec from rfl] at hstep
      simp only [ScheduleStepCanon.Spec, wordAt_eval_c128_0, …, scheduleStep_output, scheduleStep_localLength] at hstep
      rw [ih (by omega) (k + 14) (by omega), ih … (k+9) …, ih … (k+1) …, ih … k …] at hstep
      by_cases hjk : j = 16 + k
      · subst hjk; rw [hvb, Vector.getElem_set_self, stepWord, hstep]
        rw [PureSchedule.ext32, dif_pos hk16, Vector.getElem_set, if_pos (by omega : k + 16 = 16 + k)]
      · rw [hvb, Vector.getElem_set_ne (by omega) hj (by omega), PureSchedule.ext32_succ_ne x k j hj (by omega)]
        exact ih (by omega) j hj
  ```
- `Rounds16Canon.lean:60-88`, same skeleton with `stateVar256` and `PureRounds.applyN`:
  ```lean
  rw [foldlAcc_eq_stateVar256 r0 i₀ input_var k hk16] at hstep
  replace hstep := hstep (by simp only [RoundCanon.circuit, RoundCanon.Assumptions])
  rw [show (RoundCanon.circuit (kAt (r0 + k))).Spec = RoundCanon.Spec (kAt (r0 + k)) from rfl] at hstep
  …
  rw [← show PureRounds.applyN r0 schedOf (k + 1) stateOf
      = Specs.SHA256.sha256Round (PureRounds.applyN r0 schedOf k stateOf) (kAt (r0 + k)) (PureRounds.at16 schedOf k) from rfl] at hstep
  ```
**Key sub-idioms:** `conv_lhs => rw [varBuf]` + `dif_pos`/`dif_neg`; `Vector.getElem_set_self` / `Vector.getElem_set_ne`; `show … from rfl` to reconcile a `FormalCircuit.Spec` projection with the named `Spec`.

#### S12 — `set_option maxRecDepth 100000 in` before deep-fold soundness
`Rounds16Canon.lean:46` and `Rounds16.lean:41`.

#### S13 — Top-level `main` soundness: window-advance splicing
`SHA256CompressGF2Canonical/Main.lean:47-72`:
```lean
have hw1 : PureSchedule.extend16 block = PureSchedule.window block 1 := by
  have h := PureSchedule.extend16_window block 0 (by omega)
  rwa [PureSchedule.window_zero] at h
have hw2 : PureSchedule.extend16 (PureSchedule.window block 1) = PureSchedule.window block 2 := PureSchedule.extend16_window block 1 (by omega)
…
rw [hw1] at hsc1; rw [hsc1, hw2] at hsc2; rw [hsc2, hw3] at hsc3
rw [ofFn_wordAt_c768_sched env input_var_h input_var_m, ofFn_wordAt_c768_state env …, hmIn, hhIn] at hrd1
…
have hwin : ∀ k, PureRounds.win64 (PureSchedule.valSchedule block 48) k = PureSchedule.window block k := fun k => rfl
have hS4' : Specs.SHA256.sha256Compress hIn8 (Specs.SHA256.messageSchedule block) = PureRounds.applyRounds16 48 … := by
  rw [PureRounds.sha256Compress_split, PureSchedule.messageSchedule_eq, hwin 0, hwin 1, hwin 2, hwin 3, PureSchedule.window_zero]
have hS4 := hrd4.trans hS4'.symm
rw [Specs.SHA256.compressBlock, ← hS4]
```
Then `interval_cases k` over the 8 output words, each block:
```lean
rw [wordAt_eval_out256_sel env _ _ _ _ _ _ _ _ 0 (by norm_num)]
simp only [o8sel]
have hk := hadd 0
rw [show ((0 : Fin 8) : ℕ) = 0 from rfl] at hk
rw [hk, toNat_eval_w256 env input_var_h 0 (by norm_num), toNat_eval_w256 env _ 0 (by norm_num), hhIn]
simp only [Fin.getElem_fin, toWords_getElem, show ∀ a b : ℕ, _root_.add32 a b = (a + b) % 2 ^ 32 from fun _ _ => rfl]
```

#### S14 — BLAKE3: `toNat_injective` to lift a numeric spec back to bit vectors
`Blake3/G.lean:51-53` (`AddExact.soundness`):
```lean
rw [hpin]
apply toNat_injective
rw [hadd, toNat_addWord]
```
`toNat_injective` (`Blake3/Theorems.lean:59-66`):
```lean
theorem toNat_injective : Function.Injective (toNat : Word (F p2) → ℕ) := by
  intro x y hxy
  refine Vector.ext fun i hi => ?_
  have hx := val_eq_testBit x i hi; have hy := val_eq_testBit y i hi
  rw [hxy] at hx
  have hv : ZMod.val (x[i]'hi) = ZMod.val (y[i]'hi) := hx.trans hy.symm
  exact ZMod.val_injective p2 hv
```
**This is the load-bearing GF(2) bridge in BLAKE3**: the shared `Add32.Spec` is numeric (`toNat out = (toNat x + toNat y) % 2^32`) but the trusted BLAKE3 spec is bit-level (`addWord`), so `toNat_injective` + `toNat_addWord` converts.

#### S15 — BLAKE3 composite soundness: pure `rw` chaining, zero arithmetic
Every composite in `Blake3/Circuit.lean` and `Blake3/Round.lean` is 3–6 lines. E.g. `Steps7.soundness` (`Circuit.lean:172-180`):
```lean
obtain ⟨h4, h6, h7⟩ := h_holds
rw [h4] at h6; rw [h6] at h7; exact h7
```
`Steps2.soundness` (`Circuit.lean:107-111`): `simpa only [Blake3Bits.steps2, h1] using h2`.
`Round.soundness` (`Round.lean:212-217`): `simpa only [roundState, hcolumns] using hdiagonals`.
Top-level (`Circuit.lean:241-252`):
```lean
obtain ⟨hprepare, hsteps, hfinal⟩ := h_holds
rw [hprepare] at hsteps
have hresult := congrArg Config.state hsteps
have hinitial := congrArg Config.state hprepare
dsimp only at hresult hinitial
rw [hresult, hinitial] at hfinal
simpa only [Blake3Bits.compress, Blake3Bits.compressState] using hfinal
```
**Design lesson:** BLAKE3 makes *every* subcircuit `Spec` an **exact functional equality** `output = f input` (rather than a `toNat` relation), so composition is `rw` only. This is why 86 880 constraints cost ~260 lines of soundness while SHA-256's 47 952 costs ~500.

---

### 3.2 `completeness`

Only three shapes exist in the entire corpus.

#### C1 — leaf gadget (witnessVector + forEach): `h_env` + `ring`
`Ch32Canon.lean:59-64`, `Maj32Canon.lean:59-64`, `Pin32Canon.lean:49-54`, `Pin256Canon.lean:130-135`, `Blake3/PinCanon.lean:57-62,147-153`, `Pin32.lean:46-51`:
```lean
theorem completeness : Completeness (F p2) main Assumptions := by
  circuit_proof_start
  intro i
  have henv := h_env i
  simp only [circuit_norm, Vector.getElem_ofFn] at henv ⊢
  rw [henv]; ring
```
**Why:** `h_env i` says the witness at slot `i` equals the generator expression; substituting makes the constraint `e − e = 0`, closed by `ring` over `F 2`.

#### C2 — composite of subcircuits: `simp only [<circuit>, <Assumptions>, and_self]`
Because every GF(2) `Assumptions` is `True`, completeness of a composite is *purely* discharging trivial preconditions.
- `ScheduleStepCanon.lean:67-69`: `simp only [Add32Canon.circuit, Add32.Assumptions, Pin32Canon.circuit, Pin32.Assumptions, and_self]`
- `RoundCanon.lean:98-101`: 4-way `simp only [… , and_self]`
- `Rounds16Canon.lean:97-99`: `simp [RoundCanon.circuit, RoundCanon.Assumptions, Pin256Canon.circuit, Pin256.Assumptions]`
- `Sched16Canon.lean:148-151`: `intro i; simp only [ScheduleStepCanon.circuit, ScheduleStepCanon.Assumptions]`
- `Blake3/Circuit.lean:254-259` (top-level): `simp only [Prepare.circuit, Prepare.Assumptions, Steps7.circuit, Steps7.Assumptions, Finalize.circuit, Finalize.Assumptions, true_and]`
- SHA-256 top-level `Main.lean:134-137`: `simp [Sched16Canon.circuit, Sched16Canon.Assumptions, Rounds16Canon.circuit, …, Add32.Assumptions]`

#### C3 — the adder: `henv`/`henvp` + `cases iv` + `ring`
`Add32Canon.lean:143-206`. Structure:
```lean
circuit_proof_start [main, Add32.Spec, carryE, at32, at31]
obtain ⟨he_p, he_c, -⟩ := h_env          -- two witness families + trailing
have henv  : ∀ k, (hk : k < 31) → env.get (i₀ + 31 + k) = carryVal … (k + 1) := …   -- carries
have henvp : ∀ k, (hk : k < 31) → env.get (i₀ + k) = (x_k + c_k) * (y_k + c_k) := … -- products
refine ⟨?_, ?_⟩
· intro i; obtain ⟨iv, hiv⟩ := i; cases iv with
  | zero => simp only [Nat.zero_mod, reduceIte, circuit_norm]; …; rw [hp0]; ring
  | succ n => simp only [Nat.mod_eq_of_lt hiv, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
                Nat.mod_eq_of_lt (show n < 31 by omega), circuit_norm]
              rw [henvp (n + 1) hiv, henv n (by omega)]; ring
· … (carry family, needs the `hunf` rfl-unfolding of `carryVal (n+1+1)`)
```
The general-C `Add32.completeness` (`Add32.lean:245-287`) has **one** `henv` and **one** goal family; canonical has two of each. Recurring simp set for the mod/if normalization:
```lean
simp only [Nat.mod_eq_of_lt hiv, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
  Nat.mod_eq_of_lt (show n < 31 by omega), circuit_norm]
```

---

### 3.3 `mainCost` / `CostIs`

#### K1 — leaf gadget: `unfold main` + `hcount` reassociation + `CostIs.bind` chain
Exact template (`SHA256CompressGF2Canonical/Cost.lean:56-66` for `Add32Canon`):
```lean
theorem costIs_main (b : Var Inputs (F p2)) : CostIs (main b) ⟨62, 62⟩ := by
  unfold main
  have hcount : (⟨31, 0⟩ + (⟨31, 0⟩ + (⟨31 * 0, 31 * 1⟩ + (⟨31 * 0, 31 * 1⟩ + ⟨0, 0⟩))) : Count) = ⟨62, 62⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector 31 _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector 31 _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun i m => CostIs.assertZero _ m) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun i m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.pure _
```
The `hcount` shape is **literally the same three lines** in 9 places:
```lean
show (⟨_, _⟩ : Count) = _; congr 1
```
Instances: `Cost.lean:58-60` (62/62), `:160-162` `Ch32Canon` (⟨32,0⟩+(⟨32*0,32*1⟩+⟨0,0⟩)=⟨32,32⟩), `:226-228` `Maj32Canon`, `:316-318` `Pin32Canon`, `:528-530` `Pin256Canon` (256), `Blake3/Cost.lean:43-48,126-129,180-183` (`Add32Canon` 62, `Pin32Canon` 32, `PinStateCanon` 512), and the general-C `SHA256CompressGF2/Cost.lean:30-32,112-114,149-151,186-188,474-476`.
**Why the `congr 1`:** the LHS is a `Count.add` tree of numerals; `congr 1` reduces the structure equality to two `ℕ` numeral equalities which `rfl`/`decide` closes.

#### K2 — composite gadget: **term-mode `CostIs.bind` chain with the un-reassociated sum as an ascription**
`Cost.lean:374-379` (`ScheduleStepCanon`):
```lean
theorem costIs_main (b : Var (fields 128) (F p2)) : CostIs (main b) ⟨218, 218⟩ :=
  fun n => (CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Add32Canon.costIs_sub _) fun _ =>
    CostIs.bind (Pin32Canon.costIs_sub _) fun _ =>
    CostIs.pure _ : CostIs (main b) (⟨62, 62⟩ + (⟨62, 62⟩ + (⟨62, 62⟩ + (⟨32, 32⟩ + ⟨0, 0⟩))))) n
```
`Cost.lean:417-431` (`RoundCanon`, 11 binds), same shape with
`(⟨32,32⟩ + (⟨32,32⟩ + (⟨62,62⟩ + (⟨62,62⟩ + (⟨62,62⟩ + (⟨62,62⟩ + (⟨62,62⟩ + (⟨62,62⟩ + (⟨62,62⟩ + (⟨32,32⟩ + (⟨32,32⟩ + ⟨0,0⟩))))))))))`.
**Why the `fun n => (… : CostIs … <sum>) n`:** eta-expanding at the offset `n` and *ascribing the un-normalized nested sum* lets the elaborator unify by definitional numeral evaluation instead of by `rw`. The BLAKE3 file drops the ascription entirely where numerals collapse definitionally (`Blake3/Cost.lean:229-230`):
```lean
theorem costIs_main (b : Var Add32.Inputs (F p2)) : CostIs (main b) ⟨94, 94⟩ :=
  CostIs.bind (Add32Canon.costIs_sub b) fun _ => Pin32Canon.costIs_sub _
```

#### K3 — fold/map gadget: `CostIs.foldlRange` with the named `constant` instance
`Cost.lean:568-572` (`Sched16Canon`):
```lean
theorem costIs_main (b : Var (fields 512) (F p2)) : CostIs (main b) ⟨3488, 3488⟩ := by
  unfold main
  exact CostIs.bind (CostIs.foldlRange (constant := constantLength)
      fun _ _ n => (CostIs.bind (ScheduleStepCanon.costIs_sub _) fun _ => CostIs.pure _) n)
    fun _ => CostIs.pure _
```
`Cost.lean:648-650` (`Rounds16Canon`):
```lean
CostIs.bind (CostIs.foldlRange (constant := constantLength r0 b) fun _ _ n => RoundCanon.costIs_sub _ _ n) fun _ =>
  Pin256Canon.costIs_sub _
```
`Main.lean:150`: `CostIs.bind (CostIs.mapFinRange fun _ _ => Add32Canon.costIs_sub _ _) fun _ => …`

#### K4 — `costIs_sub` boilerplate (present for **every** gadget, always identical)
```lean
theorem costIs_sub (b : …) : CostIs (subcircuit circuit b) ⟨N, N⟩ := CostIs.subcircuit (fun n => costIs_main b n)
```

#### K5 — top-level `mainCost`
`SHA256CompressGF2Canonical/Main.lean:139-152`:
```lean
theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := by
  intro input
  exact
    (CostIs.bind (Sched16Canon.costIs_sub _) fun _ => … ×3
     CostIs.bind (Rounds16Canon.costIs_sub _ _) fun _ => … ×4
     CostIs.bind (CostIs.mapFinRange fun _ _ => Add32Canon.costIs_sub _ _) fun _ =>
     CostIs.pure _ : CostIs (main input) ⟨allocations, constraints⟩)
```
`Blake3/Cost.lean:536-544` + `Blake3/Main.lean:20-22` (`simpa [allocations, constraints] using mainCostInternal`) — BLAKE3 splits `mainCostInternal` into `Cost.lean` and re-exports through `Main.lean`.

---

### 3.4 `isR1CS_Cidentity` / `IsCidCirc`

#### I1 — **Leaf gadget: `isCidentity_ops` inside a `attribute [local semireducible]` section**
The universal opener (`Cost.lean:71-72`, `:170-171`, `:236-237`, `:290-291`, `:502-503`, `Blake3/Cost.lean:61`, `:140`, `:194`):
```lean
section
attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid
```
**Why:** the Spec marks the first two `irreducible` (`CostR1CSCanonicalSpec.lean:92`) and the machinery marks `operationsIsCid` `irreducible` (`CostR1CSCanonical.lean:304`) to stop `whnf` from materializing ~48 k operations. Leaf certificates must re-enable them locally.

Full leaf template (`Cost.lean:173-190`, `Ch32Canon`):
```lean
theorem isCidentity_ops (b : Var (fields 96) (F p2)) (hb : AffineW b) :
    ∀ n, operationsIsCid n ((main b).operations n) := by
  intro n
  unfold main
  rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 32 _ n]
  refine ⟨operationsIsCid_witnessVector 32 _ _ _, ?_⟩
  rw [Circuit.bind_operations_eq, operationsIsCid_append,
    (CostIs.forEach fun i m => CostIs.assertZero _ m) _]
  refine ⟨?_, operationsIsCid_pure _ _ _⟩
  rw [Circuit.forEach.operations_eq]
  refine operationsIsCid_flatten_ofFn (L := 1)
    (fun i => (CostIs.assertZero _).constraints _) fun i => ?_
  simp only [Vector.getElem_finRange]
  simp only [Nat.mul_one]
  refine ⟨?_, trivial⟩
  rw [wv_getElem]
  exact isCidentityRowAt_var_sub_mul (a96_affine hb _) (Affine.add (a96_affine hb _) (a96_affine hb _))
```
**Step-by-step why:**
1. `rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector 32 _ n]` — split the ops list at the bind, and *supply the constraint-count of the left half* (`CostIs.witnessVector` returns `⟨32,0⟩`, so the pin counter is unchanged) so the `k + (operationCount ops₁).constraints` in `operationsIsCid_append` becomes a closed numeral.
2. `operationsIsCid_witnessVector` — witnesses do not advance the counter, `trivial`-level.
3. `(CostIs.forEach fun i m => CostIs.assertZero _ m) _` — same trick for the assert loop (`⟨0, 32⟩`).
4. `Circuit.forEach.operations_eq` + `operationsIsCid_flatten_ofFn (L := 1)` — each `forEach` iteration is 1 constraint, so iteration `i` pins `n + i·1`.
5. `simp only [Nat.mul_one]` — normalize `i.val * 1`.
6. `rw [wv_getElem]` / `rw [at31_wv, Nat.mod_eq_of_lt i.isLt]` — turn `w[i]` (or `at31 prods i`) into the literal `Expression.var ⟨n + i⟩` that `isCidentityRowAt_var_sub_mul` expects.
7. `exact isCidentityRowAt_var_sub_mul hA hB` — the row builder.

Builder (`CostR1CSCanonical.lean:32-35`):
```lean
theorem isCidentityRowAt_var_sub_mul {k : ℕ} {A B : Expression F}
    (hA : Affine A) (hB : Affine B) :
    isCidentityRowAt k ((Expression.var ⟨k⟩ : Expression F) - A * B) := ⟨A, B, hA, hB, rfl⟩
```

**Per-leaf `A`/`B` arguments (the whole GF(2) gate table):**

| Gadget | Row expression | `A` proof | `B` proof | file:line |
|---|---|---|---|---|
| `Ch32Canon` | `pᵢ − eᵢ·(fᵢ⊕gᵢ)` | `a96_affine hb _` | `Affine.add (a96_affine hb _) (a96_affine hb _)` | `Cost.lean:189-190` |
| `Maj32Canon` | `pᵢ − (aᵢ+cᵢ)·(bᵢ+cᵢ)` | `Affine.add (a96_affine hb _) (a96_affine hb _)` | ditto | `Cost.lean:255-257` |
| `Pin32Canon` | `wᵢ − vᵢ·1` | `b32_affine hb _` | **`Affine.one`** | `Cost.lean:310` |
| `Pin256Canon` | `wᵢ − vᵢ·1` | `b256_affine hb _` | **`Affine.one`** | `Cost.lean:522` |
| `Add32Canon` product row | `dᵢ − (xᵢ+cᵢ)(yᵢ+cᵢ)` | `Affine.add (hx _ …) (carryE_affine (affineW_witnessVector_output 31 _ _) i.val)` | same with `hy` | `Cost.lean:96-100` |
| `Add32Canon` carry row | `cᵢ₊₁ − (cᵢ+dᵢ)·1` | `Affine.add (carryE_affine …) (at31_affine …)` | **`Affine.one`** | `Cost.lean:112-115` |
| Blake3 `Pin32Canon` | `wᵢ − vᵢ·1` | `b32_affine hb _` | `Affine.one` | `Blake3/Cost.lean:157` |
| Blake3 `PinStateCanon` | `wᵢ − vᵢ·1` | `b512_affine hb _` | `Affine.one` | `Blake3/Cost.lean:212` |

`Affine.one` is defined solution-adjacent in `CostR1CSCanonical.lean:29`: `theorem Affine.one : Affine (1 : Expression F) := Affine.const 1`.

#### I2 — **Composite gadget: `IsCidCirc.bind_out` chain, each step carrying `balanced_sub` + the affineness of the previous output**
`Cost.lean:384-400` (`ScheduleStepCanon`) — canonical form:
```lean
theorem isCidentity_main (b : Var (fields 128) (F p2)) (hb : AffineW b) : IsCidCirc (main b) := by
  have h1 : AffineW (lowerSigma1E (w128 b 3)) := lowerSigma1E_affine (w128_affine hb 3)
  have h0 : AffineW (lowerSigma0E (w128 b 1)) := lowerSigma0E_affine (w128_affine hb 1)
  have hw2 : AffineW (w128 b 2) := w128_affine hb 2
  have hw0 : AffineW (w128 b 0) := w128_affine hb 0
  unfold main
  refine IsCidCirc.bind_out (add32canon_cid _ _ h1 hw2) (Add32Canon.balanced_sub _) fun n1 => ?_
  refine IsCidCirc.bind_out (add32canon_cid _ _ h0 hw0) (Add32Canon.balanced_sub _) fun n2 => ?_
  refine IsCidCirc.bind_out
    (add32canon_cid _ _ (affineW_out_add32canon _ _ h1 hw2 n1) (affineW_out_add32canon _ _ h0 hw0 n2))
    (Add32Canon.balanced_sub _) fun n3 => ?_
  refine IsCidCirc.bind (Pin32Canon.isCidentity_sub _ (affineW_out_add32canon _ _ (…) (…) n3))
    (Pin32Canon.balanced_sub _) fun _ => ?_
  exact IsCidCirc.pure _
```
`Cost.lean:437-480` (`RoundCanon`) — the 11-step version, interleaving `have haN := affineW_out_add32canon …` after each bind so the next bind's affineness argument is available.

Combinators (`CostR1CSCanonical.lean:259-272`):
```lean
theorem IsCidCirc.bind {f : Circuit F α} {g : α → Circuit F β}
    (hf : IsCidCirc f) (hbal : Balanced f) (hg : ∀ a, IsCidCirc (g a)) : IsCidCirc (f >>= g) :=
  IsCidCirc.of_ops fun n => by
    rw [Circuit.bind_operations_eq, operationsIsCid_append, hbal n]
    exact ⟨hf.ops n, (hg _).ops _⟩

theorem IsCidCirc.bind_out {f : Circuit F α} {g : α → Circuit F β}
    (hf : IsCidCirc f) (hbal : Balanced f) (hg : ∀ n, IsCidCirc (g (f.output n))) : IsCidCirc (f >>= g) :=
  IsCidCirc.of_ops fun n => by
    rw [Circuit.bind_operations_eq, operationsIsCid_append, hbal n]
    exact ⟨hf.ops n, (hg n).ops (n + f.localLength n)⟩
```
**Why `hbal` is essential:** `operationsIsCid_append` produces a residual counter `k + (operationCount ops₁).constraints`, whereas the offset advances by `f.localLength n`. `Balanced` says these are equal — this is the *entire reason* canonicality needs a cost certificate.

**`bind` vs `bind_out`:** `bind_out` is used when the continuation's certificate depends on the previous output (needing `f.output n`); plain `bind` when the continuation ignores it (last step / `IsCidCirc.pure`).

#### I3 — **`isCidentity_sub` boilerplate** (two variants)
- Leaf: `IsCidCirc.subcircuit (isCidentity_ops b hb)` (`Cost.lean:125,200,267,332,544`; `Blake3/Cost.lean:103,163,218`)
- Composite: `IsCidCirc.subcircuit (isCidentity_main b hb).ops` (`Cost.lean:404,484,614,685`; all of `Blake3/Canonical.lean`)

The `.ops` accessor (`CostR1CSCanonical.lean:219-221`) converts `IsCidCirc c` back to `∀ n, operationsIsCid n (c.operations n)`, which is what `IsCidCirc.subcircuit` (`:274-286`) consumes.

#### I4 — **`balanced_sub` boilerplate — identical 3 lines in every namespace**
```lean
theorem balanced_sub (b : …) : Balanced (subcircuit circuit b) :=
  Balanced.of_costIs (costIs_sub b) fun n => by
    simp [circuit_norm, subcircuit, circuit, elaborated]
```
Occurrences: `SHA256.../Cost.lean:128-130, 202-204, 269-271, 334-336, 406-408, 486-489, 546-548, 616-618, 687-690`; `Blake3/Cost.lean:105-108, 165-168, 220-223, 236-239, 253-256, 273-276, 294-297, 315-318, 331-334, 348-351, 372-378, 393-396, 411-414, 427-430, 445-448, 463-466, 479-482, 495-498, 513-516, 529-532`. **20 identical instances in BLAKE3 alone.**

#### I5 — **`IsCidCirc.foldlRange_inv` (solution-side combinator)**
Defined in `SHA256CompressGF2Canonical/Theorems.lean:22-43` because *the trusted `IsCidCirc` has no fold combinator*:
```lean
theorem IsCidCirc.foldlRange_inv {β : Type} {m : ℕ} [Inhabited β] {init : β}
    {body : β → Fin m → Circuit F β} {constant : Circuit.ConstantLength fun (t : β × Fin m) => body t.1 t.2}
    {L : ℕ}
    (P : β → Prop) (hinit : P init)
    (hlen : ∀ i : Fin m, (body default i).localLength = L)
    (hbal : ∀ s (i : Fin m) n, P s → (operationCount ((body s i).operations n)).constraints = L)
    (hbody : ∀ s i, P s → IsCidCirc (body s i))
    (hstep : ∀ s (i : Fin m) n, P s → P ((body s i).output n)) :
    IsCidCirc (Circuit.foldlRange m init body constant) := by
  refine IsCidCirc.of_ops fun n => ?_
  rw [Circuit.foldlRange.operations_eq]
  have hacc : ∀ i : Fin m, P (Circuit.FoldlM.foldlAcc n (Vector.finRange m) body init i) := by
    intro i; rw [Circuit.FoldlM.foldlAcc]; apply finFoldl_invariant P _ _ hinit
    intro acc j hacc; exact hstep acc _ _ hacc
  refine operationsIsCid_flatten_ofFn (L := L) (fun i => hbal _ i _ (hacc i)) fun i => ?_
  rw [hlen i]
  exact (hbody _ i (hacc i)).ops _
```
And `IsCidCirc.mapFinRange` (`Theorems.lean:46-56`) with `(hlen : (body 0).localLength = L)` and `(hbal : ∀ (i : Fin m) n, (operationCount ((body i).operations n)).constraints = L)`.

**Delta vs the general-C `IsR1CSCirc.foldlRange_inv`** (`CostR1CS.lean:519`, used at `SHA256CompressGF2/Cost.lean:575-593`): the canonical version takes **two extra arguments** — `hlen` (the constant `localLength`) and `hbal` (the per-iteration constraint count) — because the ordered pins need `n + i·L` alignment.

Usage (`Cost.lean:577-610`, `Sched16Canon`):
```lean
theorem isCidentity_main (b : Var (fields 512) (F p2)) (hb : AffineW b) : IsCidCirc (main b) := by
  rw [main]
  apply IsCidCirc.bind_out
  · refine IsCidCirc.foldlRange_inv (constant := constantLength) (L := 218)
      (fun w => ∀ k (hk : k < 32), AffineW (w[k]'hk)) ?_ ?_ ?_ ?_ ?_
    · intro k hk                                    -- hinit: buffer of input words ++ zeros
      show AffineW (((Vector.ofFn fun j : Fin 16 => q512 b j.val) ++ Vector.replicate 16 (Vector.replicate 32 (0 : Expression (F p2))))[k]'hk)
      rw [Vector.getElem_append]
      split
      · rw [Vector.getElem_ofFn]; exact q512_affine hb _
      · rw [Vector.getElem_replicate]; intro j hj; rw [Vector.getElem_replicate]; exact Affine.zero
    · intro i                                       -- hlen
      simp [circuit_norm, ScheduleStepCanon.circuit, ScheduleStepCanon.elaborated]
    · intro w i n hw                                -- hbal
      exact (CostIs.bind (ScheduleStepCanon.costIs_sub _) fun _ => CostIs.pure _).constraints n
    · intro w i hw                                  -- hbody
      exact IsCidCirc.bind_out (ScheduleStepCanon.isCidentity_sub _
        (c128_affine (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega))))
        (ScheduleStepCanon.balanced_sub _) (fun _ => IsCidCirc.pure _)
    · intro w i n hw k hk                           -- hstep (invariant preservation through Vector.set)
      simp only [circuit_norm, Vector.getElem_set]
      split
      · exact affineW_varFromOffset _ _
      · exact hw _ _
  · exact fun n => Balanced.of_costIs (CostIs.foldlRange (constant := constantLength) …) (fun n' => by
      simp [circuit_norm, ScheduleStepCanon.circuit, ScheduleStepCanon.elaborated, Count.zero]) n
  · exact fun n => IsCidCirc.pure _
```
`Rounds16Canon` version (`Cost.lean:665-681`) uses invariant `(fun s => AffineW s)` with `(L := 562)`.

#### I6 — `IsCidCirc.mapFinRange` at top level
`Main.lean:178-187`:
```lean
refine IsCidCirc.bind (IsCidCirc.mapFinRange (L := 62)
  (by simp [circuit_norm, Add32Canon.circuit, Add32Canon.elaborated])
  (fun i n => (Add32Canon.costIs_sub _).constraints n)
  (fun i => add32canon_cid _ _ (w256_affine hh i.val) (w256_affine (Rounds16Canon.affineW_subOut 48 _ p4) i.val)))
  ?_ fun _ => ?_
· exact Balanced.of_costIs (CostIs.mapFinRange fun i n => Add32Canon.costIs_sub _ n)
    (fun n => by simp [circuit_norm, Add32Canon.circuit, Add32Canon.elaborated])
· exact IsCidCirc.pure _
```
`CostIs.constraints` accessor used as `(costIs_sub _).constraints n` — from `CostR1CSCanonical.lean:237-239`:
```lean
theorem CostIs.constraints {c : Circuit F α} {K : Count} (h : CostIs c K) (n : ℕ) :
    (operationCount (c.operations n)).constraints = K.constraints := congrArg Count.constraints (h n)
```

#### I7 — **Top-level assembly** `isR1CS_Cidentity_of_IsCidCirc`
`Main.lean:157-194` (SHA-256). Note the elaboration hint:
```lean
set_option maxRecDepth 8000 in
theorem isR1CS_Cidentity : Challenge.CostR1CS.isR1CS_Cidentity main :=
  isR1CS_Cidentity_of_IsCidCirc
  (fun input hinput => by
    have hh : AffineW input.h := affineW_input_h hinput
    have hm : AffineW input.m := affineW_input_m hinput
    unfold main
    refine IsCidCirc.bind_out (Sched16Canon.isCidentity_sub _ hm) (Sched16Canon.balanced_sub _) fun m1 => ?_
    … 7 more binds …
    · exact Balanced.of_costIs (CostIs.mapFinRange …) (fun n => by simp […])
    · exact IsCidCirc.pure _)
  (fun input hinput n => by                              -- the AffineOutput half
    have hh : AffineW input.h := affineW_input_h hinput
    intro i hi
    have hi256 : i < 256 := by have hsz : size Output = 256 := rfl; omega
    simp only [main, Circuit.bind_output_eq, Circuit.pure_output_eq,
      Circuit.mapFinRange.output_eq, Vector.getElem_mapFinRange]
    exact out256_add32canon_affine hh (Rounds16Canon.affineW_subOut 48 _ _) _ _ _ _ _ _ _ _ i hi256)
```
BLAKE3 version `Blake3/Canonical.lean:776-801` — same skeleton, `AffineOutput` half is much shorter because the output is a single pinned block:
```lean
(fun input _ n => by
  intro i hi
  have hi512 : i < 512 := by have hsz : size Output = 512 := rfl; omega
  rw [show (toElements (M := Output) ((main input).output n))[i] = ((main input).output n).bits[i]'hi512 from rfl, output_bits_eq]
  exact affineW_varFromOffset 512 _ i hi512)
```

#### I8 — **BLAKE3's `output_*_eq : … = varFromOffset … := rfl` ladder**
`Blake3/Canonical.lean:330-345, 387-402, 427-444, 469-471, 500-506, 528-531, 553-556, 576-579, 614-620, 647-655, 676-684, 705-713, 739-747, 765-767, 771-774`.
Pattern:
```lean
theorem output_a_eq (b : Var GInputs (F p2)) (n : ℕ) :
    ((subcircuit circuit b).output n).a = (varFromOffset (fields 32) (n + 346) : Var (fields 32) (F p2)) := rfl
```
Then used as `rw [G.output_a_eq]; exact affineW_varFromOffset _ _` inside the next `isCidentity_main`.
**Why:** because every composite ends in a *pin*, the output is literally a fresh `varFromOffset`. Stating it as `rfl` lets the affineness obligation of the next gadget collapse to `affineW_varFromOffset`, avoiding any structural reasoning about the deep composed circuit. This is BLAKE3's core scaling trick: `Canonical.lean:6-8` — *"Every composite boundary is pinned. Consequently, the only nontrivial affineness obligations are the pure word/state selections feeding the next canonical subcircuit."*

Note the *unnormalized offset arithmetic* is deliberate: `n + 5840 + 2920 + 1460 + 948`, `n + 48768 + 24384 + 11168` — these are kept in the compositional decomposition form so `rfl` succeeds directly.

#### I9 — **AffineW projection from `AffineProvable` via append splitting**
`Blake3/Canonical.lean:130-170` — 6 near-identical lemmas:
```lean
theorem affineW_quad_a {q : Var Quad (F p2)} (hq : AffineProvable q) : AffineW q.a := by
  have hflat : AffineW (q.a ++ (q.b ++ (q.c ++ q.d))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type] using hq i hi
  exact hflat.left_of_append
```
`…_b`: `hflat.right_of_append.left_of_append`; `…_c`: `.right_of_append.right_of_append.left_of_append`; `…_d`: three `.right_of_append`. Also `affineW_config_state`/`affineW_config_block` (2-field).
SHA-256 index-arithmetic variant (`SHA256CompressGF2/Cost.lean:756-769`):
```lean
theorem affineW_input_h {input : Var Input (F p2)} (hinput : AffineProvable input) : AffineW input.h := by
  intro i hi
  have hi256 : i < 256 := hi
  have hsz : size Input = 768 := rfl
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz, hi] using hinput i (by omega)

theorem affineW_input_m … := by
  … simpa […] using hinput (256 + i) (by omega)      -- note the +256 offset
```
Blake3 single-field: `affineW_input_bits` (`Canonical.lean:122-128`).

#### I10 — **`AffineW` for pure wiring maps: `intro i hi; unfold f; rw [Vector.getElem_ofFn]; split; …`**
The universal shape. Exhaustive list from `SHA256CompressGF2/Cost.lean`:
`a96_affine`, `b32_affine`, `b512_affine`, `a256_affine`, `a128_affine`, `a288_affine`, `a768_affine`, `b256_affine` (all one-liners `hv _ (Nat.mod_lt _ (by norm_num))`);
`c96_affine`, `c128_affine`, `c288s_affine`, `c768_affine`, `outState_affine` (with `split`);
`w128_affine`, `w288_affine`, `w256_affine`, `q512_affine`, `q768_affine`, `st768_affine` (with `Vector.getElem_ofFn`);
`rotrE_affine`, `shrE_affine` (with `split` for the out-of-range `0`), `xor3E_affine`;
`lowerSigma0E_affine`, `lowerSigma1E_affine`, `upperSigma0E_affine`, `upperSigma1E_affine` (all pure compositions, e.g. `xor3E_affine (rotrE_affine hv 7) (rotrE_affine hv 18) (shrE_affine hv 3)`);
`constW_affine` (`exact Affine.const _`);
`c512_affine`, `c512sel_affine` (a **17-case pattern-match term**, `| 0 => h0 | … | (_ + 15) => h15`), `c512x_affine`, `o8sel_affine` (`| (_ + 7) => h7`), `out256_affine`.

Canonical-only additions in `SHA256CompressGF2Canonical/Cost.lean`:
`zxorOut_affine` (`:145-150`), `affineW_subOut_ch32canon`/`_maj32canon` (`:213-216`, `:279-282`) — which unlike the general-C versions must use `zxorOut_affine hv (affineW_mapRange_var _)` since the output is *not* a bare witness vector.

BLAKE3 versions in `Canonical.lean:18-120`: `affineW_xorWord`, `affineW_rotRight`, `affineW_stateWord`, `affineW_setWord`, `affineW_writeQuad` (nested `apply affineW_setWord` ×4), `affineW_permuteState`, `affineW_finalizeState`, `affineW_initialStateBits`, `affineW_initialBlockBits`.

---

### 3.5 `computableWitness`

#### W1 — **Leaf gadget: `change` + `forAllFlat_of_structuralComputableWitnesses` + the fixed `simp only` set**
Verbatim in **every** leaf (`Ch32Canon.lean:73-92`, `Maj32Canon`, `Pin32Canon`, `Pin256Canon`, `Add32Canon`, `Add32`, `Ch32`, `Maj32`, `Pin32`, `Pin256`, `Blake3/PinCanon.lean` ×2, `Blake3/Add32Canon.lean`):
```lean
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [
    Circuit.bind_structuralComputableWitnesses_iff,
    Circuit.witnessVector_structuralComputableWitnesses_iff,
    Circuit.forEach_structuralComputableWitnesses_iff,
    Circuit.assertZero_structuralComputableWitnesses_iff,
    Circuit.pure_structuralComputableWitnesses_iff,
    and_true]
  and_intros
  · intro _ h_input
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_ofFn, a96, circuit_norm, eval_getElem_congr h_input]
  · intro _
    trivial
```
The witness-generator goal is discharged by rewriting with `eval_getElem_congr h_input` (pointwise agreement); the assert goals by `trivial`.
`Add32Canon` variant (`:240-252`) uses **`simp only [eval_at32_pt_congr (Add32.eval_x_congr h_input), eval_at32_pt_congr (Add32.eval_y_congr h_input)]`** instead of `Vector.ext`, with helper (`:220-224`):
```lean
theorem eval_at32_pt_congr {v : Var (fields 32) (F p2)} {env env' : ProverEnvironment (F p2)}
    (h : eval env v = eval env' v) (j : ℕ) :
    Expression.eval env.toEnvironment (at32 v j) = Expression.eval env'.toEnvironment (at32 v j) :=
  eval_getElem_congr h _ _
```
Doc note (`:217-219`): *"The canonical adder's product generator reads `at32 x i` directly as well as through `carryVal`, so the function-level `Add32.eval_at32_fun_congr` does not suffice."* — **canonical/general delta**: the general `Add32` uses the *function-level* `eval_at32_fun_congr` (funext) at `Add32.lean:317-321,339`; the canonical one needs the *pointwise* version.

#### W2 — **Composite gadget: subcircuit simp set + one goal per subcircuit**
```lean
simp only [
  Circuit.bind_structuralComputableWitnesses_iff,
  FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
  Circuit.pure_structuralComputableWitnesses_iff,
  Ch32Canon.subcircuit_localLength, Maj32Canon.subcircuit_localLength,
  Add32Canon.subcircuit_localLength, Pin32Canon.subcircuit_localLength,
  and_true]
refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
```
(`RoundCanon.lean:118-125`, 11 goals; `ScheduleStepCanon.lean:85-91`, 4 goals; `Blake3` composites throughout `Witness.lean`.)
**The `*.subcircuit_localLength` lemmas are indispensable simp lemmas here** — they turn the symbolic offset chain into numerals so the `by omega` side conditions close.

Two goal shapes:
- **First subcircuit** (only depends on the input): `FormalCircuit.subcircuit_flatStructuralComputableWitnesses`
  ```lean
  exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    Ch32Canon.circuit input _ (offset)
    (fun _ _ h => eval_c96_congr (eval_w288_congr h 4) (eval_w288_congr h 5) (eval_w288_congr h 6))
    Ch32Canon.computableWitnesses env env'
  ```
- **Later subcircuits** (depend on earlier outputs): `..._of_condition`
  ```lean
  refine FormalCircuit.subcircuit_flatStructuralComputableWitnesses_of_condition
    Add32Canon.circuit input _ _ ?_ Add32Canon.computableWitnesses env env'
  intro kk e e' hle h_agree h_input
  have hch := Ch32Canon.eval_subOut_of_agreesBelow (c96 …) (offset) (by omega) h_agree (eval_c96_congr …)
  have ht1a := Add32Canon.eval_subOut_of_agreesBelow _ (offset + 32 + 32) (by omega) h_agree (Add32.eval_mk_congr …)
  exact Add32.eval_mk_congr ht1a hch
  ```
**The `have`-cascade is re-derived from scratch in every goal** (RoundCanon.lean:141-271 re-proves `hch`, `ht1a`, `ht1b`, `ht1c`, `ht1`, `ht2` up to 6× with growing prefixes) — 130 lines of deliberate redundancy. Offsets are literal accumulations: `offset + 32 + 32 + 62`, `offset + 32 + 32 + 62 + 62`, … (canonical) vs `offset + 32 + 32 + 31`, … (general-C, `Round.lean:383+`).

#### W3 — **`eval_subOut_of_agreesBelow` — the per-gadget output-locality lemma**
The single most-repeated theorem name in the corpus. Three variants by output shape:

(a) **Output is a bare pin block** — 3 lines:
```lean
theorem eval_subOut_of_agreesBelow (v : …) (n : ℕ) {k : ℕ} (hk : n + 218 ≤ k)
    {env env' : ProverEnvironment (F p2)} (h_agree : env.AgreesBelow k env') :
    eval env ((subcircuit circuit v).output n) = eval env' ((subcircuit circuit v).output n) := by
  have hout : (subcircuit circuit v).output n = varFromOffset (fields 32) (n + 186) := rfl
  rw [hout]
  exact eval_varFromOffset_of_agreesBelow h_agree (by omega)
```
(`ScheduleStepCanon.lean:121-128` rel-186; `Rounds16Canon.lean:114-121` rel-8992; `Pin32Canon`, `Pin256Canon`, `Ch32`, `Maj32`, `Pin32`, `Pin256`, all of `Blake3/Witness.lean`.)

(b) **Output mixes input with own witnesses** — needs `h_input` too:
- `Add32Canon.lean:259-274`: hout is a 32-entry `Vector.ofFn (… at32 x + at32 y + carryE (Vector.mapRange 31 fun j => var ⟨n + 31 + j⟩) …)`, closed by `eval_fields_of_getElem` + three `eval_getElem_congr` + `Add32.eval_carryE_of_agreesBelow (n + 31) (by omega) h_agree i`. **Note the `n + 31`**: canonical witnesses products first, carries second — the general `Add32` uses `n` (`Add32.lean:376-377`).
- `Ch32Canon.lean:99-107` / `Maj32Canon.lean:98-106`: `hout : … = zxorOut v (varFromOffset (fields 32) n)`, closed by `eval_zxorOut_congr h_input (eval_varFromOffset_of_agreesBelow h_agree (by omega))`.
- `RoundCanon.lean:278-291`: `hout : … = outState (varFromOffset (fields 32) (n + 498)) (varFromOffset (fields 32) (n + 530)) v`, closed by `eval_outState_congr`. (General-C `Round.lean:483-496`: offsets `n + 281`, `n + 313`.)

(c) **Output is a struct of pins** — `eval_config_mk_congr`/`eval_quad_mk_congr` fan-out (`Blake3/Witness.lean:353-368, 803-816, 847-859, 887-899, 927-939`).

Base lemma (`SHA256CompressGF2/EvalCongr.lean:50-57` and identically `Blake3/EvalCongr.lean:50-57`):
```lean
theorem eval_varFromOffset_of_agreesBelow {m offset k : ℕ}
    (h_agree : env.AgreesBelow k env') (hk : offset + m ≤ k) :
    eval env (varFromOffset (fields m) offset : Var (fields m) (F p2))
      = eval env' (varFromOffset (fields m) offset : Var (fields m) (F p2)) := by
  refine eval_fields_of_getElem fun i hi => ?_
  rw [ProvableType.varFromOffset_fields]
  simp only [circuit_norm]
  exact h_agree (offset + i) (by omega)
```

#### W4 — **`attribute [local irreducible]` before the loop/top-level peel**
- `Main.lean:202-203`: `attribute [local irreducible] Sched16Canon.circuit Rounds16Canon.circuit Add32Canon.circuit main` — comment: *"Keep the unifier from expanding the 47,952-witness circuit while peeling the top-level `do` block; offsets and outputs come from the `rfl` lemmas instead."*
- `Sched16Canon.lean:176`: `attribute [local irreducible] main`
- `Rounds16Canon.lean:125`: `attribute [local irreducible] RoundCanon.circuit Pin256Canon.circuit main`
- `Blake3/Witness.lean:1005-1006`: `attribute [local irreducible] Prepare.circuit Steps7.circuit Finalize.circuit main`

#### W5 — **Top-level `computableWitness`: the `himplies` induction closer**
Identical ~35-line block at `SHA256CompressGF2Canonical/Main.lean:277-312` and `Blake3/Witness.lean:1040-1082`:
```lean
have hflat := FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses input env env' hstruct
unfold FormalCircuitBase.computableWitnessCondition at hflat
rw [← Operations.forAll_toFlat_iff] at hflat ⊢
let targetCondition : Condition (F p2) :=
  { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
apply FlatOperation.forAll_implies (F := F p2) n ?_ hflat
have himplies : ∀ (ops : List (FlatOperation (F p2))) (off : ℕ), n ≤ off →
    FlatOperation.forAll off
      (Condition.implies (FormalCircuitBase.computableWitnessCondition input env env') targetCondition).ignoreSubcircuit ops := by
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
    | assert e => simp only [FlatOperation.forAll, Condition.implies, Condition.ignoreSubcircuit]
                  exact ⟨by intro _; trivial, ih off hoff⟩
    | lookup l => … (same)
    | interact i => … (same)
exact himplies ((main input).operations n).toFlat n (le_refl n)
```
**Why:** the top-level obligation drops the `input`-agreement precondition (given `OnlyAccessedBelow n`), so the per-gadget condition must be *weakened* to `targetCondition` by an induction that supplies `hinput` at each witness.

#### W6 — **`set` to name intermediate outputs in the top-level `hstruct`**
`Main.lean:223-233`:
```lean
set wb1 := (subcircuit Sched16Canon.circuit input.m).output n with hwb1def
set wb2 := (subcircuit Sched16Canon.circuit wb1).output (n + 3488) with hwb2def
set wb3 := (subcircuit Sched16Canon.circuit wb2).output (n + 3488 + 3488) with hwb3def
set s1 := (subcircuit (Rounds16Canon.circuit 0) (c768 input.h input.m)).output (n + 3488 + 3488 + 3488) with hs1def
…
```
Offsets accumulate literally (3488, 9248), matching `*.subcircuit_localLength`.

---

## 4. GF(2) gate encodings and their spec lemmas

### 4.1 XOR — **zero constraints**
`+` in `Expression (F p2)` *is* XOR. Every XOR is an inlined affine expression.
- `xor3E` (`ScheduleStepTheorems.lean:52-53`):
  ```lean
  def xor3E (a b c : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
    Vector.ofFn fun i : Fin 32 => b32 a i.val + b32 b i.val + b32 c i.val
  ```
- Blake3 `xorWord` (`Instances/.../Spec.lean:81-82`): `Vector.ofFn fun i => x[i.val] + y[i.val]`
- Spec lemma: `xor3_bit` (`Theorems.lean:174-177`) — **`by decide`**:
  ```lean
  theorem xor3_bit : ∀ a b c : F p2,
      decide (ZMod.val (a + b + c) = 1)
        = ((decide (ZMod.val a = 1) ^^ decide (ZMod.val b = 1)) ^^ decide (ZMod.val c = 1)) := by decide
  ```
- `val_add_eq_xor : ∀ a b : F p2, ZMod.val (a + b) = ZMod.val a ^^^ ZMod.val b := by decide` (`Theorems.lean:22-23`)

### 4.2 Rotation — **zero constraints, pure re-indexing**
```lean
def rotrE (n : ℕ) (v : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => b32 v (i.val + n)                    -- ScheduleStepTheorems.lean:44-45
def rotRight {α : Type} (x : Word α) (n : ℕ) : Word α :=
  Vector.ofFn fun i => atWord x (i.val + n)                           -- Blake3 Spec.lean:84-85
```
Spec lemma `testBit_rotRight32` (`Theorems.lean:93-114`) — the one genuinely hard bit lemma:
```lean
theorem testBit_rotRight32 (x n i : ℕ) (hx : x < 2 ^ 32) (hi : i < 32) :
    (rotRight32 x n).testBit i = x.testBit ((i + n) % 32) := by
  unfold rotRight32
  set m := n % 32 with hm
  have hhigh : x / 2 ^ m < 2 ^ (32 - m) := by
    apply Nat.div_lt_of_lt_mul
    calc x < 2 ^ 32 := hx
    _ = 2 ^ m * 2 ^ (32 - m) := by rw [← pow_add]; congr 1; omega
  rw [show x % 2 ^ m * 2 ^ (32 - m) + x / 2 ^ m = 2 ^ (32 - m) * (x % 2 ^ m) + x / 2 ^ m by ring,
    Nat.testBit_two_pow_mul_add _ hhigh]
  split
  · rw [Nat.testBit_div_two_pow]; congr 1; omega
  · rw [Nat.testBit_mod_two_pow]
    have : i - (32 - m) < m := by omega
    rw [show (i + n) % 32 = i - (32 - m) by omega]
    simp [this]
```
Plus `rotRight32_lt` (`Theorems.lean:180-195`) — bound preservation, closed with a `calc` + `omega`.

### 4.3 Shift — **zero constraints, re-index + zero-fill**
```lean
def shrE (n : ℕ) (v : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => if i.val + n < 32 then b32 v (i.val + n) else 0   -- ScheduleStepTheorems.lean:48-49
theorem testBit_shr (x n i : ℕ) : (x / 2 ^ n).testBit i = x.testBit (i + n) := Nat.testBit_div_two_pow ..
```

### 4.4 σ/Σ combinators (SHA-256) — **zero constraints**
`ScheduleStepTheorems.lean:55-65`:
```lean
def lowerSigma0E (v) := xor3E (rotrE 7 v) (rotrE 18 v) (shrE 3 v)
def lowerSigma1E (v) := xor3E (rotrE 17 v) (rotrE 19 v) (shrE 10 v)
def upperSigma0E (v) := xor3E (rotrE 2 v) (rotrE 13 v) (rotrE 22 v)
def upperSigma1E (v) := xor3E (rotrE 6 v) (rotrE 11 v) (rotrE 25 v)
```
Two generic bridges (`ScheduleStepTheorems.lean:97-182`), both proved by `Nat.eq_of_testBit_eq` + `by_cases hi : i < 32`:
```lean
theorem toNat_eval_sigShr (env) (v) (r1 r2 s : ℕ) :
    toNat (Vector.map (Expression.eval env) (xor3E (rotrE r1 v) (rotrE r2 v) (shrE s v)))
      = rotRight32 (toNat …) r1 ^^^ rotRight32 (toNat …) r2 ^^^ toNat … / 2 ^ s
theorem toNat_eval_sig3 (env) (v) (r1 r2 r3 : ℕ) : … ^^^ … ^^^ …
```
The four instances are one-liners:
```lean
theorem toNat_eval_lowerSigma0E … := toNat_eval_sigShr env v 7 18 3
theorem toNat_eval_lowerSigma1E … := toNat_eval_sigShr env v 17 19 10
theorem toNat_eval_upperSigma0E … := toNat_eval_sig3 env v 2 13 22
theorem toNat_eval_upperSigma1E … := toNat_eval_sig3 env v 6 11 25
```

### 4.5 AND / `Ch` / `Maj` — **1 constraint per bit**

`Ch32Canon.main` (`Ch32Canon.lean:22-28`):
```lean
def main (v : Var (fields 96) (F p2)) : Circuit (F p2) (Var (fields 32) (F p2)) := do
  let p ← witnessVector 32 (fun env => Vector.ofFn fun i : Fin 32 =>
    (a96 v i.val * (a96 v (32 + i.val) + a96 v (64 + i.val))).eval env)
  Circuit.forEach (Vector.finRange 32) (fun i =>
    assertZero (p[i.val]'i.isLt - a96 v i.val * (a96 v (32 + i.val) + a96 v (64 + i.val))))
  return zxorOut v p
```
Row: `pᵢ − eᵢ·(fᵢ⊕gᵢ) = 0`, output `gᵢ ⊕ pᵢ`. **Canonical vs general delta:** general `Ch32` (`Ch32.lean:17-23`) witnesses the *result* and pins with `(w − gᵢ) − eᵢ·(fᵢ⊕gᵢ)` — C-side is `w − g`, not a bare variable. Canonical must pin `p` alone and **inline** the final XOR into the output:
```lean
def zxorOut (v : Var (fields 96) (F p2)) (p : Var (fields 32) (F p2)) : Var (fields 32) (F p2) :=
  Vector.ofFn fun i : Fin 32 => a96 v (64 + i.val) + p[i.val]'i.isLt      -- Canonical/Theorems.lean:69-71
```
Doc: *"A named def keeps the circuit output opaque so subcircuit affineness does not reduce the whole `ofFn`."*

`Maj32Canon.main` (`Maj32Canon.lean:22-28`): row `pᵢ − (aᵢ+cᵢ)·(bᵢ+cᵢ) = 0`, output `cᵢ ⊕ pᵢ`.

Spec lemmas — **the entire Ch/Maj correctness is 2 `decide`s** (`Theorems.lean:246-255`):
```lean
theorem ch_bit : ∀ e f g : F p2,
    decide (ZMod.val (g + e * (f + g)) = 1)
      = ((decide (ZMod.val e = 1) && decide (ZMod.val f = 1))
          ^^ (!decide (ZMod.val e = 1) && decide (ZMod.val g = 1))) := by decide

theorem maj_bit : ∀ a b c : F p2,
    decide (ZMod.val ((a + c) * (b + c) + c) = 1)
      = (((decide (ZMod.val a = 1) && decide (ZMod.val b = 1))
          ^^ (decide (ZMod.val a = 1) && decide (ZMod.val c = 1)))
          ^^ (decide (ZMod.val b = 1) && decide (ZMod.val c = 1))) := by decide
```
Lifted to words by `ch_words` / `maj_words` (`Theorems.lean:318-363`, pattern S8), whose hypothesis is *exactly the shape produced by the circuit*:
```lean
(hout : ∀ (j : ℕ) (hj : j < 32),
  ZMod.val (out[j]'hj) = ZMod.val ((v[64+j]) + (v[j]) * ((v[32+j]) + (v[64+j]))))
```
so the soundness proof is `refine ch_words input _ fun j hj => ?_` + `linear_combination hc`.

Supporting: `testBit_not32` (`Theorems.lean:258-263`) via `Nat.testBit_two_pow_sub_one`; `testBit_Ch`, `testBit_Maj`, `testBit_Ch_ge`, `testBit_Maj_ge`.

### 4.6 Pin gadgets — copy row, **1 constraint per bit**
```lean
-- Pin32Canon (SHA-256), PinCanon.lean:24-29
def main (v) := do
  let w ← witnessVector 32 (fun env => Vector.ofFn fun i : Fin 32 => (b32 v i.val).eval env)
  Circuit.forEach (Vector.finRange 32) (fun i => assertZero (w[i.val]'i.isLt - b32 v i.val * 1))
  return w
```
vs general `Pin32` (`Pin32.lean:20`): `assertZero (w[i.val]'i.isLt - b32 v i.val)` — **the entire canonical delta is `* 1`**. Doc (`PinCanon.lean:8-12`): *"the ordered identity-C obligation has no linear-row case, so the constant-one `B` must appear in the constraint expression itself. Same cost, same matrices."*
Sizes: `Pin32Canon` 32, `Pin256Canon` 256, Blake3 `Pin32Canon` 32, `PinStateCanon` 512, `PinQuadExact` 128 (4×32).
`Spec` is `out = v` (`Pin32.Spec`, `Blake3/PinCanon.lean:28-29`).
Soundness is 12 lines, closing with `linear_combination hc` after `rw [show Expression.eval env (var { index := i₀ + j }) = env.get (i₀ + j) from rfl]`.

### 4.7 Concatenation / windowing — **zero constraints**
All `Vector.ofFn` with `if`-chains (`ScheduleStepTheorems.lean:27-39`, `MainTheorems.lean:17-40`, `Rounds16Theorems.lean:14-32`, `Sched16Theorems.lean:14-42`):
`c96` (3×32), `c128` (4×32), `c288s` (256 ‖ 32), `c768` (256 ‖ 512), `c512`/`c512x`/`c512sel` (16×32), `out256`/`o8sel` (8×32), `w128`/`w256`/`w288`/`q512`/`q768`/`st768`.
Their `wordAt` bridges: `wordAt_eval_c96_0/1/2`, `wordAt_eval_c128_0/1/2/3`, `wordAt_eval_c512x_sel`, `wordAt_eval_out256_sel`, `wordAt_eval_c288s_state/msg`, `wordAt_eval_st768`, `ofFn_wordAt_c288s`, `ofFn_wordAt_c768_state/sched`, `toNat_eval_q512/q768/w256`.
All proved by `refine wordAt_map_eval_eq_toNat _ x k (by norm_num) ?_` + `unfold` + `rw [Vector.getElem_ofFn]` + `if_pos`/`if_neg (by omega : …)` + `simp only [show (32 * k + j) % 32 = j from by omega]`.

### 4.8 BLAKE3 word ops (Instances/.../Spec.lean:63-101)
```lean
def carry {α} [Zero α] [Add α] [Mul α] (x y : Word α) : ℕ → α
  | 0 => 0
  | i + 1 => let c := carry x y i; (atWord x i + c) * (atWord y i + c) + c
def addWord {α} [Zero α] [Add α] [Mul α] (x y : Word α) : Word α :=
  Vector.ofFn fun i => atWord x i.val + atWord y i.val + carry x y i.val
def xorWord {α} [Add α] (x y : Word α) : Word α := Vector.ofFn fun i => x[i.val] + y[i.val]
def rotRight {α} (x : Word α) (n : ℕ) : Word α := Vector.ofFn fun i => atWord x (i.val + n)
def setWord … / def readQuad … / def writeQuad …
```
The **generic carrier `α`** is deliberate (doc `Spec.lean:65-67`): *"the reference circuit applies this definition both to `F 2` values and to symbolic `Expression (F 2)` terms."*
Bridge `carry_eq` (`Blake3/Theorems.lean:68-74`):
```lean
theorem carry_eq (x y : Word (F p2)) (n : ℕ) : Blake3Bits.carry x y n = Add32.carryVal (atWord x) (atWord y) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Blake3Bits.carry, Add32.carryVal]; rw [ih]
```
`toNat_addWord` (`Blake3/Theorems.lean:76-93`) — a 3-step `calc` chaining `Add32.bitAt_eq`, `Add32.adder_correct`, ending `rfl`.

`XorRotateExact` — 32 constraints total (just the pin), `main n input := Pin32Canon.circuit (rotRight (xorWord input.x input.y) n)`. Soundness (`G.lean:86-91`) is `rw [h_holds, eval_rotRight, eval_xorWord, hx, hy]`. **Rotations used: 16, 12 (GFirst), 8, 7 (GSecond).**

---

## 5. 32-bit modular addition over GF(2)

### 5.1 The carry recurrence (char-2 single-product form)
`SHA256CompressGF2/Add32.lean:11-21` (doc) and `:50-55`:
```lean
def carryVal (xv yv : ℕ → F p2) : ℕ → F p2
  | 0 => 0
  | i + 1 => let c := carryVal xv yv i; (xv i + c) * (yv i + c) + c
```
Doc: *"`c₀ = 0, cᵢ₊₁ = (xᵢ + cᵢ)·(yᵢ + cᵢ) + cᵢ` (equal to the textbook `xᵢyᵢ ⊕ cᵢ(xᵢ ⊕ yᵢ)` because `a² = a` in `F 2`), so each carry is pinned by a **single degree-2 R1CS row**."*
Sum bits `sᵢ = xᵢ ⊕ yᵢ ⊕ cᵢ` are **inlined** (no witnesses). The bit-31 carry-out is dropped, giving mod 2³².
Carry-into-bit expression (`Add32.lean:114-115`):
```lean
def carryE (carries : Vector (Expression (F p2)) 31) (i : ℕ) : Expression (F p2) :=
  if i = 0 then 0 else at31 carries (i - 1)
```

### 5.2 Encoding — general vs canonical

**General (`Add32.lean:119-128`, 31 witnesses / 31 constraints):**
```lean
let carries ← witnessVector 31 (fun env => Vector.ofFn fun i : Fin 31 =>
  carryVal (fun j => (at32 x j).eval env) (fun j => (at32 y j).eval env) (i.val + 1))
Circuit.forEach (Vector.finRange 31) (fun i =>
  assertZero ((at31 carries i.val - carryE carries i.val)
    - (at32 x i.val + carryE carries i.val) * (at32 y i.val + carryE carries i.val)))
return Vector.ofFn fun i : Fin 32 => at32 x i.val + at32 y i.val + carryE carries i.val
```
C-side is `cᵢ₊₁ − cᵢ` — **a two-term affine form, not a single variable** ⇒ fails `isCidentityRowAt`.

**Canonical (`SHA256CompressGF2Canonical/Add32Canon.lean:34-47` ≡ `Blake3CompressGF2Canonical/Add32Canon.lean:32-45`, 62/62):**
```lean
def main (input : Var Inputs (F p2)) : Circuit (F p2) (Var (fields 32) (F p2)) := do
  let x := input.x; let y := input.y
  let prods ← witnessVector 31 (fun env => Vector.ofFn fun i : Fin 31 =>
    let c := carryVal (fun j => (at32 x j).eval env) (fun j => (at32 y j).eval env) i.val
    ((at32 x i.val).eval env + c) * ((at32 y i.val).eval env + c))
  let carries ← witnessVector 31 (fun env => Vector.ofFn fun i : Fin 31 =>
    carryVal (fun j => (at32 x j).eval env) (fun j => (at32 y j).eval env) (i.val + 1))
  Circuit.forEach (Vector.finRange 31) (fun i =>
    assertZero (at31 prods i.val
      - (at32 x i.val + carryE carries i.val) * (at32 y i.val + carryE carries i.val)))
  Circuit.forEach (Vector.finRange 31) (fun i =>
    assertZero (at31 carries i.val - (carryE carries i.val + at31 prods i.val) * 1))
  return Vector.ofFn fun i : Fin 32 => at32 x i.val + at32 y i.val + carryE carries i.val
```
Doc (`:12-23`): *"To keep the carry a single variable (shallow, so subcircuit composition does not blow up `whnf`), we split each bit into two canonical rows: product row `dᵢ − (xᵢ+cᵢ)(yᵢ+cᵢ) = 0`, carry row `cᵢ₊₁ − (cᵢ + dᵢ)·1 = 0`. We witness the 31 products `d₀..d₃₀` and then the 31 carries `c₁..c₃₁`, in the same order the constraint rows pin them."*
**Allocation layout:** `[n .. n+30]` = products, `[n+31 .. n+61]` = carries. This is why `eval_subOut_of_agreesBelow` uses `Vector.mapRange 31 fun j => var ⟨n + 31 + j⟩` and `Add32.eval_carryE_of_agreesBelow (n + 31) …`.

### 5.3 The soundness idiom (canonical, `Add32Canon.lean:57-141`)

**Step 1 — carry-chain induction:**
```lean
have hget : ∀ n : ℕ, n < 31 → env.get (i₀ + 31 + n)
    = carryVal (fun j => Expression.eval env (input_var_x[j % 32]'…))
               (fun j => Expression.eval env (input_var_y[j % 32]'…)) (n + 1) := by
  intro n
  induction n with
  | zero => … have hp0 := h_prod ⟨0, by norm_num⟩; have hc0 := h_carry ⟨0, by norm_num⟩
            simp only [Nat.zero_mod, Nat.add_zero, reduceIte, circuit_norm] at hp0 hc0
            have hunf : carryVal … (0 + 1) = … := rfl
            rw [Nat.add_zero, hunf]; simp only [Nat.zero_mod] at *
            linear_combination hc0 + hp0
  | succ n ih => have hprev := ih (by omega); have hp := h_prod ⟨n+1, hn⟩; have hc := h_carry ⟨n+1, hn⟩
                 simp only [Nat.mod_eq_of_lt hn, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
                   Nat.mod_eq_of_lt (show n < 31 by omega), circuit_norm] at hp hc
                 rw [hprev] at hp hc
                 have hunf : carryVal … (n + 1 + 1) = … := rfl
                 rw [hunf]; linear_combination hc + hp
```
**Key:** `linear_combination hc + hp` — the honest carry is `d + c` and `d` is `(x+c)(y+c)`, so *summing* the two constraint hypotheses yields exactly the recurrence. (General-C: `linear_combination hc` — one row.)

**Step 2 — input bridges `hx`, `hy`** (pattern S3).

**Step 3 — `Finset.sum_congr` sandwich around `adder_correct`:**
```lean
rw [toNat_eq_sum, toNat_eq_sum, toNat_eq_sum]
have key := adder_correct (fun j => Expression.eval env (input_var_x[j % 32]'…))
                          (fun j => Expression.eval env (input_var_y[j % 32]'…))
refine Eq.trans ?_ (Eq.trans key ?_)
· -- LHS: output bits are the inlined sum bits
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj32 := Finset.mem_range.mp hj
  rw [bitAt_eq _ j hj32, Vector.getElem_map, Vector.getElem_ofFn]
  simp only [circuit_norm]
  by_cases hj0 : j = 0
  · subst hj0; simp only [reduceIte, circuit_norm, carryVal]
  · simp only [if_neg hj0]
    rw [show Expression.eval env (var { index := i₀ + 31 + (j - 1) % 31 }) = env.get (i₀ + 31 + (j - 1) % 31) from rfl,
      Nat.mod_eq_of_lt (show j - 1 < 31 by omega), hget (j - 1) (by omega),
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
· -- RHS: the evaluated inputs are the input bit values
  have hXsum : … = ∑ j ∈ Finset.range 32, bitAt input_x j * 2 ^ j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj32 := Finset.mem_range.mp hj
    rw [bitAt_eq _ j hj32]; simp only [Nat.mod_eq_of_lt hj32]; rw [hx j hj32]
  have hYsum : … := … (same)
  rw [hXsum, hYsum]
```
**Note the `i₀ + 31 +` offset — the general-C version uses `i₀ +`.** This is the only textual difference in step 3.

### 5.4 The three pure adder lemmas (identical in both `Add32.lean` and `Blake3/Add32Theorems.lean`)

```lean
theorem fullAdder_val : ∀ a b c : F p2,
    ZMod.val a + ZMod.val b + ZMod.val c = ZMod.val (a + b + c) + 2 * ZMod.val ((a + c) * (b + c) + c) := by decide
```
**8-case `decide` — the entire full-adder correctness.**

```lean
theorem adder_invariant (xv yv : ℕ → F p2) (k : ℕ) :
    (∑ i ∈ Finset.range k, ZMod.val (xv i) * 2 ^ i) + (∑ i ∈ Finset.range k, ZMod.val (yv i) * 2 ^ i)
      = (∑ i ∈ Finset.range k, ZMod.val (xv i + yv i + carryVal xv yv i) * 2 ^ i)
        + ZMod.val (carryVal xv yv k) * 2 ^ k := by
  induction k with
  | zero => simp [carryVal]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hfa := fullAdder_val (xv n) (yv n) (carryVal xv yv n)
    have hstep : carryVal xv yv (n + 1) = (xv n + carryVal xv yv n) * (yv n + carryVal xv yv n) + carryVal xv yv n := rfl
    have hfa' := congrArg (· * 2 ^ n) hfa
    simp only [add_mul] at hfa'
    rw [hstep, pow_succ]
    ring_nf
    ring_nf at hfa' ih
    linarith [ih, hfa']
```
**The `ring_nf` ×3 + `linarith [ih, hfa']` closer is the load-bearing idiom** — normalize goal and both hypotheses to the same polynomial form, then linear arithmetic over ℕ.

```lean
theorem sum_bits_lt (f : ℕ → F p2) (k : ℕ) : ∑ i ∈ Finset.range k, ZMod.val (f i) * 2 ^ i < 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hb : ZMod.val (f n) ≤ 1 := by have := ZMod.val_lt (f n); simp only [p2] at this; omega
    have hle : ZMod.val (f n) * 2 ^ n ≤ 2 ^ n := by
      calc ZMod.val (f n) * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ hb
        _ = 2 ^ n := one_mul _
    linarith

theorem adder_correct (xv yv : ℕ → F p2) :
    (∑ i ∈ Finset.range 32, ZMod.val (xv i + yv i + carryVal xv yv i) * 2 ^ i)
      = ((∑ i ∈ Finset.range 32, ZMod.val (xv i) * 2 ^ i) + (∑ i ∈ Finset.range 32, ZMod.val (yv i) * 2 ^ i)) % 2 ^ 32 := by
  have hinv := adder_invariant xv yv 32
  have hlt := sum_bits_lt (fun i => xv i + yv i + carryVal xv yv i) 32
  have hc : ZMod.val (carryVal xv yv 32) < 2 := by
    have := ZMod.val_lt (carryVal xv yv 32); simp only [p2] at this; omega
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  rw [h32] at hinv hlt ⊢
  omega
```
**`have h32 : (2:ℕ)^32 = 4294967296 := by norm_num` then `omega` — literalize the modulus so `omega` can handle it.** This is the canonical trick for closing modular-arithmetic goals with `omega`.

---

## 6. Cost bookkeeping structure — what keeps 725 lines tractable

`/Users/lucidsamuel/experiments/scribe/corpus/zk-golf-challenges/Solution/SHA256CompressGF2Canonical/Cost.lean` (725 L). Header doc (`:14-23`): *"All `CostIs`/`IsCidCirc`/affine certificates for the canonical gadgets, kept out of the functional files. … Each gadget's block is wrapped in a `section` so its `attribute [local irreducible]` matches the original per-file scope."*

### 6.1 Structural devices

1. **Total separation from the functional files.** `Add32Canon.lean` etc. contain *only* `main`/`elaborated`/`soundness`/`completeness`/`circuit`/`computableWitnesses`/`subcircuit_localLength`/`eval_subOut_of_agreesBelow`. Zero cost or R1CS content. `Cost.lean` re-opens each namespace.
2. **Per-gadget `namespace … section … end … end` blocks**, in strict dependency order:
   `Add32Canon` (33-133) → shared `wv_getElem`/`zxorOut_affine` (135-153) → `Ch32Canon` (155-207) → `affineW_subOut_ch32canon` (209-219) → `Maj32Canon` (221-274) → `affineW_subOut_maj32canon` (276-285) → `Pin32Canon` (287-339) → `add32canon_cid`/`affineW_out_add32canon` (341-368) → `ScheduleStepCanon` (370-411) → `RoundCanon` (413-497) → `Pin256Canon` (499-551) → `affineW_subOut_schedcanon` (553-563) → `Sched16Canon` (565-633) → `round_out_affine_canon` (635-643) → `Rounds16Canon` (645-699) → top-level `out256_add32canon_affine` (701-725).
3. **Exactly 4 theorems per leaf gadget, 4 per composite** — a rigid schema:
   | | leaf | composite |
   |---|---|---|
   | | `costIs_main` (K1) | `costIs_main` (K2/K3) |
   | | `costIs_sub` (K4) | `costIs_sub` (K4) |
   | | `isCidentity_ops` (I1, in `semireducible` sub-section) | `isCidentity_main` (I2/I5) |
   | | `isCidentity_main` = `IsCidCirc.of_ops …` | — |
   | | `isCidentity_sub` = `IsCidCirc.subcircuit (isCidentity_ops …)` | `isCidentity_sub` = `IsCidCirc.subcircuit (… ).ops` |
   | | `balanced_sub` (I4) | `balanced_sub` (I4) |
   | | | `affineW_subOut` |
4. **Nested `section attribute [local semireducible] …` only around `isCidentity_ops`** — never around composites (which never unfold the predicate).
5. **Interstitial namespace-level "adapter" theorems** between gadget blocks, so the *next* gadget's proof is a flat term. E.g. `add32canon_cid` (`:358-360`) and `affineW_out_add32canon` (`:362-365`) exist only to strip the `⟨x, y⟩` struct constructor so `RoundCanon.isCidentity_main` reads `add32canon_cid _ _ ha1 hch` rather than `Add32Canon.isCidentity_sub ⟨_, _⟩ ha1 hch`.
6. **Numeric cost constants never appear as arithmetic** — they appear as `⟨62, 62⟩` literals in a `CostIs.bind` sum tree and are collapsed by definitional evaluation, never by `norm_num`/`omega`.

### 6.2 The `CostIs`/canonical lemma chain, bottom to top

```
CostIs.witnessVector m c              ⟨m, 0⟩          (CostR1CS.lean:324)
CostIs.assertZero e                   ⟨0, 1⟩          (:336)
CostIs.pure a                         Count.zero      (:311)
CostIs.bind hf hg                     K₁ + K₂         (:314)
CostIs.forEach (per-index)            ⟨m*0, m*1⟩      (:375)
CostIs.mapFinRange                                    (:383)
CostIs.foldlRange (constant := …)                     (:391)
CostIs.subcircuit                                     (:340)
  ↓
CostIs.constraints h n : (operationCount …).constraints = K.constraints   (CostR1CSCanonical.lean:237)
  ↓
Balanced.of_costIs hc hL                                                  (CostR1CSCanonical.lean:232)
  ↓
IsCidCirc.bind / bind_out  (consume Balanced)                             (:259, :267)
IsCidCirc.foldlRange_inv / mapFinRange  (consume hlen + hbal)             (Canonical/Theorems.lean:22, :46)
  ↓
IsCidCirc.subcircuit (h : ∀ n, operationsIsCid n ((circuit.main b).operations n))  (:274)
  ↓
isR1CS_Cidentity_of_IsCidCirc hops hout                                   (:290)
```
And the *proof-internal* chain inside `isCidentity_ops`:
```
Circuit.bind_operations_eq → operationsIsCid_append (:142)
  ← needs (operationCount ops₁).constraints, supplied by CostIs.witnessVector / CostIs.forEach applied at the offset
operationsIsCid_witnessVector (:255) / operationsIsCid_pure (:250)   -- decoupled k and n
Circuit.forEach.operations_eq → operationsIsCid_flatten_ofFn (:194)
  ← hL : (CostIs.assertZero _).constraints _
at31_wv / wv_getElem  → isCidentityRowAt_var_sub_mul (:32)
```
The **decoupled** `operationsIsCid_pure`/`operationsIsCid_witnessVector` (taking `k` and `n` separately) exist precisely for this — doc `CostR1CSCanonical.lean:248-249`: *"`pure` with the pin counter and the offset decoupled (they differ mid-block; unifying them through large closures times out `whnf`)."*

### 6.3 BLAKE3's contrasting structure (`Blake3/Cost.lean`, 546 L)

Only **3 leaf `isCidentity_ops`** (`Add32Canon`, `Pin32Canon`, `PinStateCanon`); **everything else is `costIs_main`/`costIs_sub`/`balanced_sub` triples** (17 namespaces × 3 = 51 theorems, all 2–6 lines). The `isCidentity_main` proofs live separately in `Canonical.lean`. Header doc (`:6-11`): *"All composite gadgets are balanced… The base proofs below cover the canonical ripple-carry adder and the two vector-pin sizes; every other certificate is obtained by balanced composition."*
This is the **cleaner factoring**: aspect-per-file (`Circuit.lean` = functional, `Cost.lean` = CostIs+Balanced+3 leaf certs, `Canonical.lean` = IsCidCirc composition + affineness, `Witness.lean` = computableWitness, `Main.lean` = 33-line public entrypoint) vs SHA-256's gadget-per-file + one monolithic `Cost.lean`.

---

## 7. Recurring helper lemmas (name / statement / role)

### 7.1 In `Challenge/Utils/CostR1CSCanonical.lean`
| Name | Statement (abbrev) | Role |
|---|---|---|
| `Affine.one` | `Affine (1 : Expression F)` | `B` of every canonical copy/sum row |
| `isCidentityRowAt_var_sub_mul` | `Affine A → Affine B → isCidentityRowAt k (var ⟨k⟩ - A*B)` | **the only row constructor** |
| `isCidentityRowAt.isR1CSRow` | canonical row ⊆ R1CS row | refinement |
| `operationsIsCid` | ops-level pin-counter (nested-aware) | working certificate |
| `flatOperationsIsCid.flatOperationsIsR1CS`, `operationsIsCid.operationsIsR1CS` | refinement | |
| `flatCount_append`, `flatCount_toFlat_nested`, `flatCount_toFlat_nestedList` | counting bridges | mutual induction |
| `flatOperationsIsCid_append`, `operationsIsCid_append` | `IsCid k (a++b) ↔ IsCid k a ∧ IsCid (k + count a) b` | **the split lemma every leaf proof `rw`s** |
| `operationsIsCid_iff_toFlat` | nested ↔ flat | |
| `operationsIsCid_flatten_ofFn` | `(∀ i, count(g i)=L) → (∀ i, IsCid (k+i*L) (g i)) → IsCid k (ofFn g).flatten` | **loop/forEach closer** |
| `isCidCirc_iff_ops`, `IsCidCirc.of_ops`, `IsCidCirc.ops` | bridge | |
| `IsCidCirc.isR1CSCirc` | refinement | |
| `Balanced`, `Balanced.of_costIs`, `CostIs.constraints` | lockstep | |
| `IsCidCirc.pure`, `.witnessVector`, `operationsIsCid_pure`, `operationsIsCid_witnessVector` | base cases (decoupled `k`/`n`) | |
| `IsCidCirc.bind`, `.bind_out`, `.subcircuit` | composition | |
| `isR1CS_Cidentity_of_IsCidCirc`, `isR1CS_Cidentity.isR1CS` | top level / refinement | |

### 7.2 Solution-side, `Solution/SHA256CompressGF2Canonical/Theorems.lean`
| `IsCidCirc.foldlRange_inv` | invariant `P`, `hinit`, `hlen`, `hbal`, `hbody`, `hstep` | fold |
| `IsCidCirc.mapFinRange` | `hlen`, `hbal`, `h` | map |
| `zxorOut` | `Vector.ofFn fun i => a96 v (64 + i.val) + p[i.val]` | opaque Ch/Maj output |
| `eval_zxorOut_congr` | needs *both* `hv` and `hp` | computableWitness |

### 7.3 `Solution/SHA256CompressGF2/Theorems.lean` (the GF(2) bit-theory core)
`val_le_one`, `val_add_eq_xor`, `val_mul_eq_and` (all `by decide`); `foldl_add_eq_sum`, `fromBits_eq_sum`, `toNat_eq_fromBits`, `bits_bool`, `toNat_lt`, `val_eq_testBit`, `testBit_toNat_ge`, `testBit_toNat`; `testBit_rotRight32`, `testBit_shr`, `rotRight32_lt`; `windowVals`, `windowVals_getElem`, `wordAt_eq_fromBits`, `window_bool`, `wordAt_lt`, `testBit_wordAt`, `testBit_wordAt_ge`; `xor3_bit`; `toNat_map_eval_window`, `wordAt_map_eval_eq_toNat`, `wordAt_map_eval_eq_wordAt`, `toWords_getElem`; `ch_bit`, `maj_bit`, `testBit_not32`, `testBit_Ch`, `testBit_Maj`, `testBit_Ch_ge`, `testBit_Maj_ge`, `testBit_w96_0/1/2`, `ch_words`, `maj_words`; accessors `a96`, `b32`, `b512`, `a256`.

### 7.4 `EvalCongr.lean` (both instances, identical)
`eval_fields_iff` (the `↔`), `eval_getElem_congr` (mp), `eval_fields_of_getElem` (mpr), `eval_varFromOffset_of_agreesBelow`.
**These four are the base of every `computableWitness` proof in the corpus.**

### 7.5 Pure-ℕ layer
`PureSchedule.lean`: `valSchedule`, `vs_succ_ne`, `vs_stable`, `vs_lt16`, `vs_step`, `messageSchedule_eq`, `ext32`, `ext32_succ_ne`, `ext32_lt16`, `ext32_stable`, `extend16`, `extIdx`, `extIdx_lt/_input/_output/_out'`, `extend16_getElem`, `window`, `window_getElem`, `ext32_eq_window`, `window_zero`, `extend16_window`.
`PureRounds.lean`: `kAt`, `valState`, `sha256Compress_eq`, `win64`, `win64_getElem`, `at16`, `at16_lt`, `applyRounds16`, `applyN`, `foldl_eq_applyN`, `applyRounds16_eq_applyN`, `applyRounds16_advance`, `sha256Compress_split`.
**Common idiom for delinearizing `Fin.foldl`:** `suffices h : ∀ k (hk : k ≤ N), Fin.foldl k … = valX … by exact h N (le_refl N)` then `induction k` with `Fin.foldl_succ_last` and the `castSucc`-eraser:
```lean
rw [show Fin.foldl k (fun w (i : Fin k) => body w i.castSucc.val) init
      = Fin.foldl k (fun w (i : Fin k) => body w i.val) init from rfl, ih (by omega)]
simp only [Fin.val_last]
```
(`PureSchedule.lean:105`, `PureRounds.lean:41-48,85-88,109-114`, `Sched16Theorems.lean:199-206`, `Rounds16CanonTheorems.lean:42-47`.)

### 7.6 Fold-accumulator closed forms (per-loop, 3-lemma pattern)
| Loop | closed form | bridges |
|---|---|---|
| `Sched16Canon` | `varBuf i₀ v : ℕ → Vector (fields 32 (Expression …)) 32` (`Sched16CanonTheorems.lean:41-49`) | `finFoldl_eq_varBuf`, `varBuf_out`, `foldlAcc_eq_varBuf`, `foldlAcc_eq_varBuf_do`, `stepBody_localLength`, `eval_stepWord_of_agreesBelow`, `eval_varBuf_getElem_of_agreesBelow` |
| `Rounds16Canon` | `stateVar256 r0 i₀ v : ℕ → fields 256 (Expression …)` (`Rounds16CanonTheorems.lean:26-29`) | `fin_foldl_eq_stateVar256`, `foldlAcc_eq_stateVar256`, `foldlAcc_eq_stateVar256_var`, `fin_foldl_subcircuit_eq_stateVar256`, `eval_stateVar256_of_agreesBelow` |

**The `_var` duplicate exists purely for type-spelling:** `foldlAcc_eq_stateVar256_var` has `(β := Var (fields 256) (F p2))` while `foldlAcc_eq_stateVar256` has `(β := fields 256 (Expression (F p2)))`; both bodies are the *same term*. Doc (`:57-58`): *"`foldlAcc` bridge in the `Var`-spelled accumulator type, which is how the `computableWitness` peeling lemmas present the fold."* Similarly `Sched16Canon.foldlAcc_eq_varBuf_do := foldlAcc_eq_varBuf i₀ v k h`.

Also `stepWord`, `@[simp] scheduleStep_output`, `@[simp] scheduleStep_localLength`, `constantLength` (the explicit `Circuit.ConstantLength` instance):
```lean
def constantLength : Circuit.ConstantLength (fun (x : … × Fin 16) => do …) where
  localLength := 218
  localLength_eq _ _ := by simp [circuit_norm, ScheduleStepCanon.circuit, ScheduleStepCanon.elaborated]
```
Doc (`Sched16Theorems.lean:140-142`): *"Naming it lets the fold in `main` skip synthesis and lets the cost/R1CS lemmas fold with the same instance."* / (`Rounds16Theorems.lean:121-123`): *"skip the expensive `infer_constant_length` synthesis (which times out on the `c288s`/`q768` window wrappers)."*

### 7.7 `eval_*_congr` family (the computableWitness input-agreement layer)
SHA-256 (`ScheduleStepTheorems.lean:218-293`, `Round.lean:215-243`, `Sched16Theorems.lean:60-77`, `Rounds16Theorems.lean:84-106`, `MainTheorems.lean:102-133`, `Add32.lean:298-321`):
`eval_c96_congr`, `eval_c128_congr`, `eval_w128_congr`, `eval_rotrE_congr`, `eval_shrE_congr`, `eval_xor3E_congr`, `eval_lowerSigma0E_congr`, `eval_lowerSigma1E_congr`, `eval_upperSigma0E_congr`, `eval_upperSigma1E_congr`, `eval_w288_congr`, `eval_constW_congr`, `eval_outState_congr`, `eval_q512_congr`, `eval_c512x_congr`, `eval_q768_congr`, `eval_st768_congr`, `eval_c288s_congr`, `eval_input_h_congr`, `eval_input_m_congr`, `eval_w256_congr`, `eval_c768_congr`, `eval_out_mk_congr`, `Add32.eval_mk_congr`, `eval_x_congr`, `eval_y_congr`, `eval_at32_fun_congr`, `eval_carryE_of_agreesBelow`, `ScheduleStep.eval_in1_congr`, `eval_in2_congr`.
Standard body:
```lean
refine eval_fields_of_getElem fun i hi => ?_
unfold <builder> <accessor>
rw [Vector.getElem_ofFn]
[split ×k]
exact eval_getElem_congr h _ _
```
Struct-projection variant (`MainTheorems.lean:102-110`, `Blake3/Witness.lean:137-235` — 18 instances):
```lean
theorem eval_input_h_congr {v : Var Input (F p2)} (h : eval env v = eval env' v) : eval env v.h = eval env' v.h := by
  have h2 := congrArg (fun s : Input (F p2) => s.h) h
  simpa [circuit_norm] using h2
```
Struct-constructor variant (`Blake3/Witness.lean:74-135` — 7 instances):
```lean
theorem eval_quad_mk_congr … (ha) (hb) (hc) (hd) :
    eval env (⟨a, b, c, d⟩ : Var Quad (F p2)) = eval env' (⟨a, b, c, d⟩ : Var Quad (F p2)) := by
  simp only [circuit_norm] at ha hb hc hd ⊢
  rw [ha, hb, hc, hd]
```
Blake3-specific: `eval_xorRotate_congr`, `eval_stateWord_congr`, `eval_writeQuad_congr` (needs the `CircuitType.eval_expression_prover_to_verifier` bridge, `Witness.lean:40-43`), `eval_permuteState_congr`, `eval_finalizeState_congr`, `eval_initialState_congr`, `eval_initialBlock_congr`, `eval_freshQuad_of_agreesBelow`.

### 7.8 `Blake3/PureEval.lean` — map-eval commutation lemmas
`eval_splitWords`, `eval_flattenWords`, `eval_constWord`, `eval_initialState`, `eval_initialBlock`, `eval_permute`, `eval_permuteState`, `eval_finalizeState`. All ≤10 lines:
```lean
refine Vector.ext fun i hi => ?_
simp [<def>, circuit_norm]
```
with `by_cases h : x.testBit i = true <;> simp [constWord, h, circuit_norm]` (constWord), `interval_cases i <;> simp [permute, circuit_norm]` (permute, 16 cases), `split` (initialState/finalizeState).
`Blake3/Theorems.lean:95-136`: `eval_xorWord`, `eval_rotRight`, `eval_stateWord`, `eval_setWord` (`by_cases h : j / 32 = i.val <;> simp [setWord, h, circuit_norm]`), `eval_readQuad`, `eval_writeQuad`.

---

## 8. Tactic vocabulary per obligation

### 8.1 `soundness`
| Tactic / lemma | Frequency | Where |
|---|---|---|
| `circuit_proof_start [main, Spec, …]` | every proof | universal |
| `obtain ⟨…⟩ := h_holds` / `:= h_input` | every composite | |
| `Vector.ext_iff.mp` + `rwa [Vector.getElem_map]` | every gadget with input | S3 |
| `refine Vector.ext fun i hi => ?_` | vector goals | |
| `rw [Vector.getElem_ofFn]`, `Vector.getElem_map`, `Vector.getElem_mapRange`, `Vector.getElem_finRange` | pervasive | |
| `Vector.getElem_set_self`, `Vector.getElem_set_ne`, `Vector.getElem_append_left/right`, `Vector.getElem_replicate` | fold invariants | S11 |
| **`linear_combination h`** / `linear_combination hc + hp` | every constraint→value step | S9 |
| **`by decide`** | `fullAdder_val`, `xor3_bit`, `ch_bit`, `maj_bit`, `val_le_one`, `val_add_eq_xor`, `val_mul_eq_and` | GF(2) signature |
| `apply Nat.eq_of_testBit_eq; intro i; by_cases hi : i < 32; … push_neg at hi` | every bitwise word lemma | S8 |
| `Nat.testBit_xor`, `Nat.testBit_and`, `Nat.testBit_div_two_pow`, `Nat.testBit_mod_two_pow`, `Nat.testBit_two_pow_mul_add`, `Nat.testBit_two_pow_sub_one`, `Nat.testBit_lt_two_pow`, `Nat.pow_le_pow_right` | bit layer | |
| `Finset.sum_congr rfl fun j hj => ?_` + `Finset.mem_range.mp hj` | `toNat` sums | S-adder |
| `Finset.sum_range_succ`, `Finset.sum_eq_zero`, `Fin.sum_univ_eq_sum_range`, `Fin.sum_univ_castSucc` | | |
| `ring_nf` (×3) + `linarith [ih, hfa']` | `adder_invariant` | §5.4 |
| `omega` after `have h32 : (2:ℕ)^32 = 4294967296 := by norm_num` | `adder_correct` | §5.4 |
| `interval_cases i` / `interval_cases k` | 8- or 16-way case splits | S6 |
| `simp only [show <numeric fact> from by omega]` | index normalization | pervasive |
| `simp only [Nat.mod_eq_of_lt hj]`, `Nat.mod_lt _ (by norm_num)` | total accessors | pervasive |
| `if_pos (by omega : …)` / `if_neg (by omega : ¬ …)` / `dif_pos` / `dif_neg` / `split` | window `ofFn`s | |
| `conv_lhs => rw [varBuf]` | recursive-def unfolding | S11 |
| `show … from rfl` / `have hunf : … := rfl` | defeq unfolding under binders | S10 |
| `Nat.eq_of_testBit_eq`, `Nat.add_mod_mod`, `Nat.sub_add_cancel`, `Nat.one_le_iff_ne_zero.mpr` | | |
| `simpa only [<def>, h] using h'` | BLAKE3 composites | S15 |
| `set x := … with hx` | naming | |
| `set_option maxRecDepth 100000 in` | `Rounds16Canon.soundness` | S12 |
| `dsimp only at …` | BLAKE3 top-level | |

**Not observed anywhere:** `bv_decide`, `decide` on non-`F 2` propositions, `native_decide`, `aesop`, `nlinarith`, `polyrith`.

### 8.2 `completeness`
`circuit_proof_start`; `intro i`; `h_env i`; `simp only [circuit_norm, Vector.getElem_ofFn] at henv ⊢`; `rw [henv]`; **`ring`**; `simp only [<circuit>, <Assumptions>, and_self / true_and]`; `obtain ⟨iv, hiv⟩ := i` + `cases iv with | zero | succ n`; `simp only [Nat.zero_mod, reduceIte, circuit_norm]`; `refine ⟨?_, ?_⟩`.
**`ring` is the universal closer** (GF(2) is a commutative ring; the constraint after substitution is a polynomial identity).

### 8.3 `mainCost`
`unfold main`; `show (⟨_, _⟩ : Count) = _; congr 1`; `rw [← hcount]`; `refine CostIs.bind (…) fun _ => ?_`; `exact CostIs.pure _`; `CostIs.subcircuit (fun n => costIs_main b n)`; `(constant := constantLength)`; term-mode ascription `(… : CostIs (main b) <sum>)`; `intro input`.
**No `omega`, no `norm_num`, no `decide`.** All arithmetic is definitional numeral evaluation.

### 8.4 `isR1CS_Cidentity`
`attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid`; `unfold main`; `rw [Circuit.bind_operations_eq, operationsIsCid_append, CostIs.witnessVector m _ n]`; `refine ⟨…, ?_⟩`; `rw [Circuit.forEach.operations_eq]`; `refine operationsIsCid_flatten_ofFn (L := 1) (fun i => (CostIs.assertZero _).constraints _) fun i => ?_`; `simp only [Vector.getElem_finRange]`; `simp only [Nat.mul_one]`; `rw [wv_getElem]` / `rw [at31_wv, Nat.mod_eq_of_lt i.isLt]`; `exact isCidentityRowAt_var_sub_mul hA hB`; `refine IsCidCirc.bind_out h hbal fun n => ?_`; `exact IsCidCirc.pure _`; `Balanced.of_costIs h (fun n => by simp [circuit_norm, subcircuit, circuit, elaborated])`; `refine IsCidCirc.foldlRange_inv (constant := …) (L := …) P ?_ ?_ ?_ ?_ ?_`; `intro i hi; unfold f; rw [Vector.getElem_ofFn]; split`; `exact affineW_varFromOffset _ _`; `exact affineW_mapRange_var _`; `exact Affine.add …` / `Affine.zero` / `Affine.one` / `Affine.const _`; `hflat.left_of_append` / `.right_of_append`; `simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz, hi] using hinput …`; `set_option maxRecDepth 8000 in`; `(by omega)` for offset side conditions.
**Canonical simp set:** `simp [circuit_norm, subcircuit, circuit, elaborated]` (localLength) and `simp only [circuit_norm, subcircuit, <Ns>.circuit, <Ns>.elaborated]` (output shape).

### 8.5 `computableWitness`
`intro offset input env env'`; `change Operations.forAllFlat offset (FormalCircuitBase.computableWitnessCondition input env env') ((main input).operations offset)`; `apply FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses`; `unfold main`; the fixed `simp only [Circuit.bind_structuralComputableWitnesses_iff, Circuit.witnessVector_…, Circuit.forEach_…, Circuit.assertZero_…, Circuit.pure_…, FormalCircuit.subcircuit_…, Circuit.foldlRange_…, Circuit.mapFinRange_…, <Ns>.subcircuit_localLength, and_true]`; `and_intros` / `refine ⟨?_, …, ?_⟩` / `constructor`; `FormalCircuit.subcircuit_flatStructuralComputableWitnesses …` (independent) vs `…_of_condition` + `intro kk e e' hle h_agree h_input` (dependent); `have h… := <Ns>.eval_subOut_of_agreesBelow _ (offset + …) (by omega) h_agree …` cascade; `trivial`; `attribute [local irreducible] …`; `set … with …`; `rw [foldlAcc_eq_varBuf_do offset input iv hiv]` / `rw [foldlAcc_eq_stateVar256_var …]` / `rw [fin_foldl_subcircuit_eq_stateVar256 …]`; `obtain ⟨iv, hiv⟩ := i`; the `himplies` induction (W5) with `Condition.implies`, `Condition.ignoreSubcircuit`, `FlatOperation.forAll_implies`, `Operations.forAll_toFlat_iff`, `ProverEnvironment.agreesBelow_of_le`.
BLAKE3 shortcut for 4 identical goals (`Witness.lean:340-348`):
```lean
all_goals
  exact FormalCircuit.subcircuit_flatStructuralComputableWitnesses
    Pin32Canon.circuit input _ _ (fun _ _ h => by
      first
      | have hx := congrArg Quad.a h; simpa [circuit_norm] using hx
      | have hx := congrArg Quad.b h; simpa [circuit_norm] using hx
      | have hx := congrArg Quad.c h; simpa [circuit_norm] using hx
      | have hx := congrArg Quad.d h; simpa [circuit_norm] using hx)
    Pin32Canon.computableWitnesses env env'
```

### 8.6 `elaborated`
- Default: `by elaborate_circuit` (all leaf gadgets, all BLAKE3 gadgets, `RoundCanon`, `ScheduleStepCanon`).
- Loop circuits need `elaborate_circuit_with { … } using by …`:
  - `Rounds16Canon.lean:26-36`: `{ localLength _ := 9248; output _ i₀ := varFromOffset (fields 256) (i₀ + 8992) }` then `refine ⟨fun a => ?_, fun a n => ?_, ?_, ?_⟩` with four `simp only [circuit_norm]`.
  - `Sched16Canon.lean:36-70`: `{ output _ i₀ := c512x (stepWord i₀ 0) … (stepWord i₀ 15) }` then a `have hfold := finFoldl_eq_varBuf n a` + 16 `varBuf_out n a k (by norm_num) 16 (by norm_num) (by norm_num)` rewrites.

---

## 9. Delta table: general-C vs canonical (retrieval keys)

| Concern | general (`Solution/SHA256CompressGF2/`) | canonical (`…Canonical/`) |
|---|---|---|
| Predicate | `isR1CS` / `IsR1CSCirc` / `isR1CSRow` | `isR1CS_Cidentity` / `IsCidCirc` / `isCidentityRowAt` |
| Row builder | `isR1CSRow_sub_mul hC hA hB` (C **affine**) **or** `isR1CSRow_of_affine` | `isCidentityRowAt_var_sub_mul hA hB` (C = **`var ⟨k⟩` only**) |
| Linear row | allowed (`isR1CSRow_of_affine`) | **forbidden** — must write `… * 1` |
| bind | `IsR1CSCirc.bind hf hg` | `IsCidCirc.bind hf **hbal** hg` |
| fold | `IsR1CSCirc.foldlRange_inv P hinit hbody hstep` | `IsCidCirc.foldlRange_inv P hinit **hlen hbal** hbody hstep` |
| reducibility guard | `attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS [a96/b32/b256]` | `attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid` (opposite direction!) |
| `Add32` rows | 1 row/bit: `(cᵢ₊₁ − cᵢ) − (xᵢ+cᵢ)(yᵢ+cᵢ)`, 31/31 | 2 rows/bit: `dᵢ − (xᵢ+cᵢ)(yᵢ+cᵢ)` and `cᵢ₊₁ − (cᵢ+dᵢ)·1`, 62/62 |
| adder soundness closer | `linear_combination hc` | `linear_combination hc + hp` |
| adder carry block offset | `i₀ + n` | `i₀ + 31 + n` |
| `Ch32`/`Maj32` output | witnessed result `w` | inlined `zxorOut v p` (AND witnesses only) |
| `Pin32`/`Pin256` row | `w − v` | `w − v * 1` |
| Round pin offsets | 281 / 313 | 498 / 530 |
| ScheduleStep pin offset | 93 | 186 |
| adder witness congr | `Add32.eval_at32_fun_congr` (funext) | `Add32Canon.eval_at32_pt_congr` (pointwise) |
| per-gadget extras | `costIs_main/sub`, `isR1CS_main/sub`, `affineW_subOut` | + **`balanced_sub`**, + `isCidentity_ops`, + `isCidentity_main/sub` |

---

## 10. Reviewer-facing guarantee lemmas (`CostR1CSCanonicalGuarantees.lean`)

```lean
def assertExprs : List (FlatOperation F) → List (Expression F)
  | [] => [] | .assert e :: ops => e :: assertExprs ops | _ :: ops => assertExprs ops

theorem flatOperationsIsCid.pin {k} {ops} (h : flatOperationsIsCid k ops) :
    ∀ t (e : Expression F), (assertExprs ops)[t]? = some e → isCidentityRowAt (k + t) e
-- induction ops generalizing k; cases t with zero => simpa [← ht] using h.1
--                                        | succ t => rw [show k + (t + 1) = (k + 1) + t by omega]; exact ih h.2 t e ht

theorem IsCidCirc.row_pins {c} (h : IsCidCirc c) (n t : ℕ) {e}
    (ht : (assertExprs (Operations.toFlat (c.operations n)))[t]? = some e) : isCidentityRowAt (n + t) e := (h n).pin t e ht

theorem guarantee_row_refines / guarantee_obligation_refines / guarantee_iff_ops
```
Sanity examples (`:103-116`), the second being the **non-vacuity witness**:
```lean
example : ¬ flatOperationsIsCid 0 [.assert ((Expression.var ⟨1⟩ : Expression F) - Expression.var ⟨0⟩ * 1)] := by
  rintro ⟨⟨A, B, -, -, hEq⟩, -⟩
  injection hEq with h1 h2
  injection h1 with hv
  injection hv with hi
  exact Nat.one_ne_zero hi
```
(Idiom: nested `injection` to peel `Expression.add`/`Expression.var`/`Variable.mk` and expose the index disagreement.)

---

## 11. Notable comments encoding proof-engineering constraints (verbatim)

- `CostR1CSCanonicalSpec.lean:78-91` — why `irreducible`: *"Whnf-normalizing an application at a concrete circuit therefore forces the scrutinee to a head constructor; i.e., it actually runs the circuit do-block and materializes all ~48k operations as one term (minutes of elaboration, and unbounded in general). … This is an elaboration hint, not semantics: the kernel ignores reducibility attributes … it can only make proofs harder to construct, never easier to fake."*
- `CostR1CSCanonical.lean:248-249` — decoupled `pure`: *"they differ mid-block; unifying them through large closures times out `whnf`."*
- `Main.lean:154-156` — *"`maxRecDepth` controls elaboration stack depth only (not the trusted kernel base nor the heartbeat budget)."*
- `Main.lean:200-201`, `Sched16Canon.lean:174-175`, `Rounds16Canon.lean:123-124` — *"Keep the unifier from expanding the N-witness circuit while peeling the loop; the offsets and outputs are supplied by the `rfl` lemmas instead."*
- `Rounds16Theorems.lean:121-123` — *"skip the expensive `infer_constant_length` synthesis (which times out on the `c288s`/`q768` window wrappers)."*
- `Rounds16Theorems.lean:157-159` — *"The accumulator type is spelled `fields 256 (Expression …)` (not `Var …`) so the LHS matches the `circuit_norm`-normalized `h_holds` syntactically."*
- `Canonical/Theorems.lean:66-68` — *"A named def keeps the circuit output opaque so subcircuit affineness does not reduce the whole `ofFn`."*
- `SHA256CompressGF2/Cost.lean:729-732` — *"The offsets `e0..e7` and the state `s4` are abstract parameters so the unifier assigns them structurally, not by reducing the deep composed circuit."*
- `Blake3/Canonical.lean:6-8` — *"Every composite boundary is pinned. Consequently, the only nontrivial affineness obligations are the pure word/state selections feeding the next canonical subcircuit."*
- `Blake3/G.lean:6-8` — *"This reference deliberately materializes every intermediate word. The extra rows make every enclosing proof a short composition of exact word equalities."*
- `Blake3/Circuit.lean:6-8` — *"This is intentionally not cost-optimized; it keeps all correctness and witness-computability arguments local and compositional."*
- `Interface.lean:13-15` — *"There is no padding or message-length handling; … There are no assumptions because every element of `F 2` is already a bit."*
