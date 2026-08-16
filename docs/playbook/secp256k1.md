# zkGolf secp256k1 ScalarMul / ScalarMulFixedBase — Proof Pattern Catalog

All paths absolute. Unless marked `[VB]` (variable-base only), line numbers are from `/Users/lucidsamuel/experiments/scribe/corpus/zk-golf-challenges/Solution/Secp256k1ScalarMulFixedBase/`; the `Secp256k1ScalarMul/` copies are **byte-identical modulo the namespace/import token** (`Solution.Secp256k1ScalarMul` ↔ `Solution.Secp256k1ScalarMulFixedBase`) for every file except `Main.lean`, `MainTheorems.lean`, `Cost.lean` (tail only), and four VB-only files.

---

## 0. Corpus map

### 0.1 Diff between the two solution trees

```
diff -rq Secp256k1ScalarMul/ Secp256k1ScalarMulFixedBase/   → differing *lines* per file:
  6–14 lines  : AddMod, AddModTheorems, CompleteAdd, CompleteAddTheorems, DivOrZero,
                DivOrZeroTheorems, EqViaCarries, Equal, IsZeroFe, IsZeroFeTheorems,
                LessThan, MulMod, MulModTheorems, Mux, Normalize, Params, ScalarMul,
                ScalarMulTheorems, Step, SubMod, SubModTheorems, ToBytes, ToBytesTheorems
                  → pure namespace rename; NO proof differences at all
  25 lines    : Cost.lean            (only `affineInput_components`, lines 1486–1500)
  26 lines    : Theorems.lean        (namespace rename only, 1124 lines)
 162 lines    : Main.lean            (REAL difference — see §8)
 216 lines    : MainTheorems.lean    (REAL difference — see §8)
VB-only files : AddModL.lean (287), SubModL.lean (297), MulModL.lean (233),
                MulModLTheorems.lean (360)   ← DEAD CODE, see §9
```

**Key structural fact for the playbook:** the entire ~12,700-line gadget stack is *identical* between the two challenges. The fixed-base specialization is confined to `Main.lean` + `MainTheorems.lean` (≈380 lines).

### 0.2 File sizes (FixedBase; VB same unless noted)

| file | LOC | role |
|---|---|---|
| `Theorems.lean` | 1124 | BigInt type, `fromLimbs`, `polyValue`, `BigIntParams`, all pure ℕ carry lemmas |
| `Cost.lean` | 1510 (VB 1513) | `CostIs` + `IsR1CSCirc` certificates for every gadget |
| `MulModTheorems.lean` | 761 | pure arithmetic cores `mulMod_soundness_core(_wm)`, `mulMod_completeness_core(_wm)` |
| `MulMod.lean` | 721 | `witnessedMul`, `MulMod.circuit` |
| `ScalarMulTheorems.lean` | 699 | `accVar`, `specAcc`, `fold_invariant`, output-boundary lemmas |
| `LessThan.lean` | 677 | borrow-chain `<` assertion |
| `CompleteAdd.lean` | 686 | complete group law circuit |
| `EqViaCarries.lean` | 659 | **the non-native carry argument** |
| `IsZeroFe.lean` | 498 | emulated-field zero flag |
| `AddModTheorems.lean` | 494 | `emuOfNat`/`pConst`/padded-`polyValue` machinery + AddMod cores |
| `DivOrZero.lean` | 491 | witnessed inversion with zero guard |
| `CompleteAddTheorems.lean` | 431 | chord/tangent closure + `soundness_core` case analysis |
| `AddMod.lean` / `SubMod.lean` | 388 / 383 | modular add / sub |
| `ScalarMul.lean` | 352 | 256-step fold + byte output |
| `SubModTheorems.lean` | 325 | borrow identity + SubMod cores |
| `ToBytes.lean` / `ToBytesTheorems.lean` | 261 / 248 | limb→byte boundary |
| `Step.lean` | 233 | one double-and-add step |
| `Main.lean` | 225 (VB 265) | comparator entry point |
| `Params.lean` | 183 | limb params, `Emu`, `FlaggedPoint`, `decodeFe`/`decodePoint` |
| `Mux.lean` | 160 | materialized select |
| `MainTheorems.lean` | 151 (VB 229) | Interface↔gadget bridge |
| `Equal.lean` / `Normalize.lean` | 118 / 107 | limbwise `===` / range check |
| `IsZeroFeTheorems.lean` | 61 | `BigInt.value_eq_zero_iff`, `decodeFe_eq_zero_iff` |

**Zero `sorry`s. Zero `native_decide` uses** (three textual mentions in Cost.lean:14, MainTheorems.lean:19/99 are comments asserting its absence).

---

## 1. The five obligations — statement shapes and where discharged

Statement templates live in the Challenge dir:

`/Users/lucidsamuel/experiments/scribe/corpus/zk-golf-challenges/Challenge/Instances/Secp256k1ScalarMulFixedBase/Challenge.lean:21-33`

```lean
def main : Var Input (F circomPrime) → Circuit (F circomPrime) (Var Output (F circomPrime)) := sorry
instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := sorry
theorem soundness   : GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := sorry
theorem completeness: GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec := sorry
theorem mainCost    : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := sorry
theorem isR1CS      : Challenge.CostR1CS.isR1CS main := sorry
theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circomPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := sorry
```

Discharge sites (FixedBase):

| obligation | file:line | length |
|---|---|---|
| `elaborated` | `Main.lean:31-33` | 3 lines — `by elaborate_circuit` |
| `soundness` | `Main.lean:41-60` | 20 lines |
| `completeness` | `Main.lean:62-74` | 13 lines |
| `mainCost` | `Main.lean:108-109` | 2 lines (+ `costIs_main` 102-106) |
| `isR1CS` | `Main.lean:136-139` | 4 lines (+3 helpers 87-134) |
| `computableWitness` | `Main.lean:152-216` | 65 lines |

VB equivalents: `Main.lean:54-79` (soundness), `81-96` (completeness), `129-130` (mainCost), `~155` (isR1CS).

---

## 2. Non-native field arithmetic: representation

### 2.1 The two primes

- **Circuit field** = BN254/circom scalar prime `p = 21888242871839275222246405745257275088548364400416034343698204186575808495617` (≈254 bits). Declared `Interface.circomPrime` (`Challenge/.../Interface.lean:55`), aliased `@[reducible] def circomPrime` in `Params.lean:27-28`. Primality is an **axiom** (`Interface.lean:57`: `axiom hCircomPrime : circomPrime.Prime`).
- **Emulated field** = secp256k1 base prime `P256 = 2^256 − 2^32 − 977`, `Params.lean:33`: `@[reducible] def P256 : ℕ := Specs.Secp256k1.p`. Also axiomatized prime (`Challenge/Specs/Secp256k1.lean:138`).

### 2.2 Limb layout

`Params.lean:36-62`:

```lean
@[reducible] def numLimbs : ℕ := 4
@[reducible] def limbBits : ℕ := 64        -- byte-aligned
@[reducible] def bytesPerLimb : ℕ := 8
@[reducible] def coordBytes : ℕ := 32
@[reducible] def Emu : TypeMap := BigInt numLimbs   -- = fields 4

def secpParams : BigIntParams circomPrime numLimbs where
  B := limbBits          -- 64
  W := 69                -- carry bit-width
  hB := by decide        -- 2^64 < p
  hW := by decide        -- 2^69 < p
  hB1 := by decide       -- 1 ≤ B
  hWB := by decide       -- carryOffset*2 < 2^W
  hWp := by decide       -- (m+1)·2^(2B)·3 + 2^W·2^B + 2^W < p   (≈2^133.1 < 2^253.6)
  hp  := by decide       -- 2^(2B)·(m+1)·4 < p
```

**Pattern name: `params-by-decide`.** All eight field-size side conditions are `by decide` on closed `Nat` arithmetic. `BigIntParams` (`Theorems.lean:887-903`) bundles them so gadgets take one argument instead of eight.

### 2.3 Denotation

`Theorems.lean:32-33, 195-199`:

```lean
def Limbs.fromLimbs (limbBits : ℕ) (limbs : List ℕ) : ℕ :=
  limbs.foldr (fun limb acc => limb + acc * 2 ^ limbBits) 0
def BigInt.value (B : ℕ) (x : BigInt m (F p)) : ℕ := fromLimbs B (x.toList.map ZMod.val)
def BigInt.Normalized (B : ℕ) (x : BigInt m (F p)) : Prop := ∀ i : Fin m, (x[i]).val < 2 ^ B
```

`Params.lean:142-150`:
```lean
def decodeFe (x : Emu (F circomPrime)) : Specs.Secp256k1.Fp := ((x.value limbBits : ℕ) : Specs.Secp256k1.Fp)
def Fe.Valid (x : Emu (F circomPrime)) : Prop := x.Normalized limbBits ∧ x.value limbBits < P256
```

`Fe.Valid` = **normalized ∧ canonical**. This pair is the invariant threaded through every gadget spec.

### 2.4 Flagged point

`Params.lean:158-181`:
```lean
structure FlaggedPoint (F : Type) where x : Emu F ; y : Emu F ; isInf : F  deriving ProvableStruct
def decodePoint (P) := if P.isInf = 1 then .infinity else .affine { x := decodeFe P.x, y := decodeFe P.y }
def FlaggedPoint.Valid (P) : Prop :=
  IsBool P.isInf ∧ Fe.Valid P.x ∧ Fe.Valid P.y ∧
    (P.isInf = 0 → Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve {x := decodeFe P.x, y := decodeFe P.y})
def infConst : Var FlaggedPoint (F circomPrime) := { x := zeroConst, y := zeroConst, isInf := 1 }
```

Note **on-curveness is part of the point invariant**, guarded by `isInf = 0`. This is what makes the tangent-case doubling proof possible (§6).

### 2.5 Constants as limbs

`Params.lean:67-86`:
```lean
def limbOfNat (v k : ℕ) : ℕ := v / 2 ^ (limbBits * k) % 2 ^ limbBits
def emuOfNat (v : ℕ) : Emu (F circomPrime) := Vector.ofFn fun k => ((limbOfNat v k : ℕ) : F circomPrime)
def emuConst (v : ℕ) : Var Emu (F circomPrime) := Vector.ofFn fun k => ((limbOfNat v k : ℕ) : F circomPrime)
def pConst := emuConst P256 ; def zeroConst := emuConst 0 ; def oneConst := emuConst 1
```

`pConst` is the `modulus` argument of every `MulMod`/`LessThan` call — **the emulated prime is never witnessed, always a constant-limb vector**, which is what keeps every `MulMod` row R1CS-clean.

---

## 3. `EqViaCarries` — the carry/overflow argument (the core non-native idiom)

**File: `EqViaCarries.lean` (659 lines). This is the single most reusable artifact in the corpus.**

### 3.1 What it proves

`EqViaCarries.lean:114-120`:
```lean
def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  (∀ k : Fin (2*m-1), (input.lhs[k]).val < (m+1) * 2 ^ (2*B)) ∧
  (∀ k : Fin (2*m-1), (input.rhs[k]).val < (m+1) * 2 ^ (2*B))
def Spec (B : ℕ) (input : Inputs m (F p)) : Prop := polyValue B input.lhs = polyValue B input.rhs
```
`polyValue B coeffs = ∑ i, coeffs[i].val * 2^(B*i)` (`Theorems.lean:423-424`).

So: *two coefficient sequences with `.val` bounded by `(m+1)·2^{2B}` denote the same ℕ in base `2^B`.* Coefficients may be far larger than `2^B` — that is exactly the point (they come out of a schoolbook convolution).

### 3.2 The signed-carry-with-offset trick

`EqViaCarries.lean:65-94` (`main`) and `Theorems.lean:875-879`:

```lean
def carryOffset (B : ℕ) : ℕ := (m + 1) * 2 ^ (B + 1)
```

Circuit shape (4 blocks):
1. Witness `carry[k]` for `k ∈ [0, 2m-1)` as `OFF + (Σ_{j≤k} P_j 2^{Bj})/2^{B(k+1)} − (Σ_{j≤k} S_j 2^{Bj})/2^{B(k+1)}` — an **offset** signed carry so it stays a ℕ.
2. `Circuit.forEach carry (fun c => Gadgets.ToBits.rangeCheck P.W P.hW c)` — each carry to `W = 69` bits.
3. Per-index affine assert `lhs[k] + (carry[k-1] − OFF) − rhs[k] − (carry[k] − OFF)·2^B = 0`, with carry-in `0` at `k = 0` (via a `dite` on `k.val = 0`).
4. `assertZero (carry[2m-2] − OFF)` — top signed carry is zero.

**No division in-circuit.** Division only appears in the witness generator (`evalPartial P.B env Pc k / 2^(P.B*(k+1))`).

### 3.3 Soundness proof idiom (`EqViaCarries.lean:128-322`, ~195 lines)

Skeleton, in order:

```lean
soundness := by
  obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P       -- destructure params FIRST
  circuit_proof_start
  simp only [circuit_norm, Gadgets.ToBits.rangeCheck] at h_holds ⊢
  obtain ⟨h_range, h_lin, h_top⟩ := h_holds
  refine ⟨?_, by split <;> simp [circuit_norm]⟩
```

**Pattern `nat-indexed-shadow` (lines 138-141):** replace every `Fin`-indexed / `env.get` object by a total `ℕ → ℕ` function via `set … with h…`:
```lean
set Pn : ℕ → ℕ := fun k => if h : k < 2*m-1 then (input.lhs[k]'h).val else 0 with hPn
set Sn : ℕ → ℕ := fun k => if h : k < 2*m-1 then (input.rhs[k]'h).val else 0 with hSn
set Cn : ℕ → ℕ := fun k => (env.get (i₀ + k)).val with hCn
```
This is *the* enabling move: it lets `omega` and `Finset.sum` lemmas operate without dependent-index friction. `set` appears **483×** across the FixedBase tree.

**Pattern `offset-algebra` (lines 150-178):** derive the numeric facts about `OFFn` once:
```lean
have hOFF_eq   : OFFn = (m + 1) * 2 ^ (B + 1) := rfl
have hOFFB_eq  : OFFn * 2 ^ B = (m + 1) * 2 ^ (2*B + 1) := by rw [hOFF_eq, Nat.mul_assoc, ← pow_add]; congr 2; ring
have hpow_le   : (m+1) * 2^(2*B+1) ≤ (m+1) * 2^(2*B) * 3 := by rw [pow_succ]; nlinarith [Nat.two_pow_pos (2*B)]
have hOFFn_cast: (OFFn : F p).val = OFFn := ZMod.val_natCast_of_lt hOFFn_lt
have hXW : (m+1) * 2^(2*B) ≤ 2^W * 2^B := by … calc … Nat.pow_le_pow_right (by norm_num); omega
```
`nlinarith [Nat.two_pow_pos …]` is the idiom for "multiply a `≤` by a positive power of two".

**Pattern `per-index-lift` (lines 188-248) — the field→ℕ bridge.** Reusable lemma `Theorems.lean:905-936`:
```lean
lemma per_index_lift {B : ℕ} (a cinF b c off : F p) (cinN offN : ℕ)
    (hpB : 2 ^ B < p) (hcin : cinF.val = cinN) (hoff : off.val = offN)
    (hlhs : a.val + cinN + offN * 2 ^ B < p) (hrhs : b.val + c.val * 2 ^ B + offN < p)
    (heq : a + cinF + off * (2 ^ B : F p) = b + c * (2 ^ B : F p) + off) :
    a.val + cinN + offN * 2 ^ B = b.val + c.val * 2 ^ B + offN
```
Internal proof idiom (`Theorems.lean:914-936`): build `hlhs_cast : <field expr> = ((<nat expr> : ℕ) : F p)` by `push_cast [hacast, hcincast, hoffcast, hpow_val_cast]; ring`, then `rw [hlhs_cast, ZMod.val_natCast_of_lt hlhs]`, then `congrArg ZMod.val heq`. **This is the canonical "lift a field equation to ℕ under no-wraparound bounds" recipe and appears twice (`per_index_lift`, `per_limb_lift` at `Theorems.lean:1090-1120`).**

Symbolic-subterm evaluation before lifting (lines 194-204):
```lean
have ha_e : Expression.eval env input_var.lhs[k] = input.lhs[k]'hk := by rw [← h_input]; simp [Vector.getElem_map]
have hcin_e : … = if k = 0 then env.get (i₀+(k-1)) - (OFFn : F p) else … := by
  simp only []; split <;> simp [circuit_norm, sub_eq_add_neg]
simp only [ha_e, hb_e, hcin_e] at hlin
```
**Idiom `rw [← h_input]; simp [Vector.getElem_map]`** — used ~40× across the tree to turn `Expression.eval env input_var[k]` into `input[k]`.

Normalizing an `assertZero` to an equation: `rw [← sub_eq_zero]; rw [← hlin]; ring` (lines 212-216).

**Pattern `weighted-sum-then-omega` (lines 258-322) — the closing move.** Sum the per-index ℕ equations weighted by `2^(B*k)`, distribute into six named atoms, then finish with a single `omega`:
```lean
set SP    := ∑ k ∈ range (2*m-1), Pn k * 2^(B*k)          -- polyValue lhs
set SS    := ∑ k ∈ range (2*m-1), Sn k * 2^(B*k)          -- polyValue rhs
set SC    := ∑ k ∈ range (2*m-1), Cn k * 2^(B*(k+1))      -- outgoing carries
set SCin  := ∑ k ∈ range (2*m-1), (if k=0 then 0 else Cn (k-1)) * 2^(B*k)
set SCin' := … (if k=0 then OFFn else Cn (k-1)) …
set G     := ∑ k ∈ range (2*m-1), 2^(B*k)                 -- geometric series
have hSCin_rel : SCin' = SCin + OFFn := by rw [… Finset.sum_range_succ' …]; ring
have htel := carry_telescope B Cn (2*m-1)     -- Theorems.lean:841
have hgeo := geom_shift B (2*m-1)             -- Theorems.lean:860
…
omega                                          -- closes: SP = SS
```
Two ℕ identities do all the work:
- `carry_telescope` (`Theorems.lean:841-856`): `∑ (carry-in)·2^{Bk} + top·2^{Bn} = ∑ (carry-out)·2^{B(k+1)}`, by `induction n` + `omega`.
- `geom_shift` (`Theorems.lean:860-873`): `2^B · G = G + 2^{Bn} − 1`, by `induction n` + `omega`.

Both `set`-ed to atoms so `omega` sees only linear arithmetic over 6 opaque naturals.

### 3.4 Completeness proof idiom (`EqViaCarries.lean:323-552`, ~230 lines)

Direction: *given* `polyValue lhs = polyValue rhs`, construct/validate the carries.

Key moves:
- `set PFn/PSn : ℕ → ℕ := fun k => ∑ j ∈ range (k+1), Pn j * 2^(B*j)` (partial sums), `set Dk := fun k => 2^(B*(k+1))`, `set Cn := fun k => OFFn + PFn k / Dk k - PSn k / Dk k`.
- **Pattern `beta-reduce-set`** (lines 364-367): because `set` on a *function* blocks reduction, immediately add
  ```lean
  have hDk_app : ∀ k, Dk k = 2 ^ (B * (k + 1)) := fun k => rfl
  have hPFn_app : ∀ k, PFn k = ∑ j ∈ Finset.range (k+1), Pn j * 2^(B*j) := fun k => rfl
  have hCn_app : ∀ k, Cn k = OFFn + PFn k / Dk k - PSn k / Dk k := fun k => rfl
  ```
- Carry magnitude bound: `partial_div_bound` (`Theorems.lean:764-795`) — `(∑_{j≤k} f j 2^{Bj}) / 2^{B(k+1)} ≤ (m+1)·2^{B+1}` given `f j < (m+1)·2^{2B}` and `B ≥ 1`. Proof: geometric bound `∑_{j≤k} 2^{Bj} ≤ 2^{Bk+1}` (`induction k` + `omega`), then `Nat.div_le_of_le_mul`.
- Range-check discharge (lines 379-385): `calc OFFn + rP - rS ≤ OFFn + rP := Nat.sub_le _ _ ; _ ≤ OFFn + OFFn := by omega ; _ < 2^W := by have := hWB; omega`.
- **Digit matching (lines 406-448):** `partial_mod_stable` (`Theorems.lean:799-821`) gives `PFn k % Dk k = PSn k % Dk k` from the *global* equality, hence the `k`-th base-`2^B` digits agree, via `Nat.mod_mul_right_div_self`.
- Per-index recurrence (lines 419-502): `quot_step` (`Theorems.lean:825-835`) splits the running quotient; then
  ```lean
  clear_value qP qS rP rS      -- ★ makes omega able to reason with ℕ subtraction
  have hmulCnk : Cn k * 2^B = OFFn*2^B + rP*2^B - rS*2^B := by rw [hCnk, Nat.sub_mul, Nat.add_mul]
  have hrPmul : rS*2^B ≤ rP*2^B + OFFn*2^B := by have : rS ≤ rP + OFFn := by omega
                                                 calc … Nat.mul_le_mul_right _ this … Nat.add_mul
  omega
  ```
  **`clear_value` (used exactly 2×, both here) is the trick that makes truncated ℕ subtraction tractable for `omega`.**
- ℕ→field cast back (lines 535-546): `have hcast := congrArg (Nat.cast : ℕ → F p) hnatk; push_cast [hpow_cast] at hcast; rw [hAk, hBk, hCk] at hcast; … rw [← sub_eq_zero] at hcast; rw [← hcast]; ring`.

---

## 4. `MulMod` — witnessed-quotient modular multiplication

### 4.1 Circuit (`MulMod.lean:281-315`)

```
q ← witness ((a·b)/n as limbs) ; r ← witness ((a·b)%n as limbs)
Normalize q ; Normalize r
Pc  ← witnessedMul a b          -- affine convolution coeffs
Sqn ← witnessedMul q n
S[k] = Sqn[k] + r[k]  (k<m) | Sqn[k]
EqViaCarries { lhs := Pc, rhs := S }     -- a·b = q·n + r over ℕ
LessThan     { lhs := r,  rhs := n }     -- r < n
return r
```

Spec (`MulMod.lean:350-362`):
```lean
Assumptions B input := a.Normalized B ∧ b.Normalized B ∧ n.Normalized B ∧
                       a.value B < n.value B ∧ b.value B < n.value B ∧ 0 < n.value B
Spec B input out    := out.Normalized B ∧ out.value B = (a.value B * b.value B) % n.value B
```

### 4.2 `witnessedMul` — the R1CS-cleanliness pattern (`MulMod.lean:58-72`)

**Pattern name: `witnessed-product-matrix`.** Instead of feeding raw products `a[i]·b[j]` (degree 2) into `EqViaCarries`, witness an `m·m` product matrix `pp`, assert `a[i]·b[j] − pp[i·m+j] = 0` (one rank-1 R1CS row each), and return `bigIntMulVars pp` — a *linear form* over `pp`. Docstring at `MulMod.lean:51-57` states the motive explicitly.

Supporting infrastructure, all isolated for heartbeat budget:
| lemma | file:line | statement |
|---|---|---|
| `witnessedMul_output` | `MulMod.lean:78-81` | `(witnessedMul a b off).1 = bigIntMulVars (mapRange (m*m) …)`; proof `simp only [witnessedMul, circuit_norm]` |
| `witnessedMul_localLength` | `MulMod.lean:84-86` | `= m*m` |
| `witnessedMul_soundness` | `MulMod.lean:91-101` | reads the `forAllNoOffset` predicate `circuit_proof_start` leaves; `intro t; have := h t; rw [add_neg_eq_zero] at this` |
| `witnessedMul_requirements` | `MulMod.lean:122-127` | vacuous (`simp only [witnessedMul, circuit_norm]`) |
| `witnessedMul_usesLocalWitnesses` | `MulMod.lean:133-143` | completeness reading; note the `heq : off' = off` argument — "the `UsesLocal` offset may differ up to `Nat.add_comm`; we commute on the small unfolded goal only" |
| `witnessedMul_completeness` | `MulMod.lean:149-159` | `simp only [witnessedMul, circuit_norm]; intro t; rw [h t]; ring` |
| `witnessedMul_map_eval` | `MulModTheorems.lean:197-230` | bridges `bigIntMulVars` ↦ `bigIntMulNoReduce` |
| `witnessedMul_eval_bridge` | `MulMod.lean:106-118` | per-`k` version, own budget |

### 4.3 The Cauchy-product bridge

`Theorems.lean:712-752`, `polyValue_bigIntMulNoReduce`:
```
polyValue B (map eval (bigIntMulNoReduce a b))
  = (∑ i, (eval a[i]).val * 2^(B*i)) * (∑ j, (eval b[j]).val * 2^(B*j))
```
under `hbound : m * (2^B * 2^B) < p`. Chain of supporting lemmas:
- `val_bigIntMulNoReduce_coeff` (`Theorems.lean:550-598`) — `.val` of a coefficient is the ℕ convolution sum, *no field wraparound*; proof: bound each term by `2^B·2^B − 1` (`Nat.mul_lt_mul''`), sum via `Finset.sum_le_sum` + `Finset.sum_const` + `Fintype.card_fin`, then `hcast : … = (natConv : F p)` via `Nat.cast_sum` + `ZMod.natCast_zmod_val`, close with `ZMod.val_natCast_of_lt hlt`.
- `val_bigIntMulNoReduce_coeff_lt` (`Theorems.lean:604-639`) — coefficient `< m·2^{2B}`.
- `cauchy_inner_reindex` (`Theorems.lean:643-663`) — the `j = k − i` reindex, via `Finset.sum_nbij' (i := fun k => k - i) (j := fun j => i + j)`, five goals all closed by `simp only [Finset.mem_filter, Finset.mem_range] at …; omega`.
- `cauchy_base_pow` (`Theorems.lean:668-702`) — pure ℕ Cauchy product, via `Finset.sum_mul_sum` + `Finset.sum_comm`.

### 4.4 Soundness/completeness cores

`MulModTheorems.lean` provides a **four-lemma ladder** (isolated for heartbeat budget — the file says so at lines 341-344, 466-472, 537-539, 700-704):

```
mulMod_soundness_core        (MulModTheorems.lean:345-464)   -- stated over `bigIntMulNoReduce`
mulMod_soundness_core_wm     (MulModTheorems.lean:473-520)   -- over abstract Pv/Qv + eval bridges
mulMod_completeness_core     (MulModTheorems.lean:540-698)
mulMod_completeness_core_wm  (MulModTheorems.lean:705-755)
```
The `_wm` variants exist purely to avoid rewriting *inside* the huge `EqViaCarries` implication at the call site; they consume per-`k` bridges `heqAB_get`/`heqQN_get` and delegate via `eqImpl_bridge` (`MulModTheorems.lean:238-287`) / `eqConj_bridge` (`289-339`).

**Soundness core arithmetic (lines 389-464):**
```lean
set qVar/rVar/qv/rv   -- abbreviations
have ha_lt/hb_lt/hn_lt/hqd_lt/hrd_lt  -- per-limb `< 2^B` from `Normalized`, via
    `rw [show Expression.eval env input_var.1[i] = input.1[i] from by rw [← h_input]; simp only [Vector.getElem_map]]`
have hfield : m * (2^B * 2^B) < p := by
    have h1 : m * (2^B*2^B) = m * 2^(2*B) := by rw [two_mul, pow_add]
    rw [h1]; have h2 : … ≤ 2^(2*B)*(m+1)*4 := by nlinarith [Nat.two_pow_pos (2*B)]; omega
have hS_eq : (mapFinRange …) = sVec qVar n (i₀+m) := rfl        -- ★ `rfl` identifies the goal's dite-vector with sVec
have h_polyeq := h_eq_impl ⟨coeff_P_bound …, fun k => by have hb := coeff_S_bound …; rw [sVec, Vector.getElem_mapFinRange] at hb; exact hb⟩
rw [hP] at h_polyeq ; rw [hSplit, hSqn, hrval] at h_polyeq       -- becomes: a·b = q·n + r
have hr_lt_n := h_lt_impl ⟨hr_norm, hn_norm'⟩
exact remainder_eq h_polyeq hr_lt_n
```
Closing lemma (`MulModTheorems.lean:63-65`):
```lean
lemma remainder_eq {a b q n r : ℕ} (heq : a*b = q*n + r) (hr : r < n) : r = a*b % n := by
  rw [heq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
```
**This three-rewrite line is the entire "modular correctness" content.** Everything else is plumbing.

**Completeness core (lines 587-698):** witness values `qval := a*b/n`, `rval := a*b%n`; prove `q < n` from `a,b < n` (`Nat.div_lt_of_lt_mul` + `Nat.mul_lt_mul_right`); values by `BigInt.value_mapRange` (`Theorems.lean:378-397`); normalization by `normalized_mapRange` (`MulModTheorems.lean:524-535`); the `EqViaCarries` identity closes with `rw [hS_eq, hSplit, hSqn, hrv_val, hqval_def, hrval_def, Nat.div_add_mod']`.

---

## 5. `AddMod` / `SubMod` / `DivOrZero` / `LessThan` / `Normalize` / `Equal` / `Mux` / `IsZeroFe` / `ToBytes`

### 5.1 `AddMod` (`AddMod.lean`, `AddModTheorems.lean`)

Circuit (`AddMod.lean:34-60`): witness `r = (a+b) % P256` and quotient **bit** `q = (a+b)/P256`; `assertZero (q*(q-1))`; `Normalize r`; `LessThan {r, pConst}`; `EqViaCarries` on
```
lhs[k] = a[k] + b[k]            (k < 4)  else 0
rhs[k] = q * pConst[k] + r[k]   (k < 4)  else 0
```
Spec (`AddMod.lean:66-71`): `Fe.Valid out ∧ decodeFe out = decodeFe a + decodeFe b`.

**Pattern `padded-polyValue`** — `AddMod`/`SubMod` feed length-`(2·numLimbs − 1)` vectors whose top coefficients are the *constant* `0`. Master lemma `polyValue_padded` (`AddModTheorems.lean:146-173`):
```lean
lemma polyValue_padded (B) (env) (f : (k : Fin (2*numLimbs-1)) → k.val < numLimbs → Expression _) (c : ℕ → ℕ)
    (hval : ∀ k h, (Expression.eval env (f k h)).val = c k.val) :
    polyValue B (map eval (mapFinRange (2*numLimbs-1) fun k => if h : k.val < numLimbs then f k h else 0))
      = ∑ k ∈ Finset.range numLimbs, c k * 2 ^ (B * k)
```
Proof idiom: per-term `by_cases hk : k.val < numLimbs · rw [dif_pos hk, if_pos hk, hval …] · rw [dif_neg hk, if_neg hk]; norm_num [circuit_norm]`, then collapse the guarded `range (2m-1)` sum to `range m` with `Finset.sum_subset (Finset.range_subset_range.mpr (by decide))`.

Both bridges then instantiate it: `AddMod.polyValue_lhs` (`:270-295`) → `a.value + b.value`; `AddMod.polyValue_rhs` (`:299-334`) → `qN·P256 + r.value` (using `limb_sum_P256`, `AddModTheorems.lean:69-75`).

**No-wraparound micro-lemmas** (reused everywhere):
```lean
val_add_limb   (:178-181)  (u+v).val = u.val + v.val         -- ZMod.val_add_of_lt, `have := limb_add_lt; omega`
bound_add_limb (:184-189)  (u+v).val < (numLimbs+1)*2^(2*limbBits)   -- ZMod.val_add_le + limb_add_le_bound
val_q_mul_limb (:192-205)  (q·p_k).val = qN * limbOfNat P256 k       -- ZMod.val_mul_of_lt
```
The numeric facts `two_pow_limb_lt`, `limb_add_lt`, `limb_add_le_bound`, `P256_pos`, `P256_lt` are all `by decide` (`AddModTheorems.lean:20-33`).

**Soundness core** (`AddModTheorems.lean:340-409`) — the closing move is the **mod-P256 cast**:
```lean
have hcast := congrArg (Nat.cast : ℕ → Specs.Secp256k1.Fp) h_polyeq
push_cast at hcast
rw [show ((P256 : ℕ) : Specs.Secp256k1.Fp) = 0 from ZMod.natCast_self _, mul_zero, zero_add] at hcast
simp only [decodeFe]; exact hcast.symm
```
**Pattern `natCast_self-kills-the-quotient`.** SubMod's version (`SubModTheorems.lean:232-237`) ends `… mul_zero, add_zero] at hcast; exact eq_sub_of_add_eq hcast`.

Boolean-quotient extraction (`AddModTheorems.lean:382-387`):
```lean
have hq01 : (env.get (i₀+numLimbs)).val ≤ 1 := by
  rcases mul_eq_zero.mp hq_bool with h | h
  · rw [h, ZMod.val_zero]; omega
  · rw [add_neg_eq_zero] at h; rw [h, ZMod.val_one]
```

Gadget-level `soundness`/`completeness` are **9-line wrappers** (`AddMod.lean:73-97`): `circuit_proof_start [<12 unfold names>]`, `obtain ⟨hq_bool, hr_norm, h_lt_impl, h_eq_impl⟩ := h_holds`, `exact soundness_core …`.

### 5.2 `SubMod`

Same shape with a **borrow** bit. Witness `r = (a + P256 − b) % P256`, `q = if a < b then 1 else 0`; identity `r + b = a + q·P256`. Key lemma (`SubModTheorems.lean:20-27`):
```lean
lemma sub_witness_identity {va vb : ℕ} (hva : va < P256) (hvb : vb < P256) :
    (va + P256 - vb) % P256 + vb = va + (if va < vb then 1 else 0) * P256 := by
  by_cases h : va < vb
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega : va + P256 - vb < P256)]; omega
  · rw [if_neg h, show va + P256 - vb = (va - vb) + P256 from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : va - vb < P256)]; omega
```
`lhs[k] = r[k] + b[k]`, `rhs[k] = a[k] + q·pConst[k]`.

### 5.3 `DivOrZero` — witnessed inversion

Circuit (`DivOrZero.lean:40-68`):
```
z ← IsZeroFe den
denSafe ← Mux { z, oneConst,  den }
numSafe ← Mux { z, zeroConst, num }
lam ← witness (emuOfNat ((numFp * denFp⁻¹).val))
Normalize lam ; LessThan { lam, pConst }
prod ← MulMod { lam, denSafe, pConst }
Equal { prod, numSafe }
return lam
```
Spec (`DivOrZero.lean:79-83`):
```lean
Fe.Valid out ∧ (decodeFe den ≠ 0 → decodeFe out * decodeFe den = decodeFe num)
             ∧ (decodeFe den = 0 → decodeFe out = 0)
```
**Pattern `guard-then-branch`.** Both soundness (`:85-133`) and completeness (`:135-223`) are a single `by_cases hd0 : decodeFe input_den = 0` with symmetric branches:
- zero branch: `rw [if_pos hd0] at hz; rw [hz, if_pos rfl, eval_oneConst] at hden; … rw [hden, value_emuOfNat_one] at hmul; rw [hnum, value_emuOfNat_zero] at heq` → `λ·1 ≡ 0` → `decodeFe_of_value_eq_zero`.
- nonzero branch: `rw [if_neg hd0] at hz; rw [hz, if_neg (zero_ne_one (α := F circomPrime))] at hden` → `mul_cast_of_mod_eq` (`DivOrZeroTheorems.lean:138-140`):
  ```lean
  lemma mul_cast_of_mod_eq {l d n : ℕ} (h : l * d % P256 = n) : (l : Fp) * (d : Fp) = (n : Fp) := by
    rw [← h, ZMod.natCast_mod, Nat.cast_mul]
  ```
Completeness certificate for the witness (`DivOrZeroTheorems.lean:151-162`):
```lean
lemma witness_cert_nonzero {nv dv : ℕ} (hnv : nv < P256) (hd : (dv : Fp) ≠ 0) :
    ((nv : Fp) * (dv : Fp)⁻¹).val * dv % P256 = nv
```
proved by `push_cast [ZMod.natCast_val, ZMod.cast_id]; rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]` then `calc` through `ZMod.val_natCast`.
And the degenerate case (`:144-146`): `witness_val_den_zero : (n * (0 : Fp)⁻¹).val = 0` by `rw [inv_zero, mul_zero, ZMod.val_zero]` — **relies on Mathlib's `0⁻¹ = 0` convention**, which is precisely what makes the gadget total.

Note the explicit hard-coded offsets in the proofs, e.g. `env.get (i₀ + 2+2+2+2+1+1)` (`:96`) and `i₀ + 11 + numLimbs + numLimbs + i` (`:160`) — the solution accepts concrete offsets rather than abstracting them.

### 5.4 `LessThan` — borrow chain

Circuit (`LessThan.lean:59-99`): witness `d = rhs − 1 − lhs` limbs, `Normalize d`, witness one carry bit per limb, boolean-constrain, assert per-limb `a[k] + d[k] + carry_in + [k=0] = b[k] + carry[k]·2^B` (the `+1` folded into limb 0's constant so every row stays **degree ≤ 1**), force top carry `= 0`.

Soundness (`:136-305`): identical `nat-indexed-shadow` + `per_limb_lift` (`Theorems.lean:1090-1120`) + `carry_telescope` + final `omega` structure, with `hd_nonneg : 0 ≤ ∑ Dn k * 2^(B*k) := Nat.zero_le _` as the slack that yields strict `<`.

Completeness (`:306-…`): uses `ripple_carry` (`Theorems.lean:949-1003`, the carry-is-a-bit induction), `ripple_eq` (`:1066-1088`, the per-limb recurrence via `Nat.mod_add_div'`), `digit_extract` (`:1007-1033`), `limb_stable` (`:1037-1063`).

### 5.5 `Normalize` (107 lines) — the shortest gadget

`Normalize.lean:60-71`:
```lean
soundness := by
  circuit_proof_start
  simp_all only [circuit_norm, Gadgets.ToBits.rangeCheck, BigInt.Normalized]
  intro i; rw [← h_input, Vector.getElem_map]; exact h_holds i
completeness := by
  circuit_proof_start
  simp_all only [circuit_norm, Gadgets.ToBits.rangeCheck, BigInt.Normalized]
  intro i; have := h_spec i; rwa [← h_input, Vector.getElem_map] at this
```
**Pattern `simp_all-then-getElem_map`** — the minimal 4-line gadget proof.

### 5.6 `Equal` (`Equal.lean:72-79`)

```lean
soundness := by circuit_proof_start; simp only [← h_input]; rw [h_holds]
completeness := by circuit_proof_start; simp only [← h_input] at h_assumptions h_spec
                   exact BigInt.value_inj h_assumptions.1 h_assumptions.2 h_spec
```
`BigInt.value_inj` (`Theorems.lean:252-273`): normalized big-ints with equal value are limb-equal. Built on `fromLimbs_injective` (`Theorems.lean:214-248`) — positional uniqueness by `congrArg (· % 2^B)` / `congrArg (· / 2^B)` and induction.

### 5.7 `Mux` — materialized selection (`Mux.lean`)

Docstring (`Mux.lean:9-16`) states the design rationale: Clean's stock `Conditional` returns *expressions* of degree `deg(sel)+max(deg t,deg f)`; `Mux` witnesses the result so **every gadget output in this solution is affine (degree 1)**. This single decision is what makes `isR1CS` provable at all.

Row: `out_i = sel·(t_i − f_i) + f_i`, one rank-1 row per element.
Soundness (`:64-83`): `rw [ProvableType.ext_iff]; intro i hi; have h := h_holds ⟨i,hi⟩; simp only [Vector.getElem_ofFn, Expression.eval, ProvableType.getElem_eval_toElements, …] at h; rcases h_assumptions with h0 | h1` then `rw [zero_mul, zero_add, neg_one_mul, add_neg_eq_zero] at h` / `rw [one_mul, neg_one_mul, neg_one_mul, add_neg_eq_zero, neg_add_cancel_right] at h`.
Completeness (`:85-103`): `rw [henv, h_selector]; rcases h_assumptions with h0 | h1 <;> … ring`.

### 5.8 `IsZeroFe` (`IsZeroFe.lean:25-79`)

`z = z0·z1·z2·z3` where `zi ← Gadgets.IsZeroField x[i]`, products materialized with `<==` (two intermediates `t01`, `t23`) to keep the result affine.
Soundness (`:47-63`) — **pattern `finite-case-blast`**:
```lean
rw [hz, ht01, ht23, hz0, hz1, hz2, hz3]
simp only [decodeFe_eq_zero_iff h_assumptions]
by_cases h0 : input[0] = 0 <;> by_cases h1 : input[1] = 0 <;>
  by_cases h2 : input[2] = 0 <;> by_cases h3 : input[3] = 0 <;> simp [h0,h1,h2,h3]
```
Supported by `IsZeroFeTheorems.lean`:
- `BigInt.value_eq_zero_iff` (`:20-33`): `value B x = 0 ↔ ∀ i, x[i] = 0`; via `Finset.sum_eq_zero_iff` + `Nat.mul_eq_zero` + `ZMod.val_eq_zero`.
- `decodeFe_eq_zero_iff` (`:41-59`): for `Fe.Valid x`, `decodeFe x = 0 ↔ (x[0]=0 ∧ x[1]=0 ∧ x[2]=0 ∧ x[3]=0)`; the `→` direction uses `Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp h) hx.2` and the `←` direction does `match i, hi with | 0,_ => … | 1,_ => … | 2,_ => … | 3,_ => …`.

### 5.9 `ToBytes` — the output boundary (`ToBytes.lean`, `ToBytesTheorems.lean`)

Witness 32 bytes, `rangeCheck 8` each, assert per-limb affine recomposition `limb_k = Σ_{t<8} byte_{8k+t}·2^{8t}`. **Byte-alignment (64 = 8·8) means there are no cross-limb carries** — the docstring (`ToBytes.lean:18-21`) calls this out, and each row's sides are `< 2^64 ≪ circomPrime`.

Pure cores:
- `eval_foldl_add` (`ToBytesTheorems.lean:35-42`): eval distributes over the affine `Fin.foldl`.
- `eval_row_iff` (`:47-57`): the assertZero row `⇔` field-level sum equation, usable in **both** proof directions — soundness does `rw [eval_row_iff] at h`, completeness does `rw [eval_row_iff]`.
- `byteSum_eq_limb` (`:65-80`), `sum_regroup` (`:84-100`), `value_limb_eq` (`:104-…`).
- `two_pow_64_lt_circomPrime : (2:ℕ)^64 < circomPrime := by decide` (`:27`).

---

## 6. `CompleteAdd` — the elliptic-curve case analysis

### 6.1 Formula

Complete affine formulas via **unconditional computation + flag muxing** (`CompleteAdd.lean:47-94`), 22 subcircuits:

```
dx ← SubMod {Q.x, P.x};  dy ← SubMod {Q.y, P.y}
sameX ← IsZeroFe dx
sy ← AddMod {P.y, Q.y};  oppY ← IsZeroFe sy
x1sq ← MulMod {P.x, P.x, pConst}
x1sq2 ← AddMod {x1sq, x1sq};  tNum ← AddMod {x1sq2, x1sq}   -- 3·x²  (a = 0 for secp256k1)
tDen ← AddMod {P.y, P.y}                                     -- 2·y
num ← Mux {sameX, tNum, dy};  den ← Mux {sameX, tDen, dx}
lam ← DivOrZero {num, den}
lamSq ← MulMod {lam, lam, pConst}
xs ← SubMod {lamSq, P.x};  x3 ← SubMod {xs, Q.x}
xd ← SubMod {P.x, x3};  yprod ← MulMod {lam, xd, pConst};  y3 ← SubMod {yprod, P.y}
cancel <== sameX * oppY
s1 ← Mux {cancel, infConst, ⟨x3, y3, 0⟩}
s2 ← Mux {Q.isInf, P, s1}
out ← Mux {P.isInf, Q, s2}
```
The mux nesting **mirrors the spec's match order** (`Challenge/Specs/Secp256k1.lean:81-92`) exactly: infinity-left, infinity-right, then `x`-equal → (`y = −y` → 𝒪 | tangent) | chord.

Spec (`CompleteAdd.lean:106-110`):
```lean
out.Valid ∧ decodePoint out = Specs.ShortWeierstrass.add Specs.Secp256k1.curve (decodePoint P) (decodePoint Q)
```

### 6.2 Soundness wiring (`CompleteAdd.lean:112-170`)

**Pattern `discharge-chain`.** 59 lines, no arithmetic: `circuit_proof_start [<18 unfold names>]`, one `obtain ⟨…22 names…⟩ := h_holds`, then one `obtain`/`have` per subcircuit discharging its `Assumptions` and naming its `Spec`:
```lean
obtain ⟨hdxv, hdxe⟩ := hdx ⟨hQx, hPx⟩
have hsameX' := hsameX hdxv
obtain ⟨hx1sqn, hx1sqe⟩ := hx1sq ⟨hPx.1, hPx.1, hpn, by rw [hpv]; exact hPx.2, …, by rw [hpv]; exact P256_pos⟩
rw [hpv] at hx1sqe
have hx1sqv : Fe.Valid _ := fe_valid_of_mod hx1sqn hx1sqe
have hx1sqd := decodeFe_of_mulmod hx1sqe
…
exact soundness_core h_assumptions.1 h_assumptions.2 hdxe hdye hsameX' … hout'
```
Glue lemmas that make this one-liner-per-step (`CompleteAddTheorems.lean`):
| lemma | line | role |
|---|---|---|
| `decodeFe_of_mulmod` | 105-109 | `value out = a*b % P256 → decodeFe out = decodeFe a * decodeFe b`; `rw [decodeFe ×3, hout, ZMod.natCast_mod, Nat.cast_mul]` |
| `fe_valid_of_mod` | 113-116 | `Normalized ∧ value = v % P256 → Fe.Valid` |
| `mulmod_assumptions` | 262-272 | packs the 6-conjunct `MulMod.Assumptions` for canonical operands; `refine ⟨…⟩ <;> rw [pConst_value env]; exacts [ha.2, hb.2, P256_pos]` |
| `isBool_ite` / `isBool_mul` / `isBool_of_eq_ite` / `isBool_of_eq_mul` | 224-252 | flag booleanity |
| `fe_valid_ite` / `fe_valid_of_eq_ite` | 240-258 | mux validity: `split <;> assumption` |
| `fe_valid_eval_zeroConst` | 96-99 | |

### 6.3 `soundness_core` — the value-level case analysis (`CompleteAddTheorems.lean:281-428`, 148 lines)

Signature takes **only decoded values and evaluated flags — no circuit plumbing** (explicit in the docstring at 274-279). Structure:

```
rcases hP.1 with hPinf | hPinf                     -- P.isInf = 0 | = 1
├─ P finite:  rw [hout, if_neg hPne1]
│  rcases hQ.1 with hQinf | hQinf
│  ├─ Q finite:  rw [hs2, if_neg hQne1, decodePoint_of_finite ×2, add_affine]
│  │  have hPc/hQc : decodeFe P.y ^ 2 = decodeFe P.x ^ 3 + 7 := (onCurve_iff _).mp (hP.2.2.2 hPinf)
│  │  by_cases hxx : decodeFe Q.x = decodeFe P.x
│  │  ├─ equal x:  have hsx : sameX = 1 := by rw [hsameX, hdx, if_pos (by rw [hxx, sub_self])]
│  │  │  by_cases hyy : decodeFe P.y + decodeFe Q.y = 0
│  │  │  ├─ opposite y  → cancel = 1 → 𝒪   (lines 333-339)
│  │  │  └─ doubling (tangent)             (lines 340-384)
│  │  └─ distinct x: chord                 (lines 385-420)
│  └─ Q = 𝒪: exact ⟨hP, by rw [decodePoint_of_isInf hQinf, decodePoint_of_finite hPinf, add_inf_right]⟩
└─ P = 𝒪: exact ⟨hQ, by rw [decodePoint_of_isInf hPinf, add_inf_left]⟩
```

**The tangent branch's crucial deduction (lines 346-356)** — recovering `Q = P` from `Q.x = P.x` and `not(P.y = −Q.y)`:
```lean
have hqy : decodeFe Q.y = decodeFe P.y := by
  rcases eq_or_eq_neg_of_sq_eq (show decodeFe Q.y ^ 2 = decodeFe P.y ^ 2 by rw [hQc, hPc, hxx]) with h | h
  · exact h
  · exact absurd (by rw [h]; ring) hyy
have hpy0 : decodeFe P.y ≠ 0 := fun h0 => hyy (by rw [hqy, h0, add_zero])
have h2py : decodeFe P.y + decodeFe P.y ≠ 0 := by rw [← two_mul]; exact mul_ne_zero two_ne_zero_fp hpy0
```
with `eq_or_eq_neg_of_sq_eq` (`:132-137`) proved by `have hz : (a-b)*(a+b) = 0 := by linear_combination h; rcases mul_eq_zero.mp hz`.

**Recovering the division from the multiplicative `DivOrZero` spec (lines 357-367):**
```lean
have hdenv : decodeFe denv = decodeFe P.y + decodeFe P.y := by rw [hden, if_pos hsx, htDen]
have hlam' : decodeFe lamv * (decodeFe P.y + decodeFe P.y) = x·x + x·x + x·x := by
  have h := hlam (by rw [hdenv]; exact h2py); rw [hdenv] at h; rw [h, hnum, if_pos hsx, htNum, hx1sq2, hx1sq]
have hslope : decodeFe lamv = 3 * decodeFe P.x ^ 2 / (2 * decodeFe P.y) := by
  rw [eq_div_iff (by rw [two_mul]; exact h2py)]; linear_combination hlam'
```
**Pattern `eq_div_iff + linear_combination`** — this is how the multiplicative circuit relation `λ·den = num` becomes the spec's division `λ = num/den`. Used twice (tangent line 365-367, chord line 398-401).

**Closure (on-curve preservation) via `linear_combination` with offline-computed cofactors** (`CompleteAddTheorems.lean:148-166`):
```lean
theorem chord_oncurve {K} [Field K] {x₁ y₁ x₂ y₂ s x₃ y₃ bb : K}
    (h₁ : y₁^2 = x₁^3 + bb) (h₂ : y₂^2 = x₂^3 + bb) (hne : x₂ - x₁ ≠ 0)
    (hs : s * (x₂ - x₁) = y₂ - y₁) (hx₃ : x₃ = s*s - x₁ - x₂) (hy₃ : y₃ = s*(x₁-x₃) - y₁) :
    y₃^2 = x₃^3 + bb := by
  subst hx₃; subst hy₃
  apply mul_left_cancel₀ hne
  linear_combination ((x₂-x₁) - (s*s - x₁ - x₂ - x₁)) * h₁
    + (s*s - x₁ - x₂ - x₁) * h₂
    + (s*s - x₁ - x₂ - x₁) * (y₁ + y₂ + s*(x₂-x₁)) * hs

theorem tangent_oncurve {K} [Field K] {x₁ y₁ s x₃ y₃ bb : K}
    (h₁ : y₁^2 = x₁^3 + bb) (hs : s * (2*y₁) = 3*x₁^2) (hx₃ …) (hy₃ …) : y₃^2 = x₃^3 + bb := by
  subst hx₃; subst hy₃
  linear_combination h₁ + (s*s - x₁ - x₁ - x₁) * hs
```
The comment at 139-143 says: *"Both are polynomial identities in the ideal generated by the hypotheses; the cofactors were computed offline (Vieta on the line-curve intersection cubic). The chord case needs one cancellation of the nonzero `x₂ − x₁`."*

These are **near-duplicates of the trusted spec's own `chord_onCurve_cubic` / `tangent_onCurve_cubic`** (`Challenge/Specs/Secp256k1.lean:59-76`) — the solution restates them with `s*s` instead of `s^2` to match the circuit's `MulMod` output shape. **This is a re-derivation, not a reuse: the solution does not import the spec's closure lemmas.**

Final assembly per branch (e.g. tangent, lines 377-384):
```lean
refine ⟨⟨Or.inl rfl, hx3v, hy3v, fun _ => ?_⟩, ?_⟩
· rw [onCurve_iff]; exact tangent_oncurve (s := decodeFe lamv) hPc (by linear_combination hlam')
    (by rw [hx3, hxs, hlamSq, hxx]) (by rw [hy3, hyprod, hxd])
· rw [decodePoint_mk_zero, tangent_eq]
  simp only [GroupPoint.affine.injEq, Point.mk.injEq]
  exact ⟨hX, hY⟩
```
where `tangent_eq` / `chord_eq` / `add_affine` / `add_inf_left` / `add_inf_right` (`:170-207`) are `rfl`-or-`simp` spec unfoldings.

### 6.4 Completeness (`CompleteAdd.lean:172-221`)

No case analysis at all. Just the same 22-step discharge chain keeping only the `Valid` half (`obtain ⟨hdxv, -⟩`), then a **single flat 5-line `exact ⟨…21 components…⟩`**. The `DivOrZero` totality is what removes the need for branching: `obtain ⟨hlamv, -, -⟩ := hlam ⟨hnumv, hdenv⟩` works unconditionally.

---

## 7. `Step` and `ScalarMul` — the loop

### 7.1 Loop shape

**Naive MSB-first double-and-add. No windowing, no precomputation, in *both* solutions.**

`Step.lean:31-40`:
```lean
doubled ← CompleteAdd { P := acc, Q := acc }      -- doubling = self-add (complete formula handles it)
added   ← CompleteAdd { P := doubled, Q := base } -- base = ⟨px, py, 0⟩
Mux { selector := bit, ifTrue := added, ifFalse := doubled }
```
Spec (`Step.lean:55-60`): `out.Valid ∧ decodePoint out = Specs.ShortWeierstrass.step curve {x := decodeFe px, y := decodeFe py} (decodePoint acc) (input.bit.val)`.

Rationale for extracting `Step` (docstring `Step.lean:12-16`): *"keeps the `Circuit.foldl` loop body a single `subcircuit` call, so the fold's `ConstantLength`/`ConstantOutput` synthesis stays trivial (inlining the three subcircuits blows the heartbeat budget)."*

`ScalarMul.lean:85-106`:
```lean
acc ← Circuit.foldlRange Specs.Secp256k1.scalarBits infConst
        (fun acc i => subcircuit Step.circuit { acc := acc, px := input.px, py := input.py, bit := input.bits[i] })
        (constantLength input)
xb ← ToBytes acc.x ; yb ← ToBytes acc.y
xm ← Mux { acc.isInf, zeroBytes, xb } ; ym ← Mux { acc.isInf, zeroBytes, yb }
return { x := ofFn fun i => xm[coordBytes-1-i], y := ofFn fun i => ym[coordBytes-1-i], isInf := acc.isInf }
```
The reversal `xm[31-i]` converts little-endian `ToBytes` output to the interface's big-endian SEC1 order. Docstring `ScalarMul.lean:31-33`: *"≈ 512 complete adds; this is a baseline, not a golfed solution."*

**`constantLength` (`ScalarMul.lean:57-76`)** is supplied explicitly because *"the default synthesis tactic times out unfolding the nested gadget tree (cf. the same pattern in Clean's `SHA256Schedule`)"*. Its proof is a single `simp` with ~25 unfold names ending in `secpParams, Gadgets.ToBits.rangeCheck, numLimbs, limbBits`; the value is the literal `31959`.

### 7.2 Composing per-step lemmas into the full theorem

**Pattern `accVar / specAcc mirrored ladders`** (`ScalarMulTheorems.lean`, mirrors `SHA256Rounds`/`valStateAfterRound` per the docstring at line 8-9):

```lean
def accVar (i₀ : ℕ) : ℕ → Var FlaggedPoint (F circomPrime)          -- :91-93
  | 0     => infConst
  | k + 1 => varFromOffset FlaggedPoint (i₀ + k * 31959 + 31950)

def specAcc (bits) (P) : ℕ → GroupPoint Fp                          -- :252-259
  | 0     => .infinity
  | k + 1 => if h : k < scalarBits then step curve P (specAcc bits P k) (bits[k]'h) else specAcc bits P k
```

Bridging lemmas:
| lemma | line | statement |
|---|---|---|
| `step_localLength` | 63-64 | `= 31959`, by `rfl` |
| `step_output` | 66-71 | `= varFromOffset FlaggedPoint (n + 31950)`; `show Step.elaborated.output …; simp only [Step.elaborated]; norm_num [secpParams, numLimbs, limbBits]; congr 1` |
| `fin_foldl_ignore_acc` | 101-104 | a `Fin.foldl` whose body ignores the accumulator returns the last value; `rw [Fin.foldl_succ_last]; simp` |
| `fin_foldl_eq_accVar` | 109-114 | the concrete `Fin.foldl` over step outputs `= accVar` |
| `foldlAcc_eq_accVar` | 122-132 | `Circuit.FoldlM.foldlAcc … = accVar i₀ i.val` |
| `foldlAcc_eq_accVar_main` | 137-148 | same, `Fin`-indexed binder, for `computableWitnesses` |
| `fin_foldl_goal_eq_accVar` | 224-246 | the **goal-side** form after numeral normalization (offset split as `15975 + 15975`) |
| `scalarMul_eq_specAcc` | 271-296 | `Specs.ShortWeierstrass.scalarMul curve bits P = specAcc bits P scalarBits` |
| `vector_foldl_eq_fin_foldl` | 261-268 | `v.foldl f init = Fin.foldl n (fun acc i => f acc v[i]) init` |

**Explicit comment on the alias trap** (`ScalarMulTheorems.lean:118-121`): *"Uses `FlaggedPoint (Expression (F circomPrime))` for the accumulator type (not the `Var FlaggedPoint (F circomPrime)` alias) so the pattern matches `h_holds` syntactically — `simp`/`rw` can't see through the alias in binder types."* **Three near-duplicate lemmas exist solely because of binder-type syntactic mismatch.**

**The fold induction** — split into two declarations for heartbeat budget (comment at `:395-399`):
- `fold_step` (`ScalarMulTheorems.lean:405-473`, `set_option maxRecDepth 8192`): carries a 5-conjunct invariant `⟨IsBool isInf, Fe.Valid x, Fe.Valid y, isInf=0 → OnCurve, decodePoint = specAcc … k⟩` from `k` to `k+1`. Body: `unfold Step.circuit Step.Assumptions Step.Spec FlaggedPoint.Valid at h_step; dsimp only [] at h_step`, discharge, then `simp only [accVar, specAcc, dif_pos hk'']` and `rw [hout_dec, ih_dec, hbits']`.
- `fold_invariant` (`:478-534`): `intro k hk; induction k with | zero => … evalInf_valid … | succ k ih => … exact fold_step … (h_steps ⟨k, hk''⟩)`.

**Instantiation in `ScalarMul.soundness` (`ScalarMul.lean:129-157`)**:
```lean
set_option maxRecDepth 8192 in
theorem soundness … := by
  circuit_proof_start
  obtain ⟨h_steps, h_tbx, h_tby, h_muxx, h_muxy⟩ := h_holds
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange] at h_steps
  simp only [circuit_norm] at h_steps
  simp only [step_localLength, step_output, fin_foldl_eq_accVar] at h_steps
  simp only [… toBytes_localLength, toBytes_output, mux_localLength, mux_output] at h_tbx h_tby h_muxx h_muxy
  norm_num [Specs.Secp256k1.scalarBits] at h_tbx h_tby h_muxx h_muxy
  simp only [secpParams, numLimbs, limbBits, scalarBits, coordBytes, List.sum_cons, List.sum_nil,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, reduceIte, reduceDIte,
    fin_foldl_goal_eq_accVar]
  obtain ⟨hbool, hfx, hfy, -, hdec256⟩ := fold_invariant … 256 (le_refl 256)
  unfold ToBytes.circuit ToBytes.Assumptions ToBytes.Spec at h_tbx h_tby
  unfold Mux.circuit Mux.Assumptions Mux.Spec at h_muxx h_muxy
  dsimp only [] at h_tbx h_tby h_muxx h_muxy
  obtain ⟨hxb_bytes, hxb_val⟩ := h_tbx hfx.1
  …
  exact ⟨⟨output_valid …, output_spec …⟩, fun i => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
```
**Pattern `normalize-hypotheses-and-goal-to-accVar-then-apply-invariant`.** Note the explicit numeral-normalization `simp only [… Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceLT, reduceIte, reduceDIte, …]` needed *before* `fin_foldl_goal_eq_accVar` will fire.

Output boundary (`ScalarMulTheorems.lean:538-696`), two `set_option maxRecDepth 8192` lemmas:
- `output_valid` (`:545-620`) — `rw [map_eval_ofFn_rev …, hmx, hmy]; simp only [Outputs.Valid]; rcases hbool with hinf0 | hinf1` then per-branch `coordVal` rewriting via `fromLimbs_rev_ofFn` (`:344-359`) / `fromLimbs_eval_zeroBytes` (`:382-393`).
- `output_spec` (`:624-694`) — `unfold Specs.Secp256k1ScalarMul.Spec Specs.ShortWeierstrass.Spec decodeOutput; rw [scalarMul_eq_specAcc, hmx, hmy]`, then the same `IsBool` split.

### 7.3 Group-theory connection

**No Mathlib elliptic curve.** The group law is the challenge's own `Specs.ShortWeierstrass` (`Challenge/Specs/Secp256k1.lean:5-125`): a plain `inductive GroupPoint | infinity | affine`, `def add` by explicit `if`-nesting, `def step`, `def scalarMul := bits.foldl (step c P) .infinity`. The only Mathlib inputs are `ZMod p` field structure, `linear_combination`, `ring`. The solution proves `decodePoint out = Specs.ShortWeierstrass.add curve (decodePoint P) (decodePoint Q)` — a *definitional* match against the spec's `if`-cascade, never an abstract group-law axiom. `Specs.Secp256k1.order` and `NoOrderTwo` exist in the spec but are **unused by the solutions**.

---

## 8. ScalarMul vs ScalarMulFixedBase — the actual difference

### 8.1 Technique

| | `Secp256k1ScalarMul` (variable base) | `Secp256k1ScalarMulFixedBase` |
|---|---|---|
| Interface `Input` | `bits : Vector F 256`, `px, py : Vector F 32` | `bits : Vector F 256` only |
| Interface `Assumptions` | `IsBits ∧ IsBytes px ∧ IsBytes py ∧ coordVal px < p ∧ coordVal py < p ∧ OnCurve …` | `IsBits input.bits` only |
| base-point plumbing | `packCoord : Vector (Expression _) 32 → Var Emu _` — a **pure affine reindexing, no constraints** (`Main.lean:29-38`) | `MainTheorems.gxConst / gyConst := emuConst gxNat / gyNat` — compile-time constant limbs (`MainTheorems.lean:58-61`) |
| on-curve obligation | assumed by the interface, transported by `decodeFe_pack` | **proved**: `MainTheorems.G_onCurve` (`:100-113`) |
| extra MainTheorems content | `pack`, `pack_getElem_val`, `pack_normalized`, `pack_value`, `pack_valid`, `decodeFe_pack`, `packCoordE`, `eval_packCoordE`, `coordVal_eq_le_sum`, `idx_lt` (≈130 lines) | `gxNat/gyNat`, `gxConst/gyConst`, `eval_*`, `fe_valid_*`, `decodeFe_*`, `G_onCurve` (≈60 lines) |
| `isR1CS` side condition | `affineW_packCoord` (`Main.lean:110-118`) — affine fold of affine input bytes, via `affine_finFoldl'` + `Affine.mul_deg0 … (degree_const _)` | `affineW_gxConst/gyConst` (`Main.lean:87-97`) — `Affine.const _` after `Vector.getElem_ofFn` |
| `affineInput_components` | returns `AffineW bits ∧ AffineW px ∧ AffineW py`; three `AffineW.left_of_append`/`right_of_append` peels (`Cost.lean:1489-1500` VB) | returns `AffineW input.bits`; one peel |
| `computableWitness` inner bridge | `simpa [circuit_norm] using congrArg (…x.bits)`, and packCoord evals from `h_input_eq` | `rw [MainTheorems.eval_gxConst, MainTheorems.eval_gxConst]` (constants are env-independent, so `rw` closes it) |

### 8.2 Cost — **identical**

Both `Main.lean` declare (VB `Main.lean:51-52`, FB `Main.lean:38-39`):
```lean
@[reducible] def allocations : Nat := 8182144
@[reducible] def constraints : Nat := 8279944
```
FixedBase docstring `Main.lean:35-37`: *"The generic double-and-add gadget allocates the same cells whether the base point is an input or a constant, so the cost matches the variable-base circuit."* Both `Cost.lean` are `scalarMulCost := ⟨8182144, 8279944⟩`.

**Key takeaway for the playbook: the "fixed base" instance yields NO cost savings in this reference solution — the same generic `ScalarMul.circuit` is invoked with constant limbs instead of packed input limbs.** No fixed-base precomputation table, no windowing. The technical saving is purely in the *proof* side: 6-conjunct interface assumptions collapse to 1, and the on-curve fact becomes a `by decide` ℕ-modular identity.

### 8.3 `G_onCurve` — the kernel-checkable point-on-curve proof

`MainTheorems.lean:100-113`:
```lean
lemma G_onCurve : Specs.ShortWeierstrass.OnCurve Specs.Secp256k1.curve Specs.Secp256k1.G := by
  have key : gyNat ^ 2 % Specs.Secp256k1.p = (gxNat ^ 3 + 7) % Specs.Secp256k1.p := by decide
  show Specs.Secp256k1.G.y ^ 2 = G.x ^ 3 + curve.a * G.x + curve.b
  rw [show curve.a = 0 from rfl, show curve.b = (7 : Fp) from rfl, zero_mul, add_zero,
      ← gxNat_cast, ← gyNat_cast]
  have hcast : ((gyNat ^ 2 : ℕ) : Fp) = ((gxNat ^ 3 + 7 : ℕ) : Fp) := by
    rw [ZMod.natCast_eq_natCast_iff]; exact key
  rwa [Nat.cast_pow, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at hcast
```
**Pattern `nat-mod-decide-then-ZMod.natCast_eq_natCast_iff`.** Docstring: *"discharged by `decide` (kernel `Nat` arithmetic, never `native_decide`)."* Note this is a `decide` on `gyNat^2 % p` where `gyNat ≈ 2^256` — a 512-bit kernel computation.

Also `gxNat_cast / gyNat_cast : ((gxNat : ℕ) : Fp) = Specs.Secp256k1.G.x := by rfl` (`:64-67`) — `rfl` works because both are literal numerals.

---

## 9. `[VB]` The unused lazy-reduction layer

`Secp256k1ScalarMul/{AddModL,SubModL,MulModL,MulModLTheorems}.lean` (1177 lines, fully proved, **imported by nothing in the dependency path** — verified: only `SubModL` imports `AddModL`, only `MulModL` imports `MulModLTheorems`; `CompleteAdd`/`ScalarMul`/`Main` never import them).

Design (docstring `AddModL.lean:5-20`): drop the `LessThan` canonical check; output only `Normalized` (`< 2^256`), spec at `Fp` level via `decodeFe` (insensitive to residue choice). *"Intermediate values flow uncanonicalized and are only reduced where a comparison or the final output needs it."*

Technical deltas vs the eager gadgets:
- Quotient is no longer boolean: `q ∈ {0,1,2}` → `Gadgets.ToBits.rangeCheck 2 (by decide) q` instead of `assertZero (q*(q-1))` (`AddModL.lean:127-129`).
- All `qN ≤ 1` bound lemmas reproved under `qN ≤ 3`: `val_q_mul_limb3` (`AddModL.lean:31-42`), `AddModL.rhs_bounds3` (`:45-…`), `AddModL.polyValue_rhs3` (`:78-…`), `SubModL.rhs_bounds3` (`SubModL.lean:30-…`), `SubModL.polyValue_rhs3` (`:66-…`). Field-fit bound `3 * 2^limbBits < circomPrime` by `decide`.
- `SubModL` borrow can be 2: `def subQ (va vb) := if va < vb then (if vb - va ≤ P256 then 1 else 2) else 0` (`SubModL.lean:112`), with `subQ_le3`, `subLe`, `subR_lt`, `subR_add` (`:117-144`) all `unfold; split <;> [split; skip] <;> omega` + `have hM2p : 2^(limbBits*numLimbs) < 2*P256 := by decide`.
- `MulModL` (`MulModL.lean:28-56`): `Assumptions := Fe.Valid a ∧ b.Normalized limbBits` (asymmetric — `a` canonical, `b` loose); modulus is `pConst` directly in `witnessedMul q pConst`; **no `LessThan r n`** step at all. Its `elaborated` is written by hand (not `elaborate_circuit`) with explicit `localLength`/`output_eq`.
- `MulModLTheorems.lean` mirrors the four `MulMod` cores as `*_loose` variants (`mulMod_soundness_core_loose` `:33`, `_wm_loose` `:130`, `mulMod_completeness_core_loose` `:175`, `_wm_loose` `:311`).
- `MulModL.circuit` carries `set_option maxHeartbeats 1000000` (`MulModL.lean:83`) — the only heartbeat raise anywhere in the corpus.

**Playbook value:** this is the shape a *golfed* solution would take. The reference authors built it, proved it, and did not wire it in.

---

## 10. `mainCost` — proof patterns

### 10.1 Architecture

`Cost.lean` is a **bottom-up ladder of `CostIs` certificates**, one per gadget, each of the form:
```lean
theorem costIs_<gadget> (input) : CostIs (<Gadget>.main input) <count> := by
  rw [show <count> = <syntactic sum of child counts> from by decide]   -- or `count_eq …`
  unfold <Gadget>.main
  refine CostIs.bind (costIs_<child1> _) fun v1 => ?_
  refine CostIs.bind (costIs_<child2> _) fun v2 => ?_
  …
  exact CostIs.pure _
theorem costIs_sub_<gadget> (b) : CostIs (subcircuit <Gadget>.circuit b) <count> :=
  CostIs.subcircuit (fun n => costIs_<gadget> b n)
```

Count table (`Cost.lean:19-35`, header, "verified against `#eval! operationCount` of the actual circuits"):
```
IsZeroField 2/2  |  IsZeroFe 11/11 |  Mux M   size M / size M |  Normalize 256/260
Equal 0/4        |  LessThan 264/269 | EqViaCarries 490/498  |  MulMod 1306/1319
AddMod 1015/1028 |  SubMod 1015/1028 | DivOrZero 1849/1871   |  ToBytes 288/292
CompleteAdd 15975/16166 | Step 31959/32341 | ScalarMul 8182144/8279944
```

### 10.2 Count-decomposition idioms

Two forms:
- **`by decide`** on concrete counts: `rw [show completeAddCost = ⟨1015,1028⟩ + (⟨1015,1028⟩ + (⟨11,11⟩ + … + Count.zero)) … from by decide]` (`Cost.lean:1212-1217`, a 6-line nested sum of 22 terms).
- **symbolic**, via `congr 1` on projections: `Cost.lean:312-315`
  ```lean
  rw [show (⟨m + m*P.B + m, m*(P.B+1) + m + m + 1⟩ : Count) = ⟨m,0⟩ + (…) from by
        simp only [Count.zero]; congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  ```
  or via the helper `count_eq (a c : ℕ) (ha : x.allocations = a) (hc : x.constraints = c) : (⟨a,c⟩ : Count) = x` (`Cost.lean:600-602`, `cases x; cases ha; cases hc; rfl`), used e.g. for `Mux` (`:771-774`).

### 10.3 Leaf certificates

| leaf | line | statement / proof |
|---|---|---|
| `CostIs.provableWitness` | 51-54 | `⟨size α, 0⟩`; `intro n; rfl` |
| `CostIs.subcircuitWithAssertion` | 72-89 | reduces a `GeneralFormalCircuit` invocation to its main's count; via `nestedCount`, `Lemmas.operationCount_toNested` |
| `costIs_toBits` | 111-129 | `⟨n, n+1⟩` |
| `costIs_rangeCheck` | 193-197 | `simpa [Count.add_zero] using CostIs.bind …` |
| `costIs_assertEqField` (`===`) | 639-646 | `⟨0,1⟩`; `unfold Expression.assertEquals; refine CostIs.assertion …; simpa using CostIs.forEach (m := 1) …` |
| `costIs_assignEqField` (`<==`) | 662-666 | `⟨1,1⟩` = witness + one row |
| `costIs_mux` | 767-778 | `⟨size M, size M⟩` |
| `costIs_witnessedMul` | 482-491 | `⟨m*m, m*m⟩` |

Note the **`Var field` duplication** (`Cost.lean:680-722`): `===`/`<==` on `Var field _` resolve to a *different* instance than on `Expression _`, so `costIs_assertEqFieldM` / `costIs_assignEqFieldM` / `isR1CS_assertEqFieldM` / `isR1CS_assignEqFieldM` / `affine_assignEqFieldM_output` all exist as near-clones. Docstring at 680-684 explains: *"same operations, different terms."*

### 10.4 The fold

`Cost.lean:1372-1383`:
```lean
theorem costIs_scalarMul (input) : CostIs (ScalarMul.main input) scalarMulCost := by
  rw [show scalarMulCost = ⟨256*31959, 256*32341⟩ + (⟨288,292⟩ + (⟨288,292⟩ + (⟨32,32⟩ + (⟨32,32⟩ + Count.zero)))) from by decide]
  unfold ScalarMul.main
  refine CostIs.bind (CostIs.foldlRange fun s i n => costIs_sub_step _ n) fun acc => ?_
  …
```
`CostIs.foldlRange` handles the 256 iterations in one line.

### 10.5 Top level

`Main.lean:102-109`:
```lean
private theorem costIs_main (input) : CostIs (main input) ⟨allocations, constraints⟩ := by
  rw [show (⟨allocations, constraints⟩ : Count) = scalarMulCost + Count.zero from by decide]
  unfold main
  exact CostIs.bind (costIs_sub_scalarMul _) fun out => CostIs.pure _
theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ := fun input => costIs_main input
```
`mainCost` is literally `fun input => costIs_main input`.

---

## 11. `isR1CS` — proof patterns

### 11.1 The affineness discipline

Everything hinges on: **every gadget output is a fresh witness cell (or a linear form over fresh cells), hence `Affine`.** Predicates:
- `Affine e` (single expression), `AffineW v` (vector of expressions, `∀ i hi, Affine v[i]`), `AffineProvable v` (provable-type instance), `AffineFP v` (FlaggedPoint triple, `Cost.lean:1154-1157`).
- Conversions: `AffineW.affineProvable`, `AffineProvable.affineW`, `AffineFP.affineProvable` (`Cost.lean:1191-1196`), `AffineFP.of_affineProvable` (`:1159`), `AffineW.append` (`:1173`), `AffineW.left_of_append` / `right_of_append`, `affineW_singleton` (`:1183`).

Per-gadget output-affineness lemmas (all trivially `simp only [circuit_norm, subcircuit, X.circuit, X.elaborated]` then `affineW_varFromOffset _ _` / `Affine.var _`):
`affineW_sub_mulMod` (594), `affine_sub_isZeroFe` (863), `affineW_sub_addMod` (958), `affineW_sub_subMod` (1024), `affineW_sub_divOrZero` (1095), `affineW_sub_toBytes` (1145), `affineProvable_sub_mux` (812), `affineFP_sub_completeAdd` (1313), `affineFP_sub_step` (1360), `affineOut_sub_scalarMul` (1468).

### 11.2 Row shape lemmas

Four hand-built `isR1CSRow` certificates, each an explicit `r1csProducts` computation with a `rcases … with h | h` on whether the product contributes 0 or 1:

| lemma | line | row shape | used by |
|---|---|---|---|
| `isR1CSRow_mul_sub` | 445-453 | `A*B − C` | `witnessedMul` product asserts |
| `isR1CSRow_mul_add_sub` | 608-619 | `A*B + C − D` | `Mux` row `sel·(t−f)+f−out` |
| `isR1CSRow_sub_one_sub_mul` | 623-634 | `w − (1 − A*B)` | `IsZeroField` assignment row |
| (trusted) `isR1CSRow_mul`, `isR1CSRow_of_affine`, `isR1CSRow_sub_mul` | — | | booleanity rows, affine rows, `w − A*B` |

Proof template (`Cost.lean:610-619`):
```lean
rcases r1csProducts_mul_affine hA hB with h | h
· refine isR1CSRow_of_r1csProducts (k := 0) ?_ (by omega)
  show r1csProducts (A * B + C + -D) = some 0
  rw [r1csProducts_add, r1csProducts_add, r1csProducts_neg, h, r1csProducts_of_affine hC, r1csProducts_of_affine hD]
· refine isR1CSRow_of_r1csProducts (k := 1) ?_ (by omega)   -- same body, `some 1`
```

**Critical hygiene note (`Cost.lean:143`, `Main.lean:84`):**
```lean
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS
```
with comment: *"Keep the trusted R1CS predicates opaque while applying the per-gadget certificates: otherwise the unifier evaluates `r1csProducts` on the asserted expressions and loops on neutral subterms."*

### 11.3 `IsR1CSCirc.forEach_mem` — the indexed forEach

`Cost.lean:134-141`:
```lean
theorem IsR1CSCirc.forEach_mem {α} {m} [Inhabited α] {xs : Vector α m} {body} {constant}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n; rw [Circuit.forEach.operations_eq]; exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)
```
Docstring: *"the generic `IsR1CSCirc.forEach` quantifies over all element values, too weak for booleanity rows."* **Used ~10× — every `forEach` in the tree goes through this.**

### 11.4 Per-gadget shape

Same `refine IsR1CSCirc.bind_out (isR1CS_sub_<child> _ <affineness args>) fun n<child> => ?_` chain, threading affineness of every prior output. Example `isR1CS_completeAdd` (`Cost.lean:1243-1299`) — 22 binds, each carrying explicit affineness witnesses like `(affineW_sub_mulMod secpParams _ nx1)`, `(affineProvable_sub_mux _ nnum).affineW`, `(affine_sub_isZeroFe _ nsx)`.

Handling non-fresh rows inside a gadget requires an explicit `change`:
```lean
intro i hi
change Affine (varFromOffset (BigInt numLimbs) nr : Var (BigInt numLimbs) (F circomPrime))[i]
exact affineW_varFromOffset _ _ i hi
```
(`Cost.lean:927-929`, `1066-1068`, `1070-1072`, `1075-1077`, `576-577`) — recurring 3-line boilerplate.

### 11.5 The fold's R1CS proof — `bind_out_inv`

`Cost.lean:1404-1412`:
```lean
theorem IsR1CSCirc.bind_out_inv {α β} {f : Circuit _ α} {g : α → Circuit _ β} (P : α → Prop)
    (hf : IsR1CSCirc f) (hout : ∀ n, P (f.output n)) (hg : ∀ a, P a → IsR1CSCirc (g a)) :
    IsR1CSCirc (f >>= g) := by
  intro n; rw [Circuit.bind_operations_eq, Lemmas.operationsIsR1CS_append]; exact ⟨hf n, hg _ (hout _) _⟩
```
Docstring: *"the continuation only sees an opaque value satisfying the invariant `P`, never the (possibly huge) output term itself — this keeps the 256-step fold output from ever being whnf-ed during unification."*

Used at `Cost.lean:1419-1424`:
```lean
refine IsR1CSCirc.bind_out_inv AffineFP ?_ ?_ fun acc hacc => ?_
· exact IsR1CSCirc.foldlRange_inv AffineFP affineFP_infConst
    (fun s i hs => isR1CS_sub_step _ hs hpx hpy (hbits i.val i.isLt))
    (fun s i k hs => affineFP_sub_step _ k)
· exact fun n => affineFP_foldlRange_output affineFP_infConst (fun s i k hs => affineFP_sub_step _ k) n
```
Plus `affineFP_foldlRange_output` (`Cost.lean:1388-1398`) using `finFoldl_invariant AffineFP _ _ hinit fun acc i h => hstep _ _ _ h`.

**Pattern name: `invariant-carrying fold certificate` — `AffineFP` is the loop invariant for both the R1CS and the output-affineness sides.**

### 11.6 Top level

`Main.lean:114-139` (FixedBase):
```lean
private theorem isR1CS_main_param (input) (hbits : AffineW input.bits) : IsR1CSCirc (main input) := by
  unfold main
  refine IsR1CSCirc.bind_out (isR1CS_sub_scalarMul _ ?_ ?_ ?_) fun nout => ?_
  · exact fun i hi => hbits i hi
  · exact affineW_gxConst
  · exact affineW_gyConst
  exact IsR1CSCirc.pure _
theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc (fun input hinput => isR1CS_main_param input (affineInput_components input hinput))
                       (fun input _ => affineOutput_main input)
```

---

## 12. `computableWitness` — proof patterns

### 12.1 Uniform skeleton (every gadget)

```lean
theorem computableWitnesses : circuit.ComputableWitnesses := by
  intro offset input env env'
  change Operations.forAllFlat offset
    (Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnessCondition input env env')
    ((main input).operations offset)
  apply Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [ …Circuit.bind_structuralComputableWitnesses_iff,
              …Circuit.provableWitness_structuralComputableWitnesses_iff,
              …Circuit.witnessVector_structuralComputableWitnesses_iff,
              …Circuit.forEach_structuralComputableWitnesses_iff,
              …FormalAssertion.assertion_structuralComputableWitnesses_iff,
              …FormalCircuit.subcircuit_structuralComputableWitnesses_iff,
              …Circuit.assertZero_structuralComputableWitnesses_iff,
              …Circuit.pure_structuralComputableWitnesses_iff, and_true ]
  and_intros   -- or refine ⟨?_, …⟩
  · <one goal per witness/subcircuit>
theorem computableWitness : ∀ n input, ProverEnvironment.OnlyAccessedBelow n (fun env => eval env input) →
    Circuit.ComputableWitnesses (main input) n :=
  Challenge.Utils.ComputableWitnessLemmas.FormalCircuitBase.computableWitnesses_implies (circuit := circuit.base) computableWitnesses
```
Instances: `Normalize.lean:73-101`, `Equal.lean:81-112`, `Mux.lean:109-136`, `EqViaCarries.lean:554-653`, `MulMod.lean:509-696`, `AddMod.lean:170-370`, `SubMod.lean`, `IsZeroFe.lean`, `DivOrZero.lean:261-…`, `ToBytes.lean`, `CompleteAdd.lean:296-…`, `Step.lean:124-193`, `ScalarMul.lean:244-341`, `Main.lean:152-216`.

### 12.2 Three recurring sub-patterns

**(a) `<witness generator reads only the input>` — the "stable" lemma family.** Each gadget defines an `eval*_stable` lemma showing its witness generator's ℕ-argument is env-invariant given `eval env x = eval env' x`:
- `evalEmu_stable` (`AddMod.lean:108-123`, duplicated in `SubMod.lean:102-117`), `MulMod.evalValue_stable` (`MulMod.lean:161-175`), `xInvCompute_stable` (`IsZeroFe.lean:188-194`), `Params.evalEmu_eq_of_eval_eq` (`Params.lean:97-112`).
All share the body:
```lean
have hmap : x.map (Expression.eval env.toEnvironment) = x.map (Expression.eval env'.toEnvironment) := by
  apply Vector.ext; intro i hi; simp only [Vector.getElem_map]
  have hi_eq := congrArg (fun y : Emu (F circomPrime) => y[i]) h
  change (eval env x)[i] = (eval env' x)[i] at hi_eq
  rw [← ProvableType.getElem_eval_fields_prover (env := env) x i hi,
      ← ProvableType.getElem_eval_fields_prover (env := env') x i hi] at hi_eq
  exact hi_eq
simp [evalEmu, hmap]
```
**`ProvableType.getElem_eval_fields_prover` is the workhorse lemma for prover-env element access** (appears ~18×).

**(b) `<prior output is stable>` — the `eval_output_of_agreesBelow` family.** Ten gadgets export one (`AddMod`, `SubMod`, `MulMod`, `Mux`, `IsZeroFe`, `DivOrZero`, `ToBytes`, `CompleteAdd`, `Step`, `ScalarMul`). Canonical form (`Mux.lean:143-156`):
```lean
lemma eval_output_of_agreesBelow (input) {offset k} {env env'}
    (h_agree : env.AgreesBelow k env') (hk : offset + size M ≤ k) :
    eval env ((main input).output offset) = eval env' ((main input).output offset) := by
  have hout : (main input).output offset = varFromOffset M offset := rfl
  rw [hout, CircuitType.eval_expression_prover_to_verifier, …, ProvableType.ext_iff]
  intro i hi
  rw [← ProvableType.getElem_eval_toElements … , ← …]
  simp only [varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange, Expression.eval]
  exact h_agree (offset + i) (by omega)
```

**(c) `<offset arithmetic>` — hard-coded concrete offsets.** Because every gadget has constant `localLength`, offsets are literal numerals asserted by `rfl`:
```lean
have hsub : ∀ X o, (subcircuit SubMod.circuit X).localLength o = 1015 := fun _ _ => rfl
have hmul : ∀ X o, (subcircuit (MulMod.circuit secpParams) X).localLength o = 1306 := fun _ _ => rfl
have hdiv : ∀ X o, (subcircuit DivOrZero.circuit X).localLength o = 1849 := fun _ _ => rfl
have hisz : ∀ x o, (subcircuit IsZeroFe.circuit x).localLength o = 11 := fun _ _ => rfl
```
(`CompleteAdd.lean:304-317`); `Step.lean:133-134` (`= 15975`); `ScalarMul.lean:249-263` (`= 31959`, `288`, `32`, and the fold `= 8181504` by `simp only [Circuit.foldlRange.localLength_eq, scalarBits, hstep, Nat.reduceMul]; rw [dif_pos (show (256:ℕ) > 0 by norm_num)]`).

Bridging `(main input).output` vs `circuit.output` — `Step.lean:116-122`:
```lean
private lemma completeAdd_output_stable (X) {o k} {env env'} (h_agree) (hk : o + 15975 ≤ k) :
    eval env (CompleteAdd.circuit.output X o) = eval env' (CompleteAdd.circuit.output X o) := by
  have h := CompleteAdd.eval_output_of_agreesBelow X (offset := o) h_agree hk
  rw [CompleteAdd.elaborated.output_eq X o] at h
  exact h
```
Docstring explains: *"bridging the two via `exact` would force an expensive `whnf` of the whole `CompleteAdd.main`, so we cross the gap once here with the cheap `elaborated.output_eq`."*

### 12.3 Opacity guards

Three sites use `attribute [local irreducible]` for `computableWitnesses`:
- `MulMod.lean:507`: `attribute [local irreducible] witnessedMul Normalize.circuit EqViaCarries.circuit LessThan.circuit` — *"so `bind`/`provableWitness`/`assertion` do not recurse into their internal witnesses."*
- `ScalarMul.lean:228`: `attribute [local irreducible] main`.
- `Main.lean:150`: `attribute [local irreducible] main ScalarMul.circuit ScalarMul.main` — *"unifying the structural goal against the subcircuit lemma would otherwise `whnf` the 256-step fold and overflow the kernel."*

### 12.4 Top-level `computableWitness` (`Main.lean:152-216`) — the only bespoke one

Unlike the gadgets, `Main.computableWitness` cannot use `computableWitnesses_implies` (no bundled `formalCircuit`; see `Main.lean:220-223`). It does the reduction manually:
```lean
intro n input hinput env env'
change (main input).operations n |>.forAllFlat n { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
have hstruct : …StructuralComputableWitnesses input env env' n ((main input).operations n) := by
  unfold main; simp only [bind_…_iff, subcircuit_…_iff, pure_…_iff, and_true]
  refine …FormalCircuit.subcircuit_flatStructuralComputableWitnesses ScalarMul.circuit input
    { bits := input.bits, px := gxConst, py := gyConst } n ?_ ScalarMul.computableWitnesses env env'
  intro e1 e2 h_input_eq
  simp only [circuit_norm, ScalarMul.Inputs.mk.injEq]
  refine ⟨simpa … congrArg (…x.bits) h_input_eq, rw [eval_gxConst, eval_gxConst], rw [eval_gyConst, eval_gyConst]⟩
have hflat := …forAllFlat_of_structuralComputableWitnesses input env env' hstruct
unfold …computableWitnessCondition at hflat
rw [← Operations.forAll_toFlat_iff] at hflat ⊢
apply FlatOperation.forAll_implies (F := F Interface.circomPrime) n ?_ hflat
have himplies : ∀ ops off, n ≤ off → FlatOperation.forAll off (Condition.implies … targetCondition).ignoreSubcircuit ops := by
  intro ops off hoff
  induction ops generalizing off with
  | nil => simp [FlatOperation.forAll]
  | cons op ops ih => cases op with
    | witness m compute => …; constructor
        · intro hparent hagree; exact hparent hagree (hinput env env' (ProverEnvironment.agreesBelow_of_le hagree hoff))
        · exact ih (m + off) (by omega)
    | assert e | lookup l | interact i => …; exact ⟨by intro _; trivial, ih off hoff⟩
exact himplies ((main input).operations n).toFlat n (le_refl n)
```
**Pattern `manual-condition-weakening-by-list-induction`** — discharges the `OnlyAccessedBelow n` hypothesis on every witness leaf.

---

## 13. Recurring helper-lemma index

### 13.1 `Theorems.lean` (the shared pure layer, namespace `Solution.<X>`)

| name | line | statement | role |
|---|---|---|---|
| `Limbs.fromLimbs` | 32 | `foldr (fun l acc => l + acc*2^B) 0` | limb denotation |
| `BigInt.value` / `.Normalized` | 195 / 199 | | denotation / range invariant |
| `fromLimbs_injective` | 214-248 | positional uniqueness | `Equal` completeness |
| `BigInt.value_inj` | 252-273 | normalized + equal value ⇒ limb-equal | `Equal` completeness |
| `fromLimbs_eq_sum` | 281-302 | `= ∑ i, l[i]*2^(B*i)` | everywhere |
| `BigInt.value_eq_sum` | 306-318 | positional-sum form | ~20 uses |
| `sum_lt_pow` | 322-342 | `∀ i, f i < 2^B → ∑ f i·2^{Bi} < 2^{Bn}` | value bounds |
| `BigInt.value_lt` | 346-349 | `Normalized ⇒ value < 2^{Bm}` | |
| `limb_decomp_mod` | 353-374 | `∑_{i<m} (N/2^{Bi} % 2^B)·2^{Bi} = N % 2^{Bm}` | witness value proofs |
| `BigInt.value_mapRange` | 378-397 | witnessed canonical digits denote `N` | MulMod/AddMod/SubMod completeness |
| `bigIntMulNoReduce` | 410-419 | schoolbook convolution (`Expression`s) | |
| `polyValue` | 423-424 | `∑ coeffs[i].val·2^{Bi}` | `EqViaCarries` spec |
| `bigIntMulVars` | 455-469 | convolution over witnessed products (**affine**) | R1CS cleanliness |
| `vector_foldl_finRange` | 427-435 | `Vector.foldl … (finRange n) = Fin.foldl n` | |
| `foldl_dif_add_eq_sum` | 439-448 | guarded `Fin.foldl` = guarded `Finset.sum` | |
| `eval_bigIntMulNoReduce_coeff` / `eval_bigIntMulVars_coeff` | 473-487 / 492-517 | evaluated coefficient as guarded sum | |
| `map_eval_bigIntMulVars_eq` | 524-546 | **eval bridge** vars ↦ schoolbook | |
| `val_bigIntMulNoReduce_coeff` | 550-598 | `.val` = ℕ convolution (no wrap) | |
| `val_bigIntMulNoReduce_coeff_lt` | 604-639 | coefficient `< m·2^{2B}` | `EqViaCarries` assumptions |
| `cauchy_inner_reindex` | 643-663 | `j = k−i` reindex (`Finset.sum_nbij'`) | |
| `cauchy_base_pow` | 668-702 | ℕ Cauchy product | |
| `polyValue_bigIntMulNoReduce` | 712-752 | **the multiply bridge** | MulMod |
| `evalPartial` | 756-759 | partial LE value (witness-side only) | EqViaCarries witness |
| `partial_div_bound` | 764-795 | carry magnitude ≤ `(m+1)·2^{B+1}` | EqViaCarries completeness |
| `partial_mod_stable` | 799-821 | higher limbs don't affect low mod | " |
| `quot_step` | 825-835 | running-quotient step | " |
| `carry_telescope` | 841-856 | carry-in sum + top = carry-out sum | EqViaCarries + LessThan soundness |
| `geom_shift` | 860-873 | `2^B·G = G + 2^{Bn} − 1` | EqViaCarries soundness |
| `carryOffset` | 879 | `(m+1)·2^{B+1}` | |
| `BigIntParams` | 887-903 | 8-field param bundle | |
| `per_index_lift` | 905-936 | field→ℕ per-index lift | EqViaCarries |
| `ripple_carry` | 949-1003 | carry is a bit + recurrence | LessThan completeness |
| `digit_extract` | 1007-1033 | `k`-th digit of a normalized sum | " |
| `limb_stable` | 1037-1063 | adding higher limb preserves digit `k` | " |
| `ripple_eq` | 1066-1088 | `g k + cin = limb + cout·2^B` | " |
| `per_limb_lift` | 1090-1120 | field→ℕ per-limb lift | LessThan soundness |
| `assertBoolComputableWitnesses` / `equalityComputableWitnesses` / `rangeCheckComputableWitnesses` | 44 / 56 / 72 | leaf computable-witness certs | |

### 13.2 Duplicated helper clusters (copy-paste across gadget files)

The following **near-identical blocks appear in 3–5 files each**, differing only in namespace:

| block | copies |
|---|---|
| `P256_pos`, `P256_lt`, `two_pow_limb_lt`, `limbOfNat_lt`, `val_limbOfNat`, `emuOfNat_getElem`, `emuOfNat_normalized`, `value_emuOfNat` | `AddModTheorems.lean:20-66`, `DivOrZeroTheorems.lean:24-67`, `CompleteAddTheorems.lean:25-64` |
| `eval_emuConst_getElem`, `eval_emuConst`, `pConst_normalized`, `pConst_value` | `AddModTheorems.lean:79-97`, `DivOrZeroTheorems.lean:79-114`, `CompleteAddTheorems.lean:70-93` |
| `emuWitnessOutput_stable` | `AddMod.lean:125-139`, `SubMod.lean:119-…`, `DivOrZero.lean:232-246` |
| `evalEmu_stable` | `AddMod.lean:108-123`, `SubMod.lean:102-117` |
| `equalityComputableWitnesses (M : TypeMap)` | `Theorems.lean:56`, `Equal.lean:29-42`, `IsZeroFe.lean:81-94` |
| `fpVar_stable` | `Step.lean:204-217`, `ScalarMulTheorems.lean:154-169` |
| `expression_stable_of_field_eval_eq` | `IsZeroFe.lean:178-186`, `CompleteAdd.lean:273-281` |
| `isBool_of_val_lt_two`, `outputValid_of_valid`, `decodeOutput_eq`, `foldl_base256_eq_fromLimbs`, `coordVal_eq` | `MainTheorems.lean` both variants |

**Playbook signal: the reference solutions accept substantial helper duplication rather than build a shared prelude — namespace hygiene ("solutions must be independent, so it is duplicated rather than imported", `ScalarMul.lean:36-39`) dominates DRY.**

---

## 14. Tactic vocabulary — frequency counts (FixedBase tree, 26 files, 12,712 lines)

```
set              483    obtain           142    ring              95
omega            330    Finset.sum_congr  63    decide            61
by decide         55    simp only [circuit_norm] 50   rcases      44
circuit_proof_start 36  ZMod.natCast_zmod_val 26   norm_num        24
ZMod.val_natCast_of_lt 21   Nat.mod_eq_of_lt 17   push_cast       14
positivity        11    elaborate_circuit  10    maxRecDepth      10
nlinarith          8    linarith           8    linear_combination 5
irreducible        5    convert            4    clear_value       2
field_simp         0    maxHeartbeats      0    native_decide     0 (real)
```

### Per-obligation vocabulary

| obligation | core tactics | closing moves |
|---|---|---|
| **soundness** (limb arithmetic) | `circuit_proof_start [<unfolds>]`, `obtain` on `h_holds`, `set … : ℕ → ℕ := fun k => if h : k < n then … else 0 with h…`, `rw [← h_input]; simp [Vector.getElem_map]`, `split <;> simp [circuit_norm, sub_eq_add_neg]`, `rw [← sub_eq_zero]; rw [← hlin]; ring` | **`omega`** after weighted-sum distribution; `per_index_lift` / `per_limb_lift`; `remainder_eq`; `nlinarith [Nat.two_pow_pos …]` for pow-multiplied bounds |
| **soundness** (EC/field-level) | `rcases hP.1 with hPinf \| hPinf`, `by_cases hxx : decodeFe Q.x = decodeFe P.x`, `rw [if_pos/if_neg …]`, `decodePoint_of_finite/of_isInf`, `add_affine/add_inf_left/add_inf_right` | **`linear_combination`** (5 uses: 2 closure lemmas, 2 slope derivations, 1 `eq_or_eq_neg_of_sq_eq`), `eq_div_iff`, `mul_left_cancel₀`, `ring` |
| **soundness** (fold) | `simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]`, `simp only [circuit_norm]`, `simp only [step_localLength, step_output, fin_foldl_eq_accVar]`, `norm_num [scalarBits]`, `simp only [… Nat.reduceAdd, Nat.reduceMul, reduceIte, reduceDIte, fin_foldl_goal_eq_accVar]` | `fold_invariant … 256 (le_refl 256)`, `induction k with \| zero \| succ k ih` |
| **completeness** | `circuit_proof_start [<same unfolds>]`, `obtain … := h_env`, `rw [evalEmu, BigInt.value, ← h_input.1]`, `refine ⟨?_, …⟩` on the tuple of subcircuit obligations, `congrArg (Nat.cast : ℕ → F p)` + `push_cast` + `rw [← sub_eq_zero]; rw [← hcast]; ring` | `Nat.div_add_mod'`, `Nat.mod_lt _ hn_pos`, `sub_witness_identity`, `clear_value` + `omega`, flat `exact ⟨…21 components…⟩` |
| **mainCost** | `rw [show <count> = <nested sum> from by decide]` (or `count_eq` + `congr 1 <;> … <;> ring`), `unfold <Gadget>.main`, `refine CostIs.bind (costIs_sub_X _) fun v => ?_` chain, `exact CostIs.pure _` | `CostIs.subcircuit (fun n => costIs_X b n)`, `CostIs.foldlRange`, `CostIs.forEach`, `CostIs.assertion`, `simpa [Count.add_zero] using …` |
| **isR1CS** | `attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS`, `unfold <Gadget>.main`, `refine IsR1CSCirc.bind_out (isR1CS_sub_X _ <affine args>) fun nX => ?_`, `IsR1CSCirc.forEach_mem`, `change Affine (varFromOffset … )[i]` | `isR1CSRow_of_affine`, `isR1CSRow_mul`, `isR1CSRow_mul_sub/mul_add_sub/sub_one_sub_mul`, `Affine.{const,var,add,sub,zero,mul_deg0,mul_fconst}`, `affine_finFoldl'`, `IsR1CSCirc.bind_out_inv`, `finFoldl_invariant` |
| **computableWitness** | `change Operations.forAllFlat …`, `apply …forAllFlat_of_structuralComputableWitnesses`, `unfold main`, the 8-lemma `simp only [*_structuralComputableWitnesses_iff, and_true]`, `and_intros` | `<Gadget>.computableWitnesses`, `*_flatStructuralComputableWitnesses_of_condition`, `eval_output_of_agreesBelow`, `ProverEnvironment.agreesBelow_of_le`, `simpa [circuit_norm] using congrArg (fun x : Inputs _ => x.f) h_input`, `omega` on offset arithmetic |

### Heartbeat / recursion management

- `set_option maxRecDepth 8192` at: `ScalarMul.lean:128, 159, 200, 243`; `ScalarMulTheorems.lean:401, 542, 622`; `Cost.lean:1464`.
- `set_option maxRecDepth 4000` at: `Cost.lean:1310, 1357`.
- `set_option maxHeartbeats` — **never used in the shipped path**; only `MulModL.lean:83` (`1000000`) in the dead lazy layer. Instead: aggressive **lemma extraction** ("isolated into its own declaration for a fresh heartbeat budget" appears verbatim at `MulModTheorems.lean:341-344, 466-472, 537-539, 700-704`, `MulMod.lean:74-77, 103-105`, `ScalarMulTheorems.lean:395-399, 402-404`).
- **Laziness idiom** (`MulMod.lean:473-478`): *"single explicit `exact` (lazy `.1/.2` projections; no eager `obtain` ⇒ no `whnf` blowup)"* —
  ```lean
  exact ⟨core.1, core.2.1, witnessedMul_completeness …, witnessedMul_completeness …, core.2.2⟩
  ```

---

## 15. Distilled playbook rules

1. **Represent a 256-bit emulated field as 4×64-bit little-endian limbs over BN254; make limbs byte-aligned so the byte boundary is a carry-free affine recomposition.** (`Params.lean:36-45`, `ToBytes.lean:18-21`)
2. **Bundle all field-size hypotheses into one `BigIntParams` structure with `by decide` fields; destructure it first thing in every gadget proof** (`obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P`).
3. **Never divide in-circuit.** Prove big-integer equality with witnessed *offset signed carries* range-checked to `W` bits (`carryOffset = (m+1)·2^{B+1}`, `W = 69`), one affine per-index row, and a forced-zero top carry.
4. **In every soundness proof, first replace all `Fin`/`env.get` indexing by total `ℕ → ℕ` shadow functions via `set … := fun k => if h : k < n then … else 0 with h…`.** Then all reasoning is `Finset.sum` + `omega`.
5. **The field→ℕ lift is always the same 4-step recipe:** build `<field expr> = ((<nat expr> : ℕ) : F p)` by `push_cast [<val casts>]; ring`; `rw [that, ZMod.val_natCast_of_lt <bound>]`; `congrArg ZMod.val <the constraint>`; conclude. Package it as a standalone `*_lift` lemma.
6. **Weighted-sum + `omega` is the closing move for every carry argument.** `set` each sum to an atom, supply the two ℕ identities (`carry_telescope`, `geom_shift`), and let `omega` do linear arithmetic over ≤6 atoms.
7. **`clear_value` before `omega` whenever truncated ℕ subtraction is in play.**
8. **Materialize every gadget output into fresh witness cells (`Mux`, `witnessedMul`, `<==`).** This single discipline makes `isR1CS` a mechanical `Affine.*` threading exercise and keeps `EqViaCarries` inputs affine.
9. **Handle the elliptic-curve exception cases by computing all branches unconditionally and muxing with `IsZeroFe` flags in the spec's own match order.** Case analysis then lives entirely in a plumbing-free `soundness_core` over decoded values.
10. **Prove chord/tangent closure with `linear_combination` and offline-computed cofactors; recover the spec's division from the circuit's multiplication with `rw [eq_div_iff hden]; linear_combination hlam'`.**
11. **Mirror the circuit fold with two ladders — `accVar` (variable level) and `specAcc` (value level) — and prove one `fold_step` + one `fold_invariant`.** Expect to need 2–3 syntactically distinct copies of the `foldlAcc = accVar` bridge because `simp`/`rw` cannot see through `Var M F` aliases in binder types.
12. **Manage elaboration cost by extraction, not by `maxHeartbeats`:** one declaration per arithmetic core, `attribute [local irreducible]` on children before structural peels, `bind_out_inv` to keep huge fold outputs opaque, lazy `.1/.2` projections instead of eager `obtain`.
13. **A "fixed base" variant may not save cost at all** — here it only shrinks the interface assumptions and replaces `packCoord` affine reindexing with `emuConst` literals plus a `by decide` on-curve check.
