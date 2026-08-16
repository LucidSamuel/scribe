# Clean / zkGolf Proof Playbook

Master reference for proving zkGolf obligations in the Clean DSL (Lean 4). Distilled from the
framework source and all nine reference solutions (~58k lines). Per-domain deep catalogs live in
`docs/playbook/`:

| file | covers |
|---|---|
| [`playbook/framework.md`](playbook/framework.md) | Clean circuit model, the five obligations, every `CostIs`/`IsR1CSCirc`/`ComputableWitnessLemmas` combinator, gotchas |
| [`playbook/assertbytes-sha256.md`](playbook/assertbytes-sha256.md) | AssertBytes + SHA256: 60+ named patterns (S1–S18, C1–C9, M1–M7, R1–R14, W1–W13), file layering |
| [`playbook/gf2-canonical.md`](playbook/gf2-canonical.md) | GF(2) + the canonical (`isR1CS_Cidentity`) obligation: SHA256CompressGF2(Canonical), Blake3 |
| [`playbook/keccak-k12.md`](playbook/keccak-k12.md) | KeccakF1600 (fold + induction) vs KangarooTwelveGF2 (unrolled, F2) |
| [`playbook/secp256k1.md`](playbook/secp256k1.md) | Non-native field arithmetic (4×64-bit limbs), EqViaCarries, complete EC addition, 256-step fold |
| [`playbook/rsa4096.md`](playbook/rsa4096.md) | 34×121-bit bignum, witnessed ModExp, PKCS#1 padding, heavy-subcircuit opacity tricks |

Vendored sources: challenge repo at `corpus/zk-golf-challenges` (buildable checkout with warm
`.lake` at `~/experiments/zk-challenges/zk-golf-challenges`), Clean at `corpus/clean` pinned to
`041c6e7e` (toolchain `leanprover/lean4:v4.28.0`). Harvested record submissions + technique
write-ups: `corpus/submissions/` (`INDEX.md` there summarizes every record's own description).

---

## 1. The contract

A solution to challenge `X` must provide, in namespace `Solution.X` (names pinned by
`configs/X.json`):

```lean
def main : Var Input (F p) → Circuit (F p) (Var Output (F p))
instance elaborated : ElaboratedCircuit (F p) Input Output main   -- usually `by elaborate_circuit`
theorem soundness    : GeneralFormalCircuit.Soundness (F p) main Assumptions Spec
theorem completeness : GeneralFormalCircuit.Completeness (F p) main ProverAssumptions ProverSpec
theorem mainCost     : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩
theorem isR1CS       : Challenge.CostR1CS.isR1CS main             -- OR isR1CS_Cidentity (GF2Canonical)
theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env => eval env input) →
  Circuit.ComputableWitnesses (main input) n
```

Rules enforced by the checker:
- **Axioms**: only `propext`, `Quot.sound`, `Classical.choice`, plus the challenge's own
  `hCircomPrime`-style axiom (GF(2) challenges have none — `Fact (Nat.Prime 2)` is a theorem).
  `sorry`, `native_decide` (`Lean.ofReduceBool`), `Lean.trustCompiler` all fail.
- **Cost claim**: the checker overwrites `Challenge/Instances/X/Cost.lean`'s placeholder with your
  claimed `allocations`/`constraints`; your solution re-declares the same fully-qualified names
  as `@[reducible] def`. The solution must import `Challenge.Instances.X.Interface` and
  `Challenge.Utils.*` but NEVER `…X.Challenge` or `…X.Cost` (name clash by design).
- **1200 s wall-clock** verification timeout; toolchain/deps must match the pinned lake manifest.
- Score = allocations + constraints. `lookup`/`interact` operations are *rejected* by the R1CS
  certificate — no lookup tables, no channels; range checks must be bit decompositions.

## 2. What costs and what's free

- `witnessVector m _` / `ProvableType.witness` = m allocations. `assertZero e` = 1 constraint.
  Nothing else costs. Subcircuit nesting adds **zero** overhead (counted flat).
- **Free (0 constraints)**: any affine wiring — rotations/shifts as `Vector.ofFn` re-indexing,
  XOR over GF(2) (`+`), NOT (`1 - x`), constants, ι-style constant-XOR, limb→byte re-grouping,
  index permutations, `Vector` append/window/select of expressions.
- R1CS row check is **syntactic**: `r1csProducts` counts degree-2 products along the top-level
  add spine. `a*b + a*c` is REJECTED (factor by hand); degree ≥3 rejected; `C - A*B` and `C + A*B`
  fine; pure affine rows fine (except canonical challenges — see §7).
- `x === y` is a hidden `FormalAssertion` subcircuit; write `assertZero (x - y)` for a bare row.
- Known records exploit: dropping recomposition rows by folding them into product rows
  (assert-bytes 240 = drop-the-top-bit: witness only 7 low bits, one row
  `(x-s)*(x-s-128)=0` subsumes top-bit booleanity + recomposition), sharing decompositions,
  merging rows via affine combination. Read `corpus/submissions/INDEX.md` before golfing.

## 3. Solution anatomy (conventions the references all follow)

- **Gadget file = six declarations**: `main`, `elaborated`, `Assumptions`/`Spec`, `soundness`,
  `completeness`, `def circuit : FormalCircuit/FormalAssertion … where …`, plus
  `computableWitnesses`. ALL supporting math exiled to `XTheorems.lean`.
- **Cost.lean is separate** and bottom-up: per gadget exactly `costIs_main`, `costIs_sub`
  (`:= CostIs.subcircuit (fun n => costIs_main b n)`), `r1cs_*`/`isCidentity_*`, `*_sub`
  wrappers, `affineW_subOut_*`. Parents only ever use the `_sub_` wrapped forms.
- **Structure-field workaround**: if `soundness := soundness` times out on defeq checking, use
  `soundness := by simp only [soundness]`.
- Proofs needing `maxHeartbeats 4000000` live alone in their own file.
- `autoImplicit false` — bind every variable explicitly.

## 4. Per-obligation quick reference

### soundness
Opener: `circuit_proof_start [main, Spec, <each child .circuit/.Spec/.Assumptions>]`.
Introduces (fixed names) `i₀ env input_var input h_input h_assumptions h_holds`; goal = Spec ∧
`Operations.Requirements` (the latter closes via `circuit_norm` or explicit `Or.inl rfl` per
subcircuit — for circuits with heavy children, do NOT put the child in the bracket list; simplify
only `at h_holds` and discharge requirements with `refine ⟨?_, Or.inl rfl, …⟩`).
Core moves:
- `h_holds` is a conjunction: `obtain ⟨c1, …, ck⟩ := h_holds` in source order after
  `simp only [Child.Assumptions, Child.Spec, and_imp] at h_holds`; then chain
  `obtain ⟨v1, n1⟩ := c1 h…` feeding each child's **Normalized/Valid output** into the next
  child's assumptions; close with `rw [vk, …, v1]`.
- Input bridge: `rw [← h_input, Vector.getElem_map]` (or `Vector.ext_iff.mp h_input i i.isLt`).
- Constraint → equation: `add_neg_eq_zero.mp` / `sub_eq_zero.mp (by ring_nf; ring_nf at h; exact h)`
  / `linear_combination h` (GF(2), and `linear_combination hc + hp` when a row is split in two).
- Field→ℕ lift recipe: build `⟨field expr⟩ = ((⟨nat expr⟩ : ℕ) : F p)` by `push_cast; ring`,
  `rw [that, ZMod.val_natCast_of_lt bound]`, `congrArg ZMod.val h`, then `omega`.
  `linarith` does NOT work on `ZMod p`; use `linear_combination`.
- Bitwise word lemmas: `apply Nat.eq_of_testBit_eq; intro j; by_cases hj : j < N` with
  `testBit_binary_sum`-style weighted-sum extraction; out-of-range branch via bound lemmas.
- Loops (`foldlRange`): prove an invariant `have key : ∀ k, k ≤ N → ⟨value = specAcc k ∧
  Normalized⟩` by `induction k` (introduce the bound *inside* branches), using the solution's own
  `foldlAcc_eq_<accVar>` bridge lemma and `h_holds ⟨k, hk⟩`. Cost of the same loop needs NO
  induction (`CostIs.foldlRange`); R1CS needs an affineness invariant (`foldlRange_inv`).

### completeness
Opener: same `circuit_proof_start`; context has `h_env` (witness-generator equations /
child implications) instead of `h_holds`, and for `FormalAssertion` an extra `h_spec`.
- Leaf: `intro i; have := h_env i; simp only [Vector.getElem_ofFn] at this; rw [this]; ring`
  (plus a `ZMod.natCast_val`+`ZMod.cast_id` cast round-trip when the generator computes in ℕ).
- Composite: `simp only [Child.Assumptions, Child.Spec, and_imp] at h_env ⊢`, keep only the
  Normalized halves (`obtain ⟨_, n1⟩ := c1 …`), then one flat `exact ⟨…⟩` supplying each child's
  assumptions. Where all `Assumptions := True` (GF(2)): `simp only [C.circuit, C.Assumptions, and_self]`.
- Invoking a `FormalAssertion` child obliges you to PROVE its Spec about honest values —
  that's why `ProverAssumptions` carries what `Assumptions` doesn't.
- `clear_value` on `set` atoms before `omega` when truncated ℕ subtraction appears.

### mainCost
Term-mode, no tactics: `fun input => (CostIs.bind … fun _ => … CostIs.pure _ :
CostIs (main input) ⟨allocations, constraints⟩)` — the ascription forces definitional numeral
reduction (both cost names are `@[reducible]`). When `Count` sums don't reduce, pre-normalize:
`rw [show K = K₁ + (K₂ + …) from by show (⟨_,_⟩ : Count) = _; congr 1]` (or `… <;> ring`).
Leaves: `CostIs.witnessVector`=⟨m,0⟩, `CostIs.assertZero`=⟨0,1⟩, `CostIs.forEach`=m•K,
`CostIs.foldlRange (constant := namedInstance)`, `CostIs.subcircuit/assertion (fun n => costIs_child _ n)`.
Name a `Circuit.ConstantLength` instance for fold bodies (`infer_constant_length` times out on
nested gadget trees) and pass the SAME instance in `main`, cost, and R1CS proofs.

### isR1CS
**Mandatory first line**: `attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS
flatOperationsIsR1CS` — otherwise unification evaluates `r1csProducts` on real expressions and hangs.
Shape: `isR1CS_of_IsR1CSCirc (fun input hinput => …) (fun input hinput => …)` — rows + output
affineness (`affineOutput_unit` when Output = unit).
- Thread affineness down the do-block with `IsR1CSCirc.bind_out … fun n => ?_` (NOT `.bind`, whose
  continuation can't see the output); child outputs are `varFromOffset` ⇒
  `affineW_witnessVector_output` / `rw [show (subcircuit C b).output n = varFromOffset … from rfl]`.
- Row table: affine → `isR1CSRow_of_affine`; `A*B` → `isR1CSRow_mul`; `C - A*B` →
  `isR1CSRow_sub_mul`; `C + A*B` → `isR1CSRow_add_mul`; anything else: hand-build via
  `isR1CSRow_of_r1csProducts` with an `rcases r1csProducts_mul_affine hA hB` split.
- `IsR1CSCirc.forEach` is too weak (quantifies over all values); copy the solutions'
  `IsR1CSCirc.forEach_mem` (index-aware, 4 lines, in every reference Cost.lean).
- Input affineness: `simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using
  hinput i (by omega)` then peel struct fields with `AffineW.left_of_append`/`right_of_append`.
- Rank-2+ sums (convolutions): witness every product into a fresh cell with one
  `a[i]*b[j] - pp[t] = 0` row and pass the *linear* form downstream ("witnessed-product-matrix").

### computableWitness
Two layers. Per gadget (`circuit.ComputableWitnesses`):
```lean
intro offset input env env'
change Operations.forAllFlat offset (…FormalCircuitBase.computableWitnessCondition input env env') ((main input).operations offset)
apply …FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
unfold main
simp only [<the *_structuralComputableWitnesses_iff lemma for every combinator main uses>, and_true, implies_true]
and_intros
```
then per goal: witness generators — show they depend on the input only through `eval` (Vector.ext +
`eval_getElem_congr h_input`); asserts — `intro _; trivial`; first subcircuit —
`FormalCircuit.subcircuit_flatStructuralComputableWitnesses` (input a pure function of parent
input); later subcircuits — `…_of_condition` (you additionally get `hle : n ≤ k` and
`h_agree : env.AgreesBelow k env'`; close witnessed-var inputs with
`eval_mem_varFromOffset_fields_of_agreesBelow h_agree (by omega)` and per-gadget
`eval_subOut_of_agreesBelow` lemmas — define one for every value-producing gadget).
Put `attribute [local irreducible] main <heavy children>` before the proof; use
circuit-abstract `rfl` lemmas (`subcircuit_output_eq`, `subcircuit_localLength_eq`) so heavy
children are never whnf'd.
Top level: build `hstruct`, then append the **verbatim ~35-line `himplies` induction block**
(identical in every reference `Main.lean` — `Condition.implies`/`ignoreSubcircuit`,
`induction ops generalizing off`, witness case uses `hinput … (agreesBelow_of_le …)`). For a
gadget whose input types line up, skip all of it:
`FormalCircuitBase.computableWitnesses_implies (circuit := c.base) computableWitnesses`.

### elaborated
`by elaborate_circuit` for everything small. Loop circuits: `elaborate_circuit_with
{ output _ i₀ := <closed form> } using by simp only [circuit_norm]; …`. When even that hits
kernel deep recursion (RSA-scale), hand-write the `ElaboratedCircuit` with a symbolic
`localLength`, `output_eq := Subsingleton.elim _ _` (unit output), and `rfl`-`have`s for child
projections.

## 5. Elaboration-cost survival rules (the difference between green and timeout)

1. `attribute [local irreducible]` on trusted R1CS predicates (always), on `main` + heavy child
   circuits before `computableWitness`, on heavy pure defs (padding folds) before composite proofs.
   Canonical predicates are the OPPOSITE: `attribute [local semireducible] isCidentityRowAt
   flatOperationsIsCid operationsIsCid` inside leaf certificate sections only.
2. One declaration per arithmetic core / per subcircuit wrapper — each gets its own heartbeat
   budget. Never raise `maxHeartbeats` when extraction works; `set_option maxRecDepth 4000–8192`
   is routine for deep folds/interval_cases.
3. Never let `circuit_norm` rewrite a goal containing a deeply-recursive subcircuit — simplify
   `at h_holds`/`at h_env` only, and expose child projections via `have h : C.Assumptions = … := rfl`.
4. `exact ⟨core.1, core.2.1, …⟩` (lazy projections) instead of eager `obtain` on huge terms.
5. Accumulator-type spelling matters: bridge lemmas must use `M (Expression F)` (not the
   `Var M F` alias) to match `h_holds` syntactically; expect to duplicate a lemma per spelling.
6. Keep big numerals symbolic: fold exponents behind names (`publicExponent`), `set bits := …`,
   state `i2osp`-style lemmas at symbolic length. `by decide` IS fine on closed ℕ facts (even
   512-bit modular arithmetic — kernel Nat is fast); `native_decide` never.
7. Spec functions written as `Vector.ofFn` make per-index restatements `rfl`; keep a
   `*Spec_loop := rfl` lemma per loop so `simp only` can put goals in per-index form.
8. `set x := <fun> with hx` blocks beta reduction — immediately add `have hx_app : ∀ k, x k = … := fun _ => rfl`.

## 6. Domain cheat-sheet

- **Prime-field bit circuits (SHA256, AssertBytes)**: `valueBits`/`Normalized` invariant threaded
  through every Spec; booleanity `b*(b-1)`; recomposition affine row; `Utils.Bits`
  (`fieldToBits/fieldFromBits/fieldFromBitsExpr` + inversion lemmas) is the entire math.
- **GF(2)** (`F 2 = ZMod 2`): `+`=XOR (free), `*`=AND (1 row), `a² = a`; no range assumptions at
  all; single-product full-adder carry `cᵢ₊₁ = (xᵢ+cᵢ)(yᵢ+cᵢ)+cᵢ` (1 row/bit; canonical: 2);
  bit facts by `by decide` over all of F 2 (2–8 cases); `ring` closes completeness;
  `linear_combination` extracts constraints. See `playbook/gf2-canonical.md` §4–5.
- **Non-native arithmetic (secp256k1, RSA)**: little-endian limbs (4×64 / 34×121); modulus as
  constant limbs; witness quotient+remainder, certify `a·b = q·n + r` with **EqViaCarries**
  (offset signed carries, range-checked to W bits, one affine row per index, zero top carry) and
  `r < n` with a borrow-chain LessThan; `remainder_eq` closes. Complete EC addition = compute all
  branches unconditionally + mux by `IsZeroFe` flags in the spec's match order;
  chord/tangent closure by `linear_combination` with offline cofactors;
  division recovered via `eq_div_iff … ; linear_combination`.
- **Iterated permutations (Keccak)**: rounds as `foldlRange` with symbolic `stateVar`/`vfold`
  ladders (soundness=induction, cost=foldlRange, R1CS=foldlRange_inv); ρ/π/ι/¬ free wiring;
  only XOR/AND rows. Fully unrolling 12 rounds (K12) trades induction for a 12-step `rw` chain.

## 7. Canonical challenges (`*GF2Canonical`) — extra deltas

`isR1CS_Cidentity` replaces `isR1CS`: row `t` must be literally `var ⟨n₀+t⟩ - A*B` (ordered pins,
no linear rows — copy rows need `* 1`). Composition demands **Balanced** (constraints =
localLength per subterm, from `Balanced.of_costIs`), so `IsCidCirc.bind hf hbal hg` /
`bind_out` / solution-side `foldlRange_inv (L := …)` carry cost side conditions. Cost ≈2× on
adders (row split), 1× on Ch/Maj (inline the output XOR as `zxorOut` instead of witnessing).
Every composite should END in a pin so its output is a bare `varFromOffset` (`output_*_eq := rfl`
ladder — Blake3's scaling trick).

## 8. Copy-paste artifacts (verbatim, from references)

- The top-level `computableWitness` `himplies` induction block (§4) — identical in all 9 solutions.
- `IsR1CSCirc.forEach_mem` — in every Cost.lean.
- The `hcount`/`show (⟨_,_⟩ : Count) = _; congr 1` Count-reassociation.
- `circuit_proof_start` hypothesis names (`i₀ env input_var input h_input h_assumptions
  h_holds/h_env/h_spec`) are hard-coded; unfold lists are matched by literal name and silently
  no-op on misses — ugly goals usually mean a name didn't resolve.
- `structure field := by simp only [thm]` whnf-timeout workaround.
