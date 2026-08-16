# Clean DSL + zkGolf — Framework Fundamentals Catalog

Paths are absolute. `CLEAN = /Users/lucidsamuel/experiments/scribe/corpus/clean`, `GOLF = /Users/lucidsamuel/experiments/scribe/corpus/zk-golf-challenges`. Pinned Clean rev (from `GOLF/lake-manifest.json`): `041c6e7ebc06f5cbfd534c2a19c4120f3de62435`; toolchain `leanprover/lean4:v4.28.0`, mathlib `v4.28.0`.

## Circuit model

### The monad
`CLEAN/Clean/Circuit/Basic.lean:28`

```lean
def Circuit (F : Type) [Field F] (α : Type) := ℕ → α × List (Operation F)
```

A circuit is a function from a **starting offset** (the index of the next free witness cell) to `(output value, list of operations)`. The `Monad` instance (`Basic.lean:33-43`) is a writer(ops)+state(offset) mix:

```lean
def bind (f : Circuit F α) (g : α → Circuit F β) : Circuit F β := fun n =>
  let (b, ops') := g (f n).1 (n + Operations.localLength (f n).2)
  (b, (f n).2 ++ ops')
```

Three projections (all `@[reducible, circuit_norm]`, `Basic.lean:76-86`):
- `Circuit.operations (circuit) (offset) : Operations F`
- `Circuit.output (circuit) (offset) : α`
- `Circuit.localLength (circuit) (offset := 0) : ℕ`

Rewrite lemmas used constantly (`Basic.lean:380-407`):
`Circuit.pure_operations_eq`, `Circuit.bind_operations_eq`, `Circuit.map_operations_eq`, `Circuit.pure_localLength_eq`, `Circuit.bind_localLength_eq`, `Circuit.map_localLength_eq`, `Circuit.pure_output_eq`, `Circuit.bind_output_eq`, `Circuit.map_output_eq`, `Circuit.bind_forAll`. Also `@[circuit_norm] Circuit.bind_def`, `Circuit.pure_def`, `Circuit.map_def`, `Circuit.seqRight_def`, `Circuit.bind_normalize`.

### Operations = "allocations" and "constraints"
`CLEAN/Clean/Circuit/Operations.lean:16, 313`

```lean
inductive FlatOperation (F : Type) where
  | witness  : (m : ℕ) → (ProverEnvironment F → Vector F m) → FlatOperation F
  | assert   : Expression F → FlatOperation F
  | lookup   : Lookup F → FlatOperation F
  | interact : AbstractInteraction F → FlatOperation F

inductive Operation (F : Type) [Field F] where
  | witness | assert | lookup | interact
  | subcircuit : {n : ℕ} → Subcircuit F n → Operation F

abbrev Operations (F : Type) [Field F] := List (Operation F)      -- Operations.lean:353
```

- **allocations** = total `m` over all `.witness m _` (i.e. `Operations.localLength`, `Operations.lean:379`; subcircuits contribute `s.localLength`).
- **constraints** = number of `.assert` nodes (one R1CS row each, by the zkGolf cost model).
- `lookup` / `interact` cost `Count.zero` in `flatOperationCount` but are **outright rejected** by the R1CS certificate (`flatOperationsIsR1CS (.lookup _ :: _) => False`).

Flattening / nesting: `NestedOperations` (`Operations.lean:22`), `NestedOperations.toFlat`, `Operations.toFlat` (`:359`), `Operations.toNested` (`:367`), `Operations.toNested_toFlat` (`Subcircuit.lean:69`, `@[circuit_norm]`).

### Emission primitives
`CLEAN/Clean/Circuit/Basic.lean:92-126`, exported at `:250`

| op | signature | cost |
|---|---|---|
| `Circuit.witnessVar (compute : ProverEnvironment F → F) : Circuit F (Variable F)` | 1 cell | `⟨1,0⟩` |
| `Circuit.witnessField (compute) : Circuit F (Expression F)` | 1 cell | `⟨1,0⟩` |
| `Circuit.witnessVars (m) (compute : ProverEnvironment F → Vector F m)` | m cells → `Vector (Variable F) m` | `⟨m,0⟩` |
| `Circuit.witnessVector (m) (compute)` | m cells → `varFromOffset (fields m) offset` | `⟨m,0⟩` |
| `Circuit.assertZero (e : Expression F) : Circuit F Unit` | 1 row | `⟨0,1⟩` |
| `Circuit.lookup (table) (entry)` | lookup | rejected by `isR1CS` |
| `Channel.emit / .pull / .push` | interact | rejected by `isR1CS` |
| `ProvableType.witness (compute : ProverEnvironment F → α F)` | `size α` cells | `⟨size α, 0⟩` |
| `ProvableVector.witness m compute` | via `ProvableType.witness` | |

Generic `witness` comes from `class Witnessable` (`Basic.lean:254-273`) with instances for `field`, `fields m`, any `ProvableType α`, and `ProvableVector α m`.

Sugar (`CLEAN/Clean/Gadgets/Equality.lean:129-180`): `x === y` (`HasAssertEq.assert_eq`, desugars to `Gadgets.Equality.circuit` — a **`FormalAssertion` subcircuit**, not a bare `assertZero`), `let x <== e` (`HasAssignEq.assignEq` = witness + `===`). Also `copyToVar`, `toVar`, `getOffset`, `witnessAny` in `CLEAN/Clean/Circuit/Extensions.lean`.

### TypeMap / Var / ProvableType
`CLEAN/Clean/Circuit/CircuitType.lean:9,59`; `CLEAN/Clean/Circuit/Provable.lean:12`

```lean
abbrev TypeMap := Type → Type

class ProvableType (M : TypeMap) where
  size : ℕ
  toElements   {F} : M F → Vector F size
  fromElements {F} : Vector F size → M F
  toElements_fromElements, fromElements_toElements
```

`class CircuitType M` supplies `Var M`, `Value M`, `ProverValue M`, `evalVerifier`, `evalProver`. Every `ProvableType` induces one via `ProvableType.toCircuitType` with `Var M F = M (Expression F)` and `Value = ProverValue = M`. Key lemmas `@[circuit_norm] CircuitType.var_of_provableType / value_of_provableType / proverValue_of_provableType`, `CircuitType.eval_verifier`, `CircuitType.eval_prover`.

Concrete types (`Provable.lean:184-256`): `unit` (`size = 0`, `unit F = Unit`), `field := id`, `fieldPair`, `fieldTriple`, `fields n := fun F => Vector F n`, `ProvableVector α n`, `ProvablePair α β`. `NonEmptyProvableType` for `field`, `fields (n+1)`.

`varFromOffset (M) (offset) : M (Expression F)` (`Provable.lean:93`) = `fromElements (Vector.mapRange (size M) fun i => var ⟨offset + i⟩)`. This is what witness allocations return; hence witnessed values are always bare `Expression.var`, hence affine.

`ProvableStruct` (`Provable.lean:307`) + `deriving ProvableStruct` (handler in `CLEAN/Clean/Utils/Tactics/ProvableStructDeriving.lean`) gives a `ProvableType` for record types (`ProvableType.fromStruct`, `:374`).

`eval` is the irreducible normal form (`CircuitType.lean:26`: `attribute [irreducible] Eval.eval`); `ProvableType.eval` is tagged `@[explicit_provable_type]`, not `circuit_norm`.

### Environments and ProverData / ProverHint
`CLEAN/Clean/Circuit/Expression.lean:21-59`

```lean
def ProverData (F : Type) := String → (n : ℕ) → Array (Vector F n)
def ProverHint (F : Type) := String → (n : ℕ) → Array (Vector F n)

structure Environment (F) where get : ℕ → F ; data : ProverData F
structure ProverEnvironment (F) extends Environment F where hint : ProverHint F
```

- **Soundness** quantifies over `Environment F` (adversarial witness assignment); `env.data` is visible to `Assumptions`/`Spec`.
- **Completeness** quantifies over `ProverEnvironment F`; `env.hint` is visible to `ProverAssumptions`/`ProverSpec` and is *not committed*.

Witness-generation machinery (`Basic.lean:278-334`): `ProverEnvironment.fromList`, `FlatOperation.dynamicWitness`, `FlatOperation.dynamicWitnesses`, `FlatOperation.proverEnvironment`, `Circuit.proverEnvironment`, `FlatOperation.witnessGenerators`, `Operations.witnessGenerators`.

```lean
def ProverEnvironment.AgreesBelow (n) (env env') := ∀ i < n, env.get i = env'.get i
def ProverEnvironment.OnlyAccessedBelow (n) (f : ProverEnvironment F → α) :=
  ∀ env env', env.AgreesBelow n env' → f env = f env'
def Operations.ComputableWitnesses (ops) (n) (env env') : Prop :=
  ops.forAllFlat n { witness n _ compute := env.AgreesBelow n env' → compute env = compute env' }
def Circuit.ComputableWitnesses (circuit) (n) := ∀ env env', (circuit.operations n).ComputableWitnesses n env env'
```

### Loop combinators
`CLEAN/Clean/Circuit/Loops.lean:477-512`

```lean
def Circuit.forEach {m} [Inhabited α] (xs : Vector α m) (body : α → Circuit F Unit)
    (_constant : ConstantLength body := by infer_constant_length) : Circuit F Unit
def Circuit.map     (xs : Vector α m) (body : α → Circuit F β) (_constant) : Circuit F (Vector β m)
def Circuit.mapFinRange (m) [NeZero m] (body : Fin m → Circuit F β) (_constant) : Circuit F (Vector β m)
def Circuit.foldl   (xs) (init) (body : β → α → Circuit F β) (_const_out) (_constant) : Circuit F β
def Circuit.foldlRange (m) [Inhabited β] (init) (body : β → Fin m → Circuit F β) (_constant) : Circuit F β
```

`class Circuit.ConstantLength (circuit : α → Circuit F β)` (`Basic.lean:345`) with `ConstantLength.fromConstantLength` and tactic `infer_constant_length` (`Basic.lean:360`). Loop lemmas: `Circuit.forEach.localLength_eq`, `.output_eq`, `.operations_eq`, `.forAll` (`@[circuit_norm ↓]`), `.forAllNoOffset`, `.usesLocalWitnesses`; analogous `map.*`, `mapFinRange.*`, `foldlRange.*`, and the underlying `Circuit.ForM.*`, `Circuit.MapM.*`, `Circuit.FoldlM.*` (incl. `Circuit.FoldlM.foldlAcc`, `Loops.lean:274`).

Note: `forEach.operations_eq` is **not** in `circuit_norm` — you `rw [Circuit.forEach.operations_eq]` explicitly in cost/R1CS proofs; `forEach.forAll` **is** in `circuit_norm ↓`.

### Formal circuit structures
`CLEAN/Clean/Circuit/Formal.lean`

```lean
structure FormalCircuitBase (F) (Input Output : TypeMap) [Field F] [CircuitType Input] [CircuitType Output] where
  name : String := "anonymous"
  main : Var Input F → Circuit F (Var Output F)
  elaborated : ElaboratedCircuit F Input Output main := by first | infer_instance | elaborate_circuit
  exposedChannels ; exposedChannels_eq
```
Projections: `.output`, `.localLength`, `.channelsWithGuarantees`, `.channelsWithRequirements`, `.localLength_eq`, `.channelsLawful`, `.subcircuitsConsistent`.

`ElaboratedCircuit` (`CLEAN/Clean/Circuit/Basic.lean:210`) is a **class** with fields `localLength`, `localLength_eq`, `output`, `output_eq`, `subcircuitsConsistent`, `channelsWithGuarantees`, `channelsWithRequirements`, `channelsLawful`.

Structures and their obligations:

| structure | Assumptions | Spec | soundness | completeness |
|---|---|---|---|---|
| `FormalCircuit F In Out` (`:129`) | `In F → Prop` | `In F → Out F → Prop` | `Soundness F main Assumptions Spec` | `Completeness F main Assumptions` |
| `FormalAssertion F In` (`:188`, extends base into `unit`) | `In F → Prop` | `In F → Prop` | `FormalAssertion.Soundness` | `FormalAssertion.Completeness` (**assumptions ∧ spec → constraints**) |
| `GeneralFormalCircuit F In Out` (`:244`) | `In F → ProverData F → Prop` | `In F → Out F → ProverData F → Prop` | `GeneralFormalCircuit.Soundness` | `GeneralFormalCircuit.Completeness` with separate `ProverAssumptions : In F → ProverData F → ProverHint F → Prop` and `ProverSpec : In F → Out F → ProverHint F → Prop` |
| `GeneralFormalCircuit.WithHint` (`:300`) | over `Value Input`/`ProverValue Input` | | `.WithHint.Soundness` | `.WithHint.Completeness` |
| `DeterministicFormalCircuit` (`:142`) | + `uniqueness` | | | |

Bridges: `GeneralFormalCircuit.toWithHint`, `FormalCircuit.isGeneralFormalCircuit`, `FormalAssertion.isGeneralFormalCircuit` (`Theorems.lean:558,577`), `FormalCircuit.original_soundness/original_completeness`, `FormalAssertion.original_*`, `GeneralFormalCircuit.original_full_soundness/…completeness` (`CLEAN/Clean/Circuit/Foundations.lean`).

Subcircuit invocation (`CLEAN/Clean/Circuit/Subcircuit.lean:353-401`), all `@[circuit_norm]`:
```lean
def subcircuit               (circuit : FormalCircuit F β α)  (b) : Circuit F (Var α F)
def assertion                (circuit : FormalAssertion F β)  (b) : Circuit F Unit
def subcircuitWithAssertion  (circuit : GeneralFormalCircuit F β α) (b) : Circuit F (Var α F)
def subcircuitWithHintAssertion (circuit : GeneralFormalCircuit.WithHint F β α) (b)
```
Each emits **exactly one** `Operation.subcircuit`. `CoeFun` instances let you write `MyGadget.circuit x` in a `do` block — that is `subcircuit`/`assertion` under the hood.

`structure Subcircuit (F) [Field F] (offset : ℕ)` (`Operations.lean:261`) carries `ops : NestedOperations F`, `Assumptions`, `Spec`, `ProverAssumptions`, `ProverSpec`, `localLength`, `soundness`, `completeness`, `localLength_eq`, `channelsWith{Guarantees,Requirements}`.

---

## The five obligations

The contract file is `GOLF/Challenge/Instances/AssertBytes/Challenge.lean`; the reference solution is `GOLF/Solution/AssertBytes/{Main,Num2Bits,Cost}.lean`. The checker config `GOLF/configs/AssertBytes.json` names exactly:

```json
"theorem_names": ["Solution.AssertBytes.soundness","Solution.AssertBytes.completeness",
                  "Solution.AssertBytes.mainCost","Solution.AssertBytes.isR1CS",
                  "Solution.AssertBytes.computableWitness"],
"definition_names": ["Solution.AssertBytes.main","Solution.AssertBytes.elaborated"],
"permitted_axioms": ["propext","Quot.sound","Classical.choice",
                     "Challenge.Instances.AssertBytes.Interface.hCircomPrime"]
```

Interface (`GOLF/Challenge/Instances/AssertBytes/Interface.lean`):
```lean
@[reducible] def bufferLen : ℕ := 16
structure Input (F : Type) where buffer : Vector F bufferLen
deriving ProvableStruct
@[reducible] def Output : TypeMap := unit
def circomPrime : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
axiom hCircomPrime : circomPrime.Prime
instance : Fact circomPrime.Prime := ⟨hCircomPrime⟩
def Assumptions (_input : Input (F circomPrime)) (_data : ProverData (F circomPrime)) : Prop := True
def Spec (input) (_output) (_data) : Prop := ∀ i : Fin bufferLen, (input.buffer[i.val]'i.isLt).val < 256
def ProverAssumptions (input) (_data) (_hint) : Prop := ∀ i : Fin bufferLen, (input.buffer[i.val]'i.isLt).val < 256
def ProverSpec (_input) (_output) (_hint) : Prop := True
```

Preamble every solution needs:
```lean
def main (input : Var Input (F circomPrime)) : Circuit (F circomPrime) (Var Output (F circomPrime)) := …
instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := by elaborate_circuit
```

### 1. soundness

**Statement** (`Challenge.lean:26`):
```lean
theorem soundness : GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec
```
Unfolded (`CLEAN/Clean/Circuit/Formal.lean:196`):
```lean
∀ offset : ℕ, ∀ env : Environment F,
∀ input_var : Var Input F, ∀ input : Input F, eval env input_var = input →
Assumptions input env.data →
ConstraintsHold.Soundness env (main input_var |>.operations offset) →
let output := eval env (ElaboratedCircuit.output main input_var offset)
Spec input output env.data ∧ Operations.Requirements env (main input_var |>.operations offset)
```

**After `circuit_proof_start [main, Spec, …]`** you get, in order, `i₀ env input_var input h_input h_assumptions h_holds`, with `main`/`Assumptions`/`Spec` dsimp'd and `h_input`, `h_assumptions`, `h_holds` and the goal `simp only [circuit_norm, h_input, extras]`-normalized. `h_holds` becomes the per-constraint / per-subcircuit conjunction (`ConstraintsHold.Soundness` = `forAllNoOffset { assert e := env e = 0; lookup l := l.Soundness env; interact i := i.Guarantees env; subcircuit s := s.Assumptions env → s.Spec env }`, `Operations.lean:691`). The trailing `Operations.Requirements` conjunct is normally closed by `circuit_norm` (for subcircuits with `channelsWithRequirements = []` it reduces to `[] = [] ∨ _`).

**Reference proof** (`GOLF/Solution/AssertBytes/Main.lean:30`):
```lean
circuit_proof_start [main, Spec, Num2Bits.circuit, Num2Bits.Spec, Num2Bits.Assumptions]
intro i
rw [← h_input, Vector.getElem_map]
exact h_holds i
```
Note `h_holds i` — `forEach.forAll` (`@[circuit_norm ↓]`) already turned the loop into `∀ i : Fin m, …`.

Discharging lemmas: `circuit_norm` simp set; `Circuit.can_replace_soundness` (`Theorems.lean:65`), `Circuit.requirements_toFlat_of_soundness` (`:94`), `Circuit.constraintsHold_toFlat_iff` (`Subcircuit.lean:78`), `constraintsHold_soundness_iff_forall_mem`, subcircuit simp lemmas `FormalCircuit.toSubcircuit_assumptions/_soundness`, `GeneralFormalCircuit.toSubcircuit_assumptions/_soundness`, `FormalAssertion.toSubcircuit_assumptions/_soundness`.

### 2. completeness

**Statement** (`Challenge.lean:27`):
```lean
theorem completeness : GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec
```
Unfolded (`Formal.lean:213`):
```lean
∀ offset : ℕ, ∀ env : ProverEnvironment F, ∀ input_var : Var Input F,
env.UsesLocalWitnessesCompleteness offset (main input_var |>.operations offset) →
∀ input : Input F, eval env input_var = input →
ProverAssumptions input env.data env.hint →
ConstraintsHold.Completeness env (main input_var |>.operations offset) ∧
ProverSpec input (eval env (ElaboratedCircuit.output main input_var offset)) env.hint
```

**After `circuit_proof_start`**: intros `i₀ env input_var h_env input h_input h_assumptions` (for `FormalAssertion.Completeness` there is an extra trailing `h_spec`). `h_env` is `ProverEnvironment.UsesLocalWitnessesCompleteness` normalized by `circuit_norm` into per-witness equations of the form `env.get (i₀ + i) = compute env …` (`Basic.lean:175`, `ProverEnvironment.ExtendsVector`). Goal is `ConstraintsHold.Completeness … ∧ ProverSpec …`.

**Reference proof** (`Main.lean:37`):
```lean
circuit_proof_start [main, ProverAssumptions, ProverSpec, Num2Bits.circuit, Num2Bits.Spec, Num2Bits.Assumptions]
intro i
have := h_assumptions i
rwa [← h_input, Vector.getElem_map] at this
```
(Only the `FormalAssertion` `ProverAssumptions = Assumptions ∧ Spec` obligation of the child gadget survives; `ProverSpec = True` is closed by `circuit_norm`.)

Discharging lemmas: `Circuit.can_replace_completeness` (`Theorems.lean:289`), `can_replace_completeness_guarantees`, `can_replace_completeness_and_guarantees`, `can_replace_usesLocalWitnessesCompleteness` (`:237`), `usesLocalWitnessesCompleteness_iff_forAll` (`:252`), `ConstraintsHold.bind_usesLocalWitnesses` (`:375`), `Circuit.forEach.usesLocalWitnesses`, `FormalAssertion.toSubcircuit_completeness` (`Subcircuit.lean:589`: `ProverAssumptions env_p = (Assumptions (eval env_p input) ∧ Spec (eval env_p input))`), `GeneralFormalCircuit.toSubcircuit_completeness`.

### 3. mainCost

**Statement** (`Challenge.lean:29`):
```lean
theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩
```
where `allocations`/`constraints` come from `GOLF/Challenge/Instances/AssertBytes/Cost.lean` (placeholder `42`/`42`, overwritten by the checker with the solver's claim) and the solution re-declares them (`Main.lean:113`): `@[reducible] def allocations : Nat := 128`, `@[reducible] def constraints : Nat := 144` (matching `instances.yml` baseline).

Definition (`GOLF/Challenge/Utils/CostR1CS.lean:301-309`):
```lean
def CostIs (c : Circuit F α) (K : Count) : Prop := ∀ n, operationCount (c.operations n) = K
def circuitCost {Input} [ProvableType Input] (main : Var Input F → Circuit F α) (K : Count) : Prop :=
  ∀ input : Var Input F, CostIs (main input) K
```

**Opening move**: there is no tactic — you `intro input` (or write `fun input => …`) and then build the `CostIs` term by structural recursion mirroring `main`'s `do` block. Because the goal is `∀ n, operationCount … = K`, you almost never `simp` it; you assemble it from combinators.

**Reference proof** (`Main.lean:121`):
```lean
theorem mainCost : circuitCost main ⟨allocations, constraints⟩ :=
  fun input =>
    show CostIs (main input) ⟨allocations, constraints⟩ from
      CostIs.forEach (fun a n => costIs_assertion_num2Bits 8 a n)
```
The `show … from` bridges `⟨16 * 8, 16 * 9⟩` (what `CostIs.forEach` produces) to `⟨128, 144⟩` — works because `allocations`/`constraints` are `@[reducible]` and `Nat` literals reduce.

Larger example (`GOLF/Solution/SHA256/Main.lean:653`): a chain of `CostIs.bind (…) fun _ => …` ending in `CostIs.pure _`, ascribed with `( … : CostIs (main input) ⟨allocations, constraints⟩)`. When the arithmetic doesn't reduce definitionally, prove a `Count` equation first and `rw [← hcount]` (see `GOLF/Solution/AssertBytes/Cost.lean:47`):
```lean
have hcount : (⟨n, 0⟩ + (⟨n * 0, n * 1⟩ + ⟨0, 1⟩) : Count) = ⟨n, n + 1⟩ := by
  show (⟨_, _⟩ : Count) = _; congr 1; simp
rw [← hcount]
```

### 4. isR1CS

**Statement** (`Challenge.lean:30`):
```lean
theorem isR1CS : Challenge.CostR1CS.isR1CS main
```
Definition (`CostR1CS.lean:738`):
```lean
def isR1CS {Input Output} [ProvableType Input] [ProvableType Output]
    (main : Var Input F → Circuit F (Var Output F)) : Prop :=
  ∀ input : Var Input F, AffineProvable input → IsR1CSCirc (main input) ∧ AffineOutput (main input)
```

**Opening move**: `apply isR1CS_of_IsR1CSCirc` (or supply the two functions directly), which splits into
```lean
(hops : ∀ input, AffineProvable input → IsR1CSCirc (main input))
(hout : ∀ input, AffineProvable input → AffineOutput (main input))
```
then `refine IsR1CSCirc.bind_out … fun n => ?_` down the `do` block, discharging each `assertZero` with an `isR1CSRow` lemma.

**Reference proof** (`Main.lean:127`):
```lean
theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
  (fun input hinput =>
    (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
      fun i n => isR1CS_assertion_num2Bits 8 _ (affineW_input_buffer input hinput i.val i.isLt) n))
  (fun _ _ => affineOutput_unit _)
```
with `affineW_input_buffer` proved by `intro i hi; simpa [AffineProvable] using hinput i hi` (`Main.lean:116`).

**Mandatory hygiene** (`Main.lean:111`, `GOLF/Solution/AssertBytes/Cost.lean:63`, `GOLF/Solution/SHA256/Main.lean:640`):
```lean
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS
```
Otherwise the unifier tries to evaluate `r1csProducts` on the actual (huge) asserted expressions and loops.

### 5. computableWitness

**Statement** (`Challenge.lean:32`):
```lean
theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circomPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n
```

**Opening move** (`Main.lean:48`):
```lean
intro n input hinput env env'
change (main input).operations n |>.forAllFlat n
  { witness := fun k _ compute => env.AgreesBelow k env' → compute env = compute env' }
```
Then prove the *structural* version and bridge:
```lean
have hstruct : …FormalCircuitBase.Operations.StructuralComputableWitnesses input env env' n ((main input).operations n) := by
  unfold main
  simp only [Challenge.Utils.ComputableWitnessLemmas.Circuit.forEach_structuralComputableWitnesses_iff]
  intro i
  exact …FormalAssertion.assertion_structuralComputableWitnesses_of_condition
    (Num2Bits.circuit 8) input (input.buffer[i.val]) _ (by …) (Num2Bits.computableWitnesses 8) env env'
have hflat := …FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses input env env' hstruct
```
`hflat` gives `forAllFlat` for `computableWitnessCondition` (which carries the extra hypothesis `eval env input = eval env' input`); you then discharge that extra hypothesis from `hinput` by an induction over `FlatOperation` using `FlatOperation.forAll_implies`, `Condition.implies`, `Condition.ignoreSubcircuit`, `Operations.forAll_toFlat_iff`, `ProverEnvironment.agreesBelow_of_le` — this exact bridging block is `Main.lean:66-104` and is essentially boilerplate to copy.

For a *gadget* (`FormalAssertion`/`FormalCircuit`), the reusable form is `FormalCircuitBase.ComputableWitnesses`:
```lean
theorem computableWitnesses (n : ℕ) : (circuit n).ComputableWitnesses := by
  intro offset x env env'
  change Operations.forAllFlat offset (…FormalCircuitBase.computableWitnessCondition x env env') ((main n x).operations offset)
  apply …FormalCircuitBase.Operations.forAllFlat_of_structuralComputableWitnesses
  unfold main
  simp only [ …bind_structuralComputableWitnesses_iff, …witnessVector_…, …forEach_…, …assertZero_…, …pure_…, and_true, implies_true, forall_const]
  intro _ h_input
  …
```
(`GOLF/Solution/AssertBytes/Num2Bits.lean:104`), then `FormalCircuitBase.computableWitnesses_implies` converts to `ComputableWitnesses'` (`Num2Bits.lean:131`).

---

## Key combinators and lemmas

### `circuit_proof_start`
`CLEAN/Clean/Utils/Tactics/CircuitProofStart.lean` — `syntax "circuit_proof_start" ("[" term,* "]")? : tactic` (`:115`), core at `circuitProofStartCore` (`:11`), also exposed as `circuit_proof_start_core` (`:154`) and `circuit_proof_all [ …]` (`:158`, adds `simp_all; grind; done`).

Supported heads: `Soundness`, `FormalAssertion.Soundness`, `GeneralFormalCircuit.Soundness`, `GeneralFormalCircuit.WithHint.Soundness`, `Completeness`, `FormalAssertion.Completeness`, `GeneralFormalCircuit.Completeness`, `GeneralFormalCircuit.WithHint.Completeness`. Anything else → `throwError "circuit_proof_start can only be used on Soundness, Completeness and variants"`.

Exactly what it does, in order:
1. `unfold <the Soundness/Completeness def>`.
2. `intro` with fixed names:
   - Soundness (all four variants): `i₀ env input_var input h_input h_assumptions h_holds`
   - `Completeness`, `GeneralFormalCircuit.Completeness`, `GeneralFormalCircuit.WithHint.Completeness`: `i₀ env input_var h_env input h_input h_assumptions`
   - `FormalAssertion.Completeness`: `i₀ env input_var h_env input h_input h_assumptions h_spec`
3. `try simp only [circuit_norm] at input_var`, `at input`, `at h_input`.
4. `try dsimp only [Assumptions] at *`, then `Spec`, `ProverAssumptions`, `ProverSpec`, `elaborated`, `main` — **by literal identifier name in the current namespace**.
5. `try dsimp only [ElaboratedCircuit.withData, ElaboratedCircuit.output]`.
6. `try provable_struct_simp` (`CLEAN/Clean/Utils/Tactics/ProvableStructSimp.lean` — loops `split_provable_struct_eq`, `decompose_provable_struct`, `simplify_provable_struct_eval`, `simp only at *`).
7. `try simp only [circuit_norm, extras] at h_input`; `at h_assumptions`; `simp only [circuit_norm, h_input, extras] at h_holds`; `at h_env`; on the goal; `simp only [circuit_norm, extras] at h_spec`.

Idiom: pass every custom `main`/`Spec`/`Assumptions`/`.circuit` of *child gadgets* in the bracket list, e.g. `circuit_proof_start [main, Spec, Num2Bits.circuit, Num2Bits.Spec, Num2Bits.Assumptions]`.

### `elaborate_circuit`
`CLEAN/Clean/Circuit/Explicit.lean:688` (`elab "elaborate_circuit" : tactic`). Siblings: `elaborate_circuit_naive` (`:645`), `elaborate_circuit_naive_with t [using t']`, `elaborate_circuit_with t [using t']` (`:950`), `infer_explicit_circuit`, `infer_explicit_circuits`.

Mechanism: infers `ExplicitCircuits main` (class at `:669` with `output/localLength/operations` plus `_eq` proofs `by rfl`), then reads its projections and *normalizes* `localLength`, `output`, `channelsWithGuarantees`, `channelsWithRequirements` with `dsimp` + `simp` over the `explicit_circuit_norm` set, and assembles `ElaboratedCircuit.mk` directly. Debug: `set_option debug.elaborateCircuit true`. Related classes: `ExplicitCircuit`, `ExplicitCircuits.IsElaborated`, `ExplicitCircuits.toElaborated`, `ElaboratedCircuit.fromExplicit`, `ElaboratedCircuit.withData` / `ElaboratedCircuit.Data`.

Idiom: `instance elaborated : ElaboratedCircuit (F p) Input Output main := by elaborate_circuit`. This is the *only* accepted way to fill the `elaborated` obligation in a challenge (`definition_names` includes `Solution.X.elaborated`).

### `Count` and `CostIs` — `GOLF/Challenge/Utils/CostR1CS.lean`

```lean
structure Count where allocations : ℕ ; constraints : ℕ  deriving Repr, DecidableEq, Inhabited   -- :115
def Count.zero : Count := ⟨0,0⟩ ; def Count.add ; instance : Add Count
@[simp] Count.add_allocations, Count.add_constraints
Count.zero_add, Count.add_zero, Count.add_assoc
```

Counting functions: `flatOperationCount` (`:161`), `flatCount` (`:167`), `nestedCount` / `nestedListCount` (mutual, `:171`), `operationCount` (`:181`), `circuitCount c n := operationCount (Circuit.operations c n)` (`:190`).

Structural lemmas in `namespace Challenge.CostR1CS.Lemmas`:
`flatOperationsIsR1CS_nil`, `operationsIsR1CS_nil` (both `@[simp]`), `flatOperationsIsR1CS_append`, `operationsIsR1CS_append`, `operationsIsR1CS_iff_toFlat`, `operationCount_append`, `nestedListCount_append`, `operationCount_toNested`. Plus `operationCount_flatten_ofFn_const` (`:286`).

`CostIs` combinators (all in `Challenge.CostR1CS`):

| lemma | signature / result |
|---|---|
| `CostIs.pure (a : α)` | `CostIs (pure a) Count.zero` |
| `CostIs.bind (hf : CostIs f K₁) (hg : ∀ a, CostIs (g a) K₂)` | `CostIs (f >>= g) (K₁ + K₂)` |
| `CostIs.map (hf : CostIs f K)` | `CostIs (g <$> f) K` |
| `CostIs.witnessVector (m) (c)` | `CostIs (Circuit.witnessVector m c) ⟨m, 0⟩` |
| `CostIs.witnessVar (c)` | `⟨1, 0⟩` |
| `CostIs.witnessField (c)` | `⟨1, 0⟩` |
| `CostIs.assertZero (e)` | `CostIs (Circuit.assertZero e) ⟨0, 1⟩` |
| `CostIs.subcircuit {circuit : FormalCircuit F In Out} {b} (h : ∀ n, operationCount ((circuit.main b).operations n) = K)` | `CostIs (subcircuit circuit b) K` |
| `CostIs.assertion {circuit : FormalAssertion F In} {b} (h : ∀ n, operationCount ((circuit.main b).operations n) = K)` | `CostIs (assertion circuit b) K` |
| `CostIs.forEach (h : ∀ a n, operationCount ((body a).operations n) = K)` | `CostIs (Circuit.forEach xs body constant) ⟨m*K.allocations, m*K.constraints⟩` |
| `CostIs.mapFinRange (h : ∀ i n, …= K)` | `⟨m*…, m*…⟩` |
| `CostIs.foldlRange (h : ∀ s i n, …= K)` | `⟨m*…, m*…⟩` |
| `circuitCount_eq_of_CostIs (h : CostIs c K)` | `circuitCount c = K` |

Idiom for a subcircuit leaf (`GOLF/Solution/AssertBytes/Cost.lean:85`):
```lean
theorem costIs_assertion_num2Bits (n) (x) : CostIs (assertion (Num2Bits.circuit n) x) ⟨n, n + 1⟩ :=
  CostIs.assertion (fun m => costIs_num2Bits n x m)
```
Note the `h` argument is `∀ n, operationCount … = K`, i.e. literally an eta-expanded `CostIs` of the child's `main` — so `fun m => costIsChild _ m` works.

### `isR1CSRow` / `IsR1CSCirc` — `GOLF/Challenge/Utils/CostR1CS.lean`

Row predicates (`:40-83`):
```lean
def degree : Expression F → ℕ                -- var 1, const 0, add max, mul sum
def Affine (e) : Prop := degree e ≤ 1
def r1csProducts : Expression F → Option ℕ   -- counts degree-2 products along the add spine
def isR1CSRow (e) : Prop := match r1csProducts e with | some k => k ≤ 1 | none => False
def flatOperationsIsR1CS : List (FlatOperation F) → Prop   -- lookup/interact ⇒ False
def operationsIsR1CS [Field F] : Operations F → Prop        -- subcircuit ⇒ flatOperationsIsR1CS s.ops.toFlat
def isR1CSCircuit (c) (offset := 0) : Prop := operationsIsR1CS (Circuit.operations c offset)
def IsR1CSCirc (c : Circuit F α) : Prop := ∀ n, operationsIsR1CS (c.operations n)
```

`IsR1CSCirc` combinators:
`IsR1CSCirc.pure`, `.bind (hf) (hg : ∀ a, …)`, `.bind_out (hf) (hg : ∀ n, IsR1CSCirc (g (f.output n)))` ← **use this one whenever the continuation needs the witnessed output's affineness**, `.map`, `.witnessVector m c`, `.witnessVar`, `.witnessField`, `.assertZero (h : isR1CSRow e)`, `.subcircuit (h : ∀ n, operationsIsR1CS ((circuit.main b).operations n))`, `.assertion (same for FormalAssertion)`, `.forEach (h : ∀ a n, …)`, `.mapFinRange`, `.foldlRange`, `.foldlRange_inv (P) (hinit) (hbody : ∀ s i, P s → IsR1CSCirc (body s i)) (hstep : ∀ s i n, P s → P ((body s i).output n))`. Bridge: `isR1CSCircuit_of_IsR1CSCirc`. Helper: `operationsIsR1CS_flatten_ofFn`, `finFoldl_invariant`.

**`IsR1CSCirc.forEach` is often too weak** (it quantifies over *all* element values). The index-aware variant is defined in the *solution*, not the framework — copy it (`GOLF/Solution/AssertBytes/Cost.lean:33`):
```lean
theorem IsR1CSCirc.forEach_mem {α} {m} [Inhabited α] {xs : Vector α m} {body : α → Circuit (F circomPrime) Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n; rw [Circuit.forEach.operations_eq]; exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)
```

Degree/affine algebra (`:562-716`):
`degree_var`, `degree_const` (`@[simp]`), `degree_add`, `degree_mul`, `degree_neg`, `degree_sub`, `degree_fconst_mul`, `degree_mul_fconst`;
`Affine.const`, `Affine.var`, `Affine.add`, `Affine.neg`, `Affine.sub`, `Affine.fconst_mul`, `Affine.mul_fconst`, `Affine.zero`, `Affine.mul_deg0`;
`affine_finFoldl`, `affine_finFoldl'` (Fin-indexed — use for `fieldFromBitsExpr`-style accumulators);
`r1csProducts_of_affine`, `r1csProducts_add`, `r1csProducts_neg`, `r1csProducts_mul_affine`;
`isR1CSRow_of_r1csProducts`, `isR1CSRow_of_affine`, **`isR1CSRow_sub_mul (hC hA hB) : isR1CSRow (C - A*B)`**, `isR1CSRow_add_mul`, **`isR1CSRow_mul (hA hB) : isR1CSRow (A*B)`**.

Affineness of provable values (`:724-843`):
```lean
def AffineProvable {Input} [ProvableType Input] (input : Var Input F) : Prop :=
  ∀ i (hi : i < size Input), Affine ((toElements (M := Input) input)[i])
def AffineOutput {Output} [ProvableType Output] (c : Circuit F (Var Output F)) : Prop := ∀ n, AffineProvable (c.output n)
def AffineW {m} (v : Var (fields m) F) : Prop := ∀ i (hi : i < m), Affine v[i]
def ConstW {m} (v) : Prop := ∀ i (hi : i < m), degree v[i] = 0
```
with `AffineProvable.affineW`, `AffineW.affineProvable`, `ConstW.affineW`, `AffineW.left_of_append`, `AffineW.right_of_append`, `affineProvable_unit`, **`affineOutput_unit`** (the whole `hout` for assertion-style challenges), `affineOutput_of_affineW`, `affine_varFromOffset`, **`affineW_witnessVector_output (m) (c) (n)`**, `affineW_varFromOffset`, `affineProvable_varFromOffset`, `affine_witnessField_output`, `affineW_mapRange_var`. Top-level: `isR1CS_of_IsR1CSCirc (hops) (hout)`.

### Row-generic layer — `GOLF/Challenge/Utils/CostR1CSRow.lean`
Abstracts all of the above over an arbitrary row predicate `P : Expression F → Prop`:
`flatOperationsRow P`, `operationsRow P`, `flatOperationsRow_mono`, `operationsRow_mono`, `flatOperationsRow_append`, `operationsRow_append`, `operationsRow_iff_toFlat`, `operationsRow_flatten_ofFn`, `IsRowCirc P c := ∀ n, operationsRow P (c.operations n)`, `IsRowCirc.mono/.pure/.bind/.witnessVector/.assertZero/.subcircuit/.bind_out`, `isRowCirc_forEach_mem`. Bridges to the R1CS instance: `flatOperationsRow_isR1CSRow_iff`, `operationsRow_isR1CSRow_iff`, `isRowCirc_isR1CSRow_iff`.

### Canonical (identity-C) obligation — used by `*GF2Canonical` challenges
**Trusted spec**, `GOLF/Challenge/Utils/CostR1CSCanonicalSpec.lean` (4 defs, no theorems):
```lean
def isCidentityRowAt (k : ℕ) (e : Expression F) : Prop :=
  ∃ A B, Affine A ∧ Affine B ∧ e = (Expression.var ⟨k⟩ : Expression F) - A * B
def flatOperationsIsCid : ℕ → List (FlatOperation F) → Prop     -- pin counter; assert must pin k, then k+1
def IsCidCirc (c : Circuit F α) : Prop := ∀ n, flatOperationsIsCid n (Operations.toFlat (c.operations n))
def isR1CS_Cidentity (main) : Prop := ∀ input, AffineProvable input → IsCidCirc (main input) ∧ AffineOutput (main input)
attribute [irreducible] isCidentityRowAt flatOperationsIsCid
```
Challenge statement form (`GOLF/Challenge/Instances/SHA256CompressGF2Canonical/Challenge.lean:31`): `theorem isR1CS_Cidentity : Challenge.CostR1CS.isR1CS_Cidentity main` **replaces** `isR1CS`.

**Machinery**, `GOLF/Challenge/Utils/CostR1CSCanonical.lean` (must `attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid` to unfold):
`Affine.one`, `isCidentityRowAt_var_sub_mul`, `isCidentityRowAt.isR1CSRow`, `operationsIsCid` (ops-level mirror, also `irreducible` at the end of the file), `flatOperationsIsCid.flatOperationsIsR1CS`, `operationsIsCid.operationsIsR1CS`, `flatCount_append`, `flatCount_toFlat_nested`, `flatCount_toFlat_nestedList`, `flatOperationsIsCid_append`, `operationsIsCid_append`, `operationsIsCid_iff_toFlat`, `operationsIsCid_flatten_ofFn`, `isCidCirc_iff_ops`, `IsCidCirc.of_ops`, `IsCidCirc.ops`, `IsCidCirc.isR1CSCirc`, **`Balanced c := ∀ n, (operationCount (c.operations n)).constraints = c.localLength n`**, `Balanced.of_costIs`, `CostIs.constraints`, `IsCidCirc.pure`, `IsCidCirc.witnessVector`, `operationsIsCid_pure`, `operationsIsCid_witnessVector`, `IsCidCirc.bind (hf) (hbal : Balanced f) (hg)`, `IsCidCirc.bind_out`, `IsCidCirc.subcircuit`, `isR1CS_Cidentity_of_IsCidCirc`, `isR1CS_Cidentity.isR1CS`.

**Guarantees (reviewer-facing, not imported by the contract)**, `GOLF/Challenge/Utils/CostR1CSCanonicalGuarantees.lean`: `assertExprs`, `flatOperationsIsCid.pin`, `IsCidCirc.row_pins`, `guarantee_row_refines`, `guarantee_obligation_refines`, `guarantee_iff_ops`, plus accept/reject sanity examples.

### `ComputableWitnessLemmas` — `GOLF/Challenge/Utils/ComputableWitnessLemmas.lean`
Namespace `Challenge.Utils.ComputableWitnessLemmas`. Complete contents:

- `Condition.onlySubcircuits (condition) : Condition F`
- `Operations.forAllFlat_of_forAll_ignoreSubcircuit_and_subcircuits`
- `eval_mem_varFromOffset_fields_of_agreesBelow` — if `env.AgreesBelow k env'` and `offset + m ≤ k`, every entry of `varFromOffset (fields m) offset` evaluates equally.
- `FormalCircuitBase.computableWitnessCondition (input) (env env') : Condition F` — `witness n _ compute := env.AgreesBelow n env' → eval env input = eval env' input → compute env = compute env'`
- `FormalCircuitBase.FlatOperation.StructuralComputableWitnesses` (`@[circuit_norm]`), `…FlatOperation.forAll_of_structuralComputableWitnesses`, `…FlatOperation.structuralComputableWitnesses_iff_forAll`
- `FormalCircuitBase.Operations.structuralComputableWitnessCondition` (`@[circuit_norm]`)
- `FormalCircuitBase.Operations.StructuralComputableWitnesses` (`@[circuit_norm]`) — the compositional predicate to prove
- `…Operations.structuralComputableWitnesses_iff_forAll`, `…Operations.forAllFlat_of_structuralComputableWitnesses` ← **the bridge**, `…Operations.structuralComputableWitnesses_append` (`@[circuit_norm]`)
- `FormalCircuitBase.computableWitnesses_forAllFlat`, `compose_computableWitnesses_of_eq`, `compose_computableWitnesses_of_condition`, `computableWitnesses_implies`
- `namespace Circuit` — all `@[circuit_norm]` iff-lemmas, exactly the simp set for the `unfold main; simp only [...]` step:
  `pure_structuralComputableWitnesses_iff`, `witnessVector_…`, `witnessVar_…`, `assertZero_…`, `bind_…` (splits at offset `n + first.localLength n`), `witnessField_…`, `provableWitness_…` (for `ProvableType.witness`), `forEach_…` (`↔ ∀ i : Fin m, … at n + i.val * (body default).localLength`), `foldlRange_…` (uses `Circuit.FoldlM.foldlAcc`), `mapFinRange_…`
- `namespace FormalCircuit` — `subcircuit_structuralComputableWitnesses_iff` (`@[circuit_norm]`), `subcircuit_flatStructuralComputableWitnesses`, `subcircuit_flatStructuralComputableWitnesses_of_condition`
- `namespace GeneralFormalCircuit` — `subcircuit_flatStructuralComputableWitnesses`, `…_of_condition`
- `namespace FormalAssertion` — `assertion_structuralComputableWitnesses_iff` (`@[circuit_norm]`), `assertion_flatStructuralComputableWitnesses`, `assertion_flatStructuralComputableWitnesses_of_condition`, `subcircuit_flatStructuralComputableWitnesses_of_condition`, **`assertion_structuralComputableWitnesses_of_condition`** ← the one AssertBytes uses.

The `_of_condition` variants take the stronger, offset-aware input hypothesis
```lean
hinput : ∀ (k : ℕ) (env env'), n ≤ k → env.AgreesBelow k env' →
         eval env parentInput = eval env' parentInput → eval env input = eval env' input
```
(use these when the child's input is a *projection/derived* value of the parent input; the `_of_eq` variants need only `eval env parentInput = eval env' parentInput → eval env input = eval env' input`).

Framework side (`CLEAN/Clean/Circuit/Subcircuit.lean:404-467`): `FormalCircuitBase.ComputableWitnesses'`, `FormalCircuitBase.ComputableWitnesses`, `FormalCircuitBase.computableWitnesses_implies`, `FormalCircuitBase.compose_computableWitnesses`, `Circuit.subcircuit_computableWitnesses`. Supporting: `Operations.forAll_toFlat_iff`, `FlatOperation.forAll_toFlat_iff`, `FlatOperation.forAll_implies`, `Condition.implies`, `Condition.ignoreSubcircuit`, `ProverEnvironment.agreesBelow_of_le`, `FlatOperation.onlyAccessedBelow_all` (`CLEAN/Clean/Circuit/Theorems.lean:386-521`).

### `Clean/Utils/Bits.lean` — `namespace Utils.Bits`
`CLEAN/Clean/Utils/Bits.lean`. Nat layer: `toBits (n) (x : ℕ) : Vector ℕ n`, `fromBits`, `toBits_fromBits_aux`, `toBits_fromBits`, `fromBits_lt`, `toBits_injective`, `fromBits_toBits`, `fromBits_toBits_mod`.
Field layer (`variable {p} [Fact p.Prime]`):
```lean
def fieldToBits (n : ℕ) (x : F p) : Vector (F p) n := .map (↑) (toBits n x.val)
def fieldFromBits {n} (bits : Vector (F p) n) : F p := fromBits (bits.map ZMod.val)
def fieldFromBitsExpr {n} (bits : Vector (Expression (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc ⟨i,_⟩ => acc + bits[i] * (2^i : F p)) 0
```
Lemmas: `fieldFromBits_eval` (eval ∘ `fieldFromBitsExpr` = `fieldFromBits` ∘ map eval), `fieldToBits_bits` (each bit is 0 or 1), `fieldToBits_fieldFromBits_aux`, **`fieldFromBits_lt`** (unconditional `< 2^n`), `fieldToBits_fieldFromBits`, `fieldToBits_injective`, `val_natCast_toBits`, **`fieldFromBits_fieldToBits`** (needs `x.val < 2^n`), `fieldFromBits_fieldToBits_mod`, `fieldFromBits_succ`, `fieldFromBits_as_sum`, `fieldFromBits_eq`, `fieldFromBits_eq_mapFinRange_cast`.

This is the entire mathematical content of the AssertBytes baseline: `Num2Bits.main n x` = `witnessVector n (fun env => fieldToBits n (x.eval env))`, `forEach bits (fun b => assertZero (b*(b-1)))`, `assertZero (x - fieldFromBitsExpr bits)`.

### `F2Bits` — `GOLF/Challenge/Utils/F2Bits.lean`
`namespace Challenge.F2Bits`, for GF(2) challenges (`Blake3CompressGF2Canonical`, `KangarooTwelveGF2`, `SHA256CompressGF2Canonical`):
```lean
@[reducible] def p2 : ℕ := 2
instance : Fact (Nat.Prime p2) := ⟨Nat.prime_two⟩
@[reducible] def bitAt {N} (v : Vector (F p2) N) (k : ℕ) : ℕ := ZMod.val ((v[k]?).getD 0)
def wordAt (w) {N} (v) (i) : ℕ := ∑ j ∈ Finset.range w, bitAt v (w*i+j) * 2^j
def toWords (w n) {N} (v) : Vector ℕ n := Vector.ofFn fun i : Fin n => wordAt w v i.val
def toNat {N} (v : Vector (F p2) N) : ℕ := wordAt N v 0
```
Over `F 2`: `+` is XOR, `*` is AND, and `Fact (Nat.Prime 2)` is a *theorem*, not an axiom — so GF(2) challenges have no `hCircomPrime`-style axiom in `permitted_axioms`.

### Other Clean utils solutions import
`CLEAN/Clean/Utils/Field.lean` — `def F p := ZMod p`, `FieldUtils.ext`, `.ext_iff`, `.val_lt_p`, `.val_eq_256`, tactic `field_to_nat`.
`CLEAN/Clean/Utils/Primes.lean` — `p1009`, `pBabybear`, `pMersenne`.
`CLEAN/Clean/Utils/Bitwise.lean` — `not64`, `add32`, `rotRight8/32/64`, `rotLeft8/64`, `xor_eq_add`, `and_mul_two_pow`, `xor_mul_two_pow`, …
`CLEAN/Clean/Utils/Rotation.lean` — `rotRight{32,64}_*` (bv-rotate equivalence, testBit lemmas, `_toBits`, `_lt`, `_composition`).
`CLEAN/Clean/Utils/Fin.lean` — `Fin.foldl_to_sum`, `foldl_eq_sum_range`, `foldl_factor_const`, `foldl_sum_val_bound`, `sum_interchange`, `foldl_split_mul_add_distrib`.
`CLEAN/Clean/Utils/Misc.lean` — `Fin.foldl_const*`, `Fin.foldl_eq_foldl_finRange`, cast/heq helpers.
`CLEAN/Clean/Gadgets/Boolean.lean` — `IsBool x := x = 0 ∨ x = 1` plus a large algebra (`IsBool.iff_mul_sub_one`, `.val_lt_two`, `and_is_bool`, `xor_is_bool`, `xor_eq_val_xor`, …).
`CLEAN/Clean/Gadgets/Bits.lean` — `Gadgets.ToBits.main n x`, `toBits n (hn : 2^n < p) : GeneralFormalCircuit (F p) field (fields n)`, `rangeCheck n hn : FormalAssertion (F p) field`.
`CLEAN/Clean/Gadgets/IsZeroField.lean` — `Gadgets.IsZeroField.circuit : FormalCircuit F field field`.

Simp sets, registered in `CLEAN/Clean/Circuit/SimpGadget.lean`: `circuit_norm`, `explicit_circuit_norm`, `explicit_provable_type`.

---

## Gotchas

**`autoImplicit false` everywhere.** Both `CLEAN/lakefile.lean` and `GOLF/lakefile.lean` set `⟨autoImplicit, false⟩` and `⟨relaxedAutoImplicit, false⟩`. Every type variable must be bound explicitly (`variable {F : Type} [Field F] {m n : ℕ}` etc.); a stray unbound identifier is a hard error, not an auto-bound implicit.

**`hCircomPrime` is a genuine axiom.** `GOLF/Challenge/Instances/AssertBytes/Interface.lean:38` declares `axiom hCircomPrime : circomPrime.Prime` and derives `instance : Fact circomPrime.Prime`. It is whitelisted in `configs/*.json` under `permitted_axioms` alongside `propext`, `Quot.sound`, `Classical.choice`. Anything else your proof pulls in (`sorryAx`, `Lean.ofReduceBool` from `native_decide`, `Lean.trustCompiler`) fails the check. So: **no `native_decide`**, and the framework is explicitly designed so you never need it (that's the whole point of `CostIs`/`IsR1CSCirc` — see the module docstring at `CostR1CS.lean:268-277`).

**Reducibility attributes are load-bearing for elaboration, not semantics.**
- You *must* write `attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS` before `isR1CS` proofs (`GOLF/Solution/AssertBytes/Main.lean:111`, `GOLF/Solution/AssertBytes/Cost.lean:63`, `GOLF/Solution/SHA256/Main.lean:640`). Without it, unification whnf-reduces `r1csProducts` on real asserted expressions and hangs.
- Conversely the canonical predicates ship `irreducible` (`CostR1CSCanonicalSpec.lean:92`, `CostR1CSCanonical.lean:304`) and you must re-enable them locally with `attribute [local semireducible] isCidentityRowAt flatOperationsIsCid operationsIsCid`.
- `Eval.eval` is globally `irreducible` (`CLEAN/Clean/Circuit/CircuitType.lean:26`). Normalize it via `circuit_norm`/`explicit_provable_type` simp lemmas (`CircuitType.eval_verifier`, `CircuitType.eval_prover`, `CircuitType.eval_var_field_prover`), never by `unfold`.
- `Circuit.operations/output/localLength` are `@[reducible]`; `bufferLen`, `Output`, `allocations`, `constraints`, `p2` are `@[reducible]` so `⟨allocations, constraints⟩` unifies definitionally with computed counts like `⟨16*8, 16*9⟩`.

**`ProvableType.eval` / `toElements` / `fromElements` are NOT in `circuit_norm`.** They are `@[explicit_provable_type]` (`Provable.lean:44,57`) with *low* priority, deliberately, so higher-level `ProvableStruct` decompositions win. When you need to see raw elements, `simp [circuit_norm, explicit_provable_type]` (this is exactly what `AffineProvable.affineW` and `Cost.affineW_of_affineProvable_pvec` do).

**Instance requirements.**
- `Circuit.forEach` needs `[Inhabited α]` and a `ConstantLength body` (auto-param `by infer_constant_length`). `Circuit.mapFinRange` needs `[NeZero m]`. `Circuit.foldlRange` needs `[Inhabited β]` plus a `ConstantLength (fun (s,a) => body s a)`. If `infer_constant_length` fails, the loop combinator won't elaborate at all.
- `AffineProvable`/`AffineOutput`/`isR1CS` require `[ProvableType Input]` and `[ProvableType Output]` — not just `CircuitType`. `ComputableWitnessLemmas` mostly only needs `[CircuitType Parent]` for the parent.
- `Field F` is needed for `Operations F` to even typecheck (`Operation` is `[Field F]`-indexed); several `CostR1CS` lemmas carry `omit [Field F] in` because they only touch `Expression`.

**Subcircuit cost composition is exact, not additive-with-slack.** `CostIs.subcircuit`/`.assertion` (`CostR1CS.lean:340,358`) prove `operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] = K` by going through `nestedCount (toSubcircuit n b).ops = nestedListCount ((circuit.main b).operations n).toNested = operationCount ((circuit.main b).operations n)` (`operationCount_toNested`). So a subcircuit costs **exactly its `main`'s count at the same offset** — nesting adds zero overhead. Same for R1CS: `IsR1CSCirc.subcircuit` uses `Operations.toNested_toFlat` + `operationsIsR1CS_iff_toFlat`, i.e. the certificate is checked on the *flattened* body, so subcircuit boundaries are invisible to both obligations.

**Degree restriction for R1CS is syntactic and conservative.** `r1csProducts` counts products *along the top-level `add` spine* modulo constant factors. Consequences:
- `a*b + a*c` is rejected (counted as 2 products) even though it is genuinely rank-1 as `a*(b+c)`. **You must factor by hand.**
- Degree ≥ 3 anywhere is `none` → `False`.
- `a - b*c` works because `Sub`/`Neg` desugar to `add _ (mul (const (-1)) _)` and `r1csProducts` looks through the degree-0 factor (`CostR1CS.lean:52-60`).
- A pure affine row is accepted (`isR1CSRow_of_affine`, it is `A · 1 = 0`).
- `lookup` and `interact` operations make `operationsIsR1CS` **`False`**. An R1CS challenge therefore forbids lookup tables and channels entirely — range checks must be inlined as bit decompositions (that's why the baseline defines `Num2Bits` from primitives instead of reusing `Gadgets.ToBits.rangeCheck`).
- The canonical variant is strictly stronger: no separate linear case; a copy/sum row must be literally `var k − A * 1`, and the `C`-side variable is *prescribed* as `n₀ + t` in emission order (no permutation). Composition there additionally requires `Balanced` (constraints = localLength per subterm), discharged via `Balanced.of_costIs`.

**`Operations.Requirements` is part of the soundness goal.** `GeneralFormalCircuit.Soundness` returns `Spec … ∧ Operations.Requirements env (…)`. For channel-free circuits `circuit_norm` closes it (subcircuit case reduces to `s.channelsWithRequirements = [] ∨ s.Assumptions env`, and `toSubcircuit_channelsWithRequirements` gives `[]`). If you ever emit a channel interaction, this conjunct becomes real work — another reason R1CS challenges avoid channels.

**Completeness for `FormalAssertion` children carries the child's `Spec` as a hypothesis you must supply.** `FormalAssertion.toSubcircuit_completeness` (`Subcircuit.lean:589`) says `ProverAssumptions env = (Assumptions (eval env input) ∧ Spec (eval env input))`. So invoking an assertion gadget inside a completeness proof obliges you to *prove its spec* about the honest values — this is exactly why `AssertBytes.ProverAssumptions` needs `< 256` while `Assumptions = True`.

**`circuit_proof_start` unfolds by literal name.** Steps 4 in its script are `try dsimp only [Assumptions] at *` etc. with `mkIdent`. If your local definitions are named differently (or live in another namespace and aren't `open`ed), those steps silently no-op (they're all `try`). Similarly all the `simp only … at h_holds/h_env/h_input/h_assumptions/h_spec` steps are `try`-guarded, so **the tactic never fails loudly** — an unexpectedly ugly goal usually means a name didn't resolve. Also: it *renames* your hypotheses to `i₀ env input_var input h_input h_assumptions h_holds` (or `… h_env … h_spec`); those names are hard-coded and you should reference them.

**Offsets are symbolic, not `0`.** `CostIs`, `IsR1CSCirc`, `IsCidCirc`, `ComputableWitnesses` are all `∀ n` statements. Never prove at `n = 0` and hope; the bridges `circuitCount_eq_of_CostIs`, `isR1CSCircuit_of_IsR1CSCirc` go one way only. Inside soundness/completeness the offset is `i₀`, and witness variables are `var ⟨i₀ + i⟩` — the standard move is `set bit_vars := Vector.mapRange n (fun i => var ⟨i₀ + i⟩)` (`Num2Bits.lean:50`).

**Name-clash discipline between contract and solution.** `GOLF/Challenge/Instances/AssertBytes/Cost.lean` declares `Solution.AssertBytes.allocations`/`constraints` (placeholder `42`), and `GOLF/Solution/AssertBytes/Main.lean:113` declares the same fully-qualified names (`128`/`144`). This only works because **no module imports both**: the solution must import `Challenge.Instances.X.Interface` and `Challenge.Utils.*` but **never** `Challenge.Instances.X.Challenge` or `Challenge.Instances.X.Cost`. The checker substitutes the claimed cost into the challenge's `Cost.lean` and then type-checks `Solution.X.mainCost` against `circuitCost main ⟨allocations, constraints⟩`.

**`bind` vs `bind_out`.** `CostIs.bind`'s continuation is `∀ a, CostIs (g a) K₂` — fine, cost doesn't depend on the value. `IsR1CSCirc.bind`'s continuation is `∀ a, IsR1CSCirc (g a)` which is usually *unprovable* for witnessed outputs; use `IsR1CSCirc.bind_out (hg : ∀ n, IsR1CSCirc (g (f.output n)))` so you can feed `affineW_witnessVector_output` / `affineW_varFromOffset`. Same for `IsCidCirc.bind_out`.

**`===`'s hidden subcircuit.** `x === y` is `Gadgets.Equality.circuit` invoked as a `FormalAssertion` subcircuit, not a raw `assertZero`. Its cost and R1CS certificate must go through `CostIs.assertion` / `IsR1CSCirc.assertion`, not `CostIs.assertZero`. If you want a bare row, write `assertZero (x - y)` directly (the baseline does).

**`GeneralFormalCircuit` decouples soundness and completeness on purpose.** `Assumptions`/`Spec` (soundness, verifier view, sees `env.data`) are unrelated to `ProverAssumptions`/`ProverSpec` (completeness, prover view, sees `env.data` and `env.hint`). Do not assume `Spec` in completeness or `ProverAssumptions` in soundness — they are separate fields, and for a range-check-style circuit the soundness assumptions are deliberately `True` while completeness needs the range (`Formal.lean:228-241` explains this with `toBits`).
