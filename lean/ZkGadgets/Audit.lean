import Lean

/-!
# Spec audit — hypothesis-liveness checks (verdict engine, C1)

The Lean kernel checks that a *proof* is correct, but nothing checks that the
*statement* is meaningful. This module is the deterministic core of a "verdict
engine": a refuter that complements the (single-sided) proof loop by flagging
degenerate statements a kernel-accepted proof would otherwise hide.

It implements **C1, hypothesis-liveness**, which catches two real regression
classes that both shipped in this repo at one point:

* **Decorative hypothesis** — a statement carries an explicit hypothesis its proof
  never uses (e.g. a bound passed to a `Spec` but ignored). `#audit_uses` flags it.
* **Dropped side-condition** — an intended hypothesis never reaches the signature
  (e.g. a `variable (hp : p > 256)` the theorem never references, so Lean omits it).
  `#audit_requires` guards a load-bearing condition by name.

Both commands fail the build (`logError`) when they fire, so they act as live CI
gates next to a theorem.

Alongside these statement-liveness checks, `#audit_axioms` guards *proof* soundness:
it runs the kernel's own dependency tracking (the engine behind `#print axioms`) and
fails the build unless the theorem rests only on `{propext, Classical.choice, Quot.sound}`.
This is the source of truth that the textual pre-filter scans only approximate — it
catches a transitive `sorryAx` (what an unfinished proof or `admit` elaborate to) or
`Lean.ofReduceBool` (the native-decision escape hatch) reached through any dependency,
which a grep cannot.

**C2, finite-model non-vacuity** (`#audit_falsifiable`) and **C3, antecedent
satisfiability** (`#audit_satisfiable`) probe the *statement* against a concrete
finite model. Both read the theorem's actual signature, instantiate its binders at
user-supplied values (e.g. `(p := 257) (x := 256)`), and add a kernel-checked
auxiliary theorem:

* `#audit_falsifiable` proves `¬ conclusion` at the instantiation — if no such
  refutation exists the command fails, catching a conclusion that is `True` in
  disguise (the vacuous-existential class: `∃ k : Fin 256, (k : ZMod p) = x` is
  unfalsifiable when `p ≤ 256`).
* `#audit_satisfiable` proves every hypothesis at the witness — if one fails the
  command names it, catching vacuity-by-impossible-antecedent ("the constraints
  can never hold, so the theorem says nothing").

A theorem passing C1 + C2 + C3 has demonstrated content: its hypotheses can hold,
its conclusion can fail, and its side-conditions are load-bearing. The probes are
derived from the signature, so a spec that drifts back toward vacuity turns the
build red. Scope: probes need decidable, enumerable instantiations — flat `ZMod p`
gadget statements qualify; Halva circuit-level theorems (function-typed circuits)
keep hand-written witnesses instead. The adversarial LLM refuter (C4) remains
future work.
-/

open Lean Elab Command Meta

namespace ScribeAudit

/-- The names of a declaration's **explicit, proposition-typed** binders that do not
    occur in its proof term — i.e. hypotheses the proof never uses. A non-empty
    result is a "decorative hypothesis" smell. -/
def unusedHyps (declName : Name) : MetaM (Array Name) := do
  let info ← getConstInfo declName
  -- `ConstantInfo.value?` excludes theorems, so match explicitly.
  let value ← match info with
    | .thmInfo ti => pure ti.value
    | .defnInfo di => pure di.value
    | _ => throwError "audit: '{declName}' has no proof term to inspect"
  lambdaTelescope value fun args body => do
    let mut unused : Array Name := #[]
    for arg in args do
      let fvarId := arg.fvarId!
      let ldecl ← fvarId.getDecl
      -- only consider explicit hypotheses; skip implicits and instance arguments
      if ldecl.binderInfo.isExplicit && (← isProp ldecl.type) then
        unless body.hasAnyFVar (· == fvarId) do
          unused := unused.push ldecl.userName
    return unused

/-- Render a declaration's type as a flat string for substring checks. -/
def signatureString (declName : Name) : MetaM String := do
  let info ← getConstInfo declName
  return toString (← ppExpr info.type)

/-- The only axioms a kernel-checked proof in this repo is permitted to rest on:
    propositional extensionality, quotient soundness, and choice. Anything else is
    a soundness escape hatch — most importantly `sorryAx` (what an unfinished proof,
    `admit`, or a homoglyph trick all elaborate to) and `Lean.ofReduceBool` (emitted
    by the native-decision tactic), plus any hand-declared assumption. -/
def trustedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The subset of `used` outside `trustedAxioms` — the escape hatches a declaration
    actually reached. Empty ⇒ the proof rests only on the trusted set. Order-preserving
    so error messages list offenders as the kernel reports them. -/
def untrustedAxioms (used : Array Name) : Array Name :=
  used.filter (fun a => !trustedAxioms.contains a)

/-- A fresh, unused name under `base` for a kernel-checked probe artifact. -/
def freshProbeName (base : Name) (suffix : String) : CoreM Name := do
  let env ← getEnv
  let mut i := 1
  while env.contains (base ++ Name.mkSimple s!"{suffix}_{i}") do
    i := i + 1
  return base ++ Name.mkSimple s!"{suffix}_{i}"

/-- Add `type := value` as a kernel-checked auxiliary theorem. `addDecl` sends the
    proof through the kernel, so a probe that "passes" here carries the same trust
    as any hand-written witness `example`. -/
def addProbeTheorem (base : Name) (suffix : String) (type value : Expr) : MetaM Unit := do
  let name ← freshProbeName base suffix
  addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- Kernel-decidable proof of `p`, or a probe-flavoured error.

    `Meta.mkDecideProof` constructs its proof *unchecked* (the kernel only sees it
    at `addDecl`, possibly asynchronously), so first evaluate `decide p` with the
    kernel's own reducer and throw synchronously unless it yields `true`. -/
def decideProbe (p : Expr) (what : MessageData) : MetaM Expr := do
  let d ← try
    Meta.mkDecide p
  catch _ =>
    throwError "audit ✗ probe: {what} is not decidable:{indentExpr p}"
  let reduced := Kernel.whnf (← getEnv) (← getLCtx) d
  unless (reduced.toOption.map (·.isConstOf ``Bool.true)).getD false do
    throwError "audit ✗ probe: {what} does not hold:{indentExpr p}"
  Meta.mkDecideProof p

/-- What a probe evaluates: the conclusion's refutability (C2) or the joint truth
    of the hypotheses at a witness (C3). -/
inductive ProbeMode
  | falsifiable
  | satisfiable
  deriving BEq

/-- Instantiate `declName`'s statement at the user-provided `bindings` and run the
    probe. The telescope is analysed first: only binders the probe's targets
    (conclusion for C2, hypothesis types for C3) transitively depend on are
    *needed*; everything else may be omitted from `bindings`.

    * needed value binders must be bound (clear error otherwise);
    * needed instance binders are synthesized, with a `Fact q`-via-`decide`
      fallback for literals like `[Fact (Nat.Prime 257)]` (no global instance);
    * proposition binders are the hypotheses: C3 kernel-checks each at the
      witness; C2 ignores them — falsifiability of the conclusion *in isolation*
      is exactly what separates "theorem with content" from "anything proves this". -/
def runProbe (declName : Name) (bindings : Array (Name × Term)) (mode : ProbeMode) :
    Elab.TermElabM Unit :=
  -- Reducing `decide` proofs of statement-sized props (sums over `Fin n`, `ZMod`
  -- arithmetic) legitimately recurses past the default 512; raise the ceiling so
  -- probe authors don't have to `set_option maxRecDepth` at every use site.
  withTheReader Core.Context
    (fun ctx => { ctx with maxRecDepth := max ctx.maxRecDepth 8192 }) do
  let info ← getConstInfo declName
  -- Gadget statements live in `Prop` over `Type 0`; degrade gracefully otherwise.
  let ty := info.type.instantiateLevelParams info.levelParams
    (info.levelParams.map fun _ => Level.zero)
  Meta.forallTelescope ty fun fvars concl => do
    let mut decls : Array (Expr × Name × Expr × BinderInfo × Bool) := #[]
    for fv in fvars do
      let d ← fv.fvarId!.getDecl
      decls := decls.push (fv, d.userName, d.type, d.binderInfo, ← Meta.isProp d.type)
    -- Needed = fvars the probe targets depend on, closed transitively through
    -- binder types (walking the telescope backwards reaches a fixpoint).
    let targets : Array Expr := match mode with
      | .falsifiable => #[concl]
      | .satisfiable => decls.filterMap fun (_, _, t, _, isPropHyp) =>
          if isPropHyp then some t else none
    let mut needed : Array FVarId := #[]
    for fv in fvars do
      if targets.any (·.containsFVar fv.fvarId!) then
        needed := needed.push fv.fvarId!
    for i in [0:decls.size] do
      let (fv, _, t, _, _) := decls[decls.size - 1 - i]!
      if needed.contains fv.fvarId! then
        for fv' in fvars do
          if t.containsFVar fv'.fvarId! && !needed.contains fv'.fvarId! then
            needed := needed.push fv'.fvarId!
    -- Substitute in telescope order.
    let mut replaced : Array Expr := #[]
    let mut values : Array Expr := #[]
    let mut used : Array Name := #[]
    for (fv, binderName, t, binderInfo, isPropHyp) in decls do
      let t := t.replaceFVars replaced values
      if let some (_, stx) := bindings.find? (·.1 == binderName) then
        let v ← Elab.Term.elabTermEnsuringType stx t
        Elab.Term.synthesizeSyntheticMVarsNoPostponing
        replaced := replaced.push fv
        values := values.push (← instantiateMVars v)
        used := used.push binderName
      -- Instance binders are classified BEFORE Prop binders: `[Fact (Nat.Prime p)]`
      -- is Prop-typed, but it is a side-condition to synthesize (or decide), not a
      -- constraint hypothesis to check at the witness.
      else if binderInfo == .instImplicit then
        if needed.contains fv.fvarId! then
          let inst ← try
            synthInstance t
          catch _ =>
            -- `Fact` is referenced by name (this module does not import Mathlib);
            -- it resolves in the environment of the file running the probe.
            let (fn, args) := t.getAppFnArgs
            if fn == `Fact && args.size == 1 then
              mkAppM `Fact.mk #[← decideProbe args[0]! m!"instance side-condition"]
            else
              throwError "audit ✗ probe: cannot synthesize instance {t} for '{binderName}'"
          replaced := replaced.push fv
          values := values.push inst
      else if isPropHyp then
        if mode == .satisfiable then
          let prf ← decideProbe t
            m!"hypothesis '{binderName}' of {declName} at the given witness"
          addProbeTheorem declName "auditSatisfiable" t prf
          replaced := replaced.push fv
          values := values.push prf
      else if needed.contains fv.fvarId! then
        throwError "audit ✗ probe: binder '{binderName}' : {t} needs a value — \
          add ({binderName} := ...)"
    for (n, _) in bindings do
      unless used.contains n do
        throwError "audit ✗ probe: no binder named '{n}' in {declName}"
    if mode == .falsifiable then
      let concl := concl.replaceFVars replaced values
      if concl.hasFVar then
        throwError "audit ✗ probe: the conclusion of {declName} still mentions a \
          binder after instantiation:{indentExpr concl}"
      let neg := mkNot concl
      let prf ← decideProbe neg m!"the negation of the conclusion of {declName} \
        (is the spec vacuously true at this instantiation?)"
      addProbeTheorem declName "auditFalsifiable" neg prf

/-- C2 core: the conclusion of `declName`, instantiated at `bindings`, must be
    **falsifiable** — a kernel-checked proof of its negation is added. Failure means
    the conclusion is `True` in disguise at this model (a vacuous spec), or the
    instantiation is not decidable. -/
def probeFalsifiable (declName : Name) (bindings : Array (Name × Term)) :
    Elab.TermElabM Unit :=
  runProbe declName bindings .falsifiable

/-- C3 core: every hypothesis of `declName`, instantiated at `bindings`, must
    **hold at the witness** — each gets a kernel-checked proof. Failure names the
    hypothesis, catching vacuity-by-impossible-antecedent. -/
def probeSatisfiable (declName : Name) (bindings : Array (Name × Term)) :
    Elab.TermElabM Unit :=
  runProbe declName bindings .satisfiable

end ScribeAudit

/-- `#audit_uses thm` fails the build if `thm` has an explicit hypothesis its proof
    never uses (a decorative / possibly-vacuous hypothesis). Silent on success, so it
    works as a live regression gate placed next to a theorem. -/
elab "#audit_uses " id:ident : command => do
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload id
    let unused ← ScribeAudit.unusedHyps declName
    unless unused.isEmpty do
      let names := String.intercalate ", " (unused.toList.map toString)
      logError m!"audit ✗ {declName}: unused (possibly decorative) hypotheses: {names}"

/-- `#audit_requires thm "needle"` fails the build unless `needle` appears in `thm`'s
    signature. Use it to pin a load-bearing side-condition (e.g. `"p > 256"`) so that
    silently dropping it — the classic vacuous-spec regression — turns the build red. -/
elab "#audit_requires " id:ident needle:str : command => do
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload id
    let sig ← ScribeAudit.signatureString declName
    let needleStr := needle.getString
    unless (sig.splitOn needleStr).length ≥ 2 do
      logError m!"audit ✗ {declName}: required hypothesis '{needleStr}' is absent from the signature — it may have been dropped"

/-- `#audit_axioms thm` runs the kernel's own dependency tracking (the engine behind
    `#print axioms`) on `thm` and fails the build unless every constant it depends on
    is in `ScribeAudit.trustedAxioms`. This is the *source of truth* for soundness:
    it sees a transitive `sorryAx` reached through any dependency and cannot be fooled
    by `admit`, a `sorryAx` homoglyph, or a `lake build` that only warns rather than
    errors. The textual scans are a fast pre-filter; this command is the guarantee. -/
elab "#audit_axioms " id:ident : command => do
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload id
    let used ← Lean.collectAxioms declName
    let bad := ScribeAudit.untrustedAxioms used
    unless bad.isEmpty do
      let names := String.intercalate ", " (bad.toList.map toString)
      logError m!"audit ✗ {declName}: depends on untrusted constants: {names} \
        (only {ScribeAudit.trustedAxioms} are permitted)"

/-- One `(name := value)` instantiation for a probe command. -/
syntax auditBinding := "(" ident " := " term ")"

private def parseBindings (bs : Array (TSyntax `auditBinding)) :
    CommandElabM (Array (Name × Term)) :=
  bs.mapM fun b => match b with
    | `(auditBinding| ($n:ident := $v:term)) => pure (n.getId, v)
    | _ => Elab.throwUnsupportedSyntax

/-- `#audit_falsifiable thm (p := 257) (x := 256)` — C2, finite-model non-vacuity.
    Instantiates `thm`'s conclusion at the given values and adds a kernel-checked
    proof of its **negation**. If none exists, the conclusion is vacuously true at
    this model and the build fails: this is the probe that catches the
    `∃ k : Fin 256, (k : ZMod p) = x` class of spec (unfalsifiable when `p ≤ 256`).
    Binders not mentioned in the conclusion may be omitted. -/
elab "#audit_falsifiable " id:ident bs:auditBinding* : command => do
  let bindings ← parseBindings bs
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload id
    ScribeAudit.probeFalsifiable declName bindings

/-- `#audit_satisfiable thm (p := 257) (x := 255) (bits := fun _ => 1)` — C3,
    antecedent satisfiability. Checks that the provided witness satisfies **every**
    hypothesis of `thm`, each via a kernel-checked `decide` proof; fails naming the
    first hypothesis the witness violates. Guards against the other vacuity mode:
    constraints that can never hold make any soundness theorem empty. -/
elab "#audit_satisfiable " id:ident bs:auditBinding* : command => do
  let bindings ← parseBindings bs
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload id
    ScribeAudit.probeSatisfiable declName bindings

namespace ScribeAudit.SelfTest

-- The decoy below deliberately ignores a hypothesis; that is the property under test.
set_option linter.unusedVariables false

-- A hypothesis the proof never uses: must be reported.
private theorem decoy_decorative (n : Nat) (hbig : n > 5) : n = n := rfl
-- A hypothesis the proof genuinely uses: must not be reported.
private theorem decoy_live (n : Nat) (h : n = 0) : n = 0 := h

-- Deterministic unit test of the detection logic (independent of message wording).
run_cmd liftTermElabM do
  let bad ← ScribeAudit.unusedHyps ``decoy_decorative
  unless bad == #[`hbig] do
    throwError "audit self-test failed: expected [hbig] unused, got {bad}"
  let good ← ScribeAudit.unusedHyps ``decoy_live
  unless good.isEmpty do
    throwError "audit self-test failed: expected no unused hyps, got {good}"

-- Deterministic unit test of the trusted-set filter. Uses `sorryAx`/`ofReduceBool`
-- as name literals only, so the test needs no genuinely-unsound declaration and the
-- file stays clean under the textual pre-filter.
run_cmd liftTermElabM do
  let flagged := ScribeAudit.untrustedAxioms #[`sorryAx, `propext, `Lean.ofReduceBool, `Quot.sound]
  unless flagged == #[`sorryAx, `Lean.ofReduceBool] do
    throwError "trusted-set self-test failed: expected [sorryAx, Lean.ofReduceBool] flagged, got {flagged}"
  unless (ScribeAudit.untrustedAxioms #[`propext, `Classical.choice, `Quot.sound]).isEmpty do
    throwError "trusted-set self-test failed: permitted set wrongly flagged"

-- Happy path through the real command: a fully-proved decl passes silently.
#audit_axioms decoy_live

-- ── C2/C3 probe self-tests ──────────────────────────────────────────────────

-- Content: hypotheses satisfiable, conclusion falsifiable. Both probes must pass.
private theorem decoy_content (n : Nat) (h : n ≤ 0) : n = 0 := Nat.le_zero.mp h
-- Vacuous conclusion (`0 ≤ n` holds for every Nat): C2 must reject it.
private theorem decoy_vacuous_concl (n : Nat) (h : n < 3) : 0 ≤ n := Nat.zero_le n
-- Impossible antecedent (`n < n` never holds): C3 must reject any witness.
private theorem decoy_unsat_hyp (n : Nat) (h : n < n) : n = 37 :=
  absurd h (Nat.lt_irrefl n)

-- Happy paths through the real commands: pass silently (and add kernel-checked
-- probe artifacts under the decoy's namespace).
#audit_falsifiable decoy_content (n := 1)
#audit_satisfiable decoy_content (n := 0)

-- Failure paths, asserted via the core functions (a failing command would fail
-- this build; the cores throw instead, so we can require that they do).
run_cmd liftTermElabM do
  let one ← `(1)
  let mut caught := false
  try ScribeAudit.probeFalsifiable ``decoy_vacuous_concl #[(`n, one)]
  catch _ => caught := true
  unless caught do
    throwError "probe self-test failed: vacuous conclusion not rejected by C2"
  caught := false
  try ScribeAudit.probeSatisfiable ``decoy_unsat_hyp #[(`n, one)]
  catch _ => caught := true
  unless caught do
    throwError "probe self-test failed: impossible antecedent not rejected by C3"
  -- A binding that names no binder must be rejected, not silently ignored.
  caught := false
  try ScribeAudit.probeFalsifiable ``decoy_content #[(`nonexistent, one)]
  catch _ => caught := true
  unless caught do
    throwError "probe self-test failed: unknown binder name not rejected"

end ScribeAudit.SelfTest
