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
gates next to a theorem. The remaining checks — finite-model non-vacuity probes
(C2), antecedent satisfiability (C3), and an adversarial refuter (C4) — are future
work and not implemented here.
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

end ScribeAudit.SelfTest
