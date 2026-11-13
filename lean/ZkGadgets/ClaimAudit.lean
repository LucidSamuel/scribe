import ZkGadgets.Audit

/-! Bind package statements to theorem declarations and audit actual dependencies.
Inputs are string literals: the statement is parsed as one term, never commands.
The first version supports closed declarations without universe parameters. -/
open Lean Elab Command Meta

elab "#audit_claim " decl:str statement:str declaredAxioms:str expectedModule:str : command => do
  liftTermElabM do
    let name := decl.getString.toName
    let info ← getConstInfo name
    let env ← getEnv
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "claim declaration must come from an imported artifact module"
    unless env.header.moduleNames[moduleIdx.toNat]! == expectedModule.getString.toName do
      throwError "claim declaration is not defined in its artifact module"
    unless info.isTheorem do
      throwError "claim declaration must be a theorem"
    unless info.levelParams.isEmpty do
      throwError "claim audit currently requires a declaration without universe parameters"
    let stx ← match Parser.runParserCategory (← getEnv) `term statement.getString with
      | .ok stx => pure stx
      | .error error => throwError "invalid claim statement: {error}"
    let expected ← Term.elabType stx
    Term.synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    if expected.hasMVar then
      throwError "claim statement contains unresolved metavariables"
    unless ← isProp expected do
      throwError "claim statement must be a proposition"
    unless ← isDefEq info.type expected do
      throwError "claim statement does not match theorem type"
    -- Send the binding itself through the kernel as well as checking defeq.
    ScribeAudit.addProbeTheorem name "claimBinding" expected (mkConst name)
    let used ← Lean.collectAxioms name
    unless (ScribeAudit.untrustedAxioms used).isEmpty do
      throwError "claim uses untrusted axioms: {used}"
    let actual := (used.toList.map toString).mergeSort
    let declared := if declaredAxioms.getString.isEmpty then []
      else (declaredAxioms.getString.splitOn ",").mergeSort
    unless actual == declared do
      throwError "declared axioms do not match actual dependencies: {actual}"
