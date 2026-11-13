import ZkGadgets.Butterfly.Model

namespace Butterfly

/-- A meaningful trade is reachable, so conservation is not vacuous. -/
theorem nontrivial_trade :
    execute .baseline [.issue .alice 3, .trade .alice 1] = some ⟨5, 1, 1, 1⟩ := by
  decide

/-- The same trace is possible under the stricter safe control. -/
theorem strict_nontrivial_trade :
    execute .boundaryStrict [.issue .alice 3, .trade .alice 1] = some ⟨5, 1, 1, 1⟩ := by
  decide

/-- Relaxing one boundary lets subtraction truncate the unpaid fee. -/
theorem boundary_exploit :
    execute .boundaryRelax [.issue .alice 1, .trade .alice 1] = some ⟨7, 0, 1, 1⟩ ∧
    total ⟨7, 0, 1, 1⟩ ≠ total initial ∧
    execute .baseline [.issue .alice 1, .trade .alice 1] = none := by
  decide

/-- Removing affordability allows a completely unfunded trade. -/
theorem removed_guard_exploit :
    execute .guardRemoved [.trade .alice 1] = some ⟨8, 0, 1, 1⟩ ∧
    total ⟨8, 0, 1, 1⟩ ≠ total initial ∧
    execute .baseline [.trade .alice 1] = none := by
  decide

/-- A debit omitting the fee creates one unit, despite a sufficient balance. -/
theorem wrong_debit_exploit :
    execute .wrongDebit [.issue .alice 2, .trade .alice 1] = some ⟨6, 1, 1, 1⟩ ∧
    total ⟨6, 1, 1, 1⟩ ≠ total initial ∧
    execute .baseline [.issue .alice 2, .trade .alice 1] = some ⟨6, 0, 1, 1⟩ := by
  decide

/-- A duplicated credit creates one unit; the baseline accepts a different outcome. -/
theorem duplicate_credit_exploit :
    execute .duplicateCredit [.issue .alice 2, .trade .alice 1] = some ⟨6, 0, 2, 1⟩ ∧
    total ⟨6, 0, 2, 1⟩ ≠ total initial ∧
    execute .baseline [.issue .alice 2, .trade .alice 1] = some ⟨6, 0, 1, 1⟩ := by
  decide

#audit_axioms nontrivial_trade
#audit_axioms strict_nontrivial_trade
#audit_axioms boundary_exploit
#audit_axioms removed_guard_exploit
#audit_axioms wrong_debit_exploit
#audit_axioms duplicate_credit_exploit

end Butterfly
