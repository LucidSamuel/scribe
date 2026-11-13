import Lean.Elab.Tactic.Omega
import ZkGadgets.Audit

/-! A finite trading example. Resource issuance draws from a counted reserve;
fees go to a counted treasury. Natural subtraction is intentional: affordability
is the condition preventing a debit from silently truncating. -/
namespace Butterfly

structure State where
  reserve : Nat
  alice : Nat
  bob : Nat
  treasury : Nat
  deriving DecidableEq, Repr

inductive Account where
  | alice | bob
  deriving DecidableEq, Repr

inductive Action where
  | issue (account : Account) (amount : Nat)
  | trade (account : Account) (amount : Nat)
  deriving DecidableEq, Repr

inductive Mutation where
  | baseline | boundaryRelax | guardRemoved | wrongDebit | duplicateCredit
  | boundaryStrict | unreachableBonus
  deriving DecidableEq, Repr

def cap : Nat := 8

def initial : State := ⟨8, 0, 0, 0⟩

def total (s : State) : Nat := s.reserve + s.alice + s.bob + s.treasury

def bounded (s : State) : Prop :=
  s.reserve ≤ cap ∧ s.alice ≤ cap ∧ s.bob ≤ cap ∧ s.treasury ≤ cap

instance (s : State) : Decidable (bounded s) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def accept (s : State) : Option State := if bounded s then some s else none

def balance (s : State) : Account → Nat
  | .alice => s.alice
  | .bob => s.bob

def affordable (m : Mutation) (amount funds : Nat) : Bool :=
  match m with
  | .boundaryRelax => decide (amount ≤ funds)
  | .guardRemoved => true
  | .boundaryStrict => decide (amount + 1 < funds)
  | _ => decide (amount < funds)

def debit (m : Mutation) (amount : Nat) : Nat :=
  if m = .wrongDebit then amount else amount + 1

def credit (m : Mutation) (amount : Nat) : Nat :=
  if m = .duplicateCredit then 2 * amount
  else if m = .unreachableBonus ∧ amount > cap then 2 * amount else amount

private def rawStep (m : Mutation) (s : State) (a : Action) : Option State :=
  match a with
  | .issue who amount =>
    if 0 < amount ∧ amount ≤ cap ∧ amount ≤ s.reserve then
      match who with
      | .alice => accept {s with reserve := s.reserve - amount, alice := s.alice + amount}
      | .bob => accept {s with reserve := s.reserve - amount, bob := s.bob + amount}
    else none
  | .trade who amount =>
    if 0 < amount ∧ amount ≤ cap ∧ affordable m amount (balance s who) = true then
      match who with
      | .alice => accept {s with alice := s.alice - debit m amount, bob := s.bob + credit m amount, treasury := s.treasury + 1}
      | .bob => accept {s with bob := s.bob - debit m amount, alice := s.alice + credit m amount, treasury := s.treasury + 1}
    else none

/-- Reject malformed states as well as out-of-range actions and outputs. -/
def step (m : Mutation) (s : State) (a : Action) : Option State :=
  if bounded s then rawStep m s a else none

def executeFrom (m : Mutation) (s : State) : List Action → Option State
  | [] => some s
  | a :: rest => (step m s a).bind (fun next => executeFrom m next rest)

def execute (m : Mutation) (actions : List Action) : Option State := executeFrom m initial actions

def SafeMutation (m : Mutation) : Prop :=
  m = .baseline ∨ m = .boundaryStrict ∨ m = .unreachableBonus

private theorem accept_eq {s t : State} (h : accept s = some t) : s = t := by
  unfold accept at h
  split at h <;> simp_all

/-- All accepted steps of the baseline and safe controls conserve resources. -/
theorem step_conserves {m : Mutation} (safe : SafeMutation m)
    {s t : State} {a : Action} (h : step m s a = some t) : total t = total s := by
  unfold step at h
  split at h
  all_goals try { simp at h }
  rcases safe with rfl | rfl | rfl <;>
    cases a with
    | issue who amount =>
      cases who <;> simp only [rawStep] at h <;> split at h
      all_goals try { simp at h }
      all_goals have eq := accept_eq h
      all_goals subst t
      all_goals simp only [total]
      all_goals omega
    | trade who amount =>
      cases who <;> simp only [rawStep, balance] at h <;> split at h
      all_goals try { simp at h }
      all_goals have eq := accept_eq h
      all_goals subst t
      all_goals simp_all [total, debit, credit, affordable]
      all_goals first | omega | (split <;> omega)

/-- Conservation applies to every length of successfully executed trace. -/
theorem executeFrom_conserves {m : Mutation} (safe : SafeMutation m)
    (actions : List Action) {s t : State}
    (h : executeFrom m s actions = some t) : total t = total s := by
  induction actions generalizing s with
  | nil => simp [executeFrom] at h; subst t; rfl
  | cons a rest ih =>
    simp only [executeFrom] at h
    cases hs : step m s a with
    | none => simp [hs] at h
    | some next =>
      simp only [hs, Option.bind_some] at h
      exact (ih h).trans (step_conserves safe hs)

theorem baseline_conservation {actions : List Action} {t : State}
    (h : execute .baseline actions = some t) : total t = 8 :=
  executeFrom_conserves (Or.inl rfl) actions h

theorem boundaryStrict_conservation {actions : List Action} {t : State}
    (h : execute .boundaryStrict actions = some t) : total t = 8 :=
  executeFrom_conserves (Or.inr (Or.inl rfl)) actions h

theorem unreachableBonus_conservation {actions : List Action} {t : State}
    (h : execute .unreachableBonus actions = some t) : total t = 8 :=
  executeFrom_conserves (Or.inr (Or.inr rfl)) actions h

#audit_axioms boundaryStrict_conservation
#audit_axioms unreachableBonus_conservation

#audit_axioms step_conserves
#audit_axioms executeFrom_conserves
#audit_axioms baseline_conservation

end Butterfly
