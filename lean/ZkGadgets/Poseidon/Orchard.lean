import Mathlib.Data.ZMod.Basic
import ZkGadgets.Poseidon.Constants
import ZkGadgets.Audit

/-! Organizer Orchard/Pallas ConstantLength<2> model.
This defines the selected hash, not the full Orchard nullifier.
No collision, success probability, or attack cost is asserted here. -/
namespace Scribe.Poseidon.Orchard

instance : NeZero modulus := ⟨by decide⟩
abbrev F := ZMod modulus
abbrev Rounds := Fin 57

structure State where
  a : F
  b : F
  c : F
  deriving DecidableEq

def schedule (r : Rounds) : List Nat :=
  List.range 4 ++ (List.range r.val).map (· + 4) ++ [60, 61, 62, 63]

def roundStep (index : Nat) (s : State) : State :=
  let rc := roundConstants[index]!
  let a := s.a + (rc.1 : F)
  let b := s.b + (rc.2.1 : F)
  let c := s.c + (rc.2.2 : F)
  let a := a ^ 5
  let b := if index < 4 || index ≥ 60 then b ^ 5 else b
  let c := if index < 4 || index ≥ 60 then c ^ 5 else c
  let row (v : Nat × Nat × Nat) : F := (v.1 : F) * a + (v.2.1 : F) * b + (v.2.2 : F) * c
  ⟨row mds[0]!, row mds[1]!, row mds[2]!⟩

def permute (r : Rounds) (s : State) : State :=
  (schedule r).foldl (fun state index => roundStep index state) s

def hash (r : Rounds) (nk rho : F) : F :=
  (permute r ⟨nk, rho, (2 ^ 65 : Nat)⟩).a

/-- Boundary API rejects noncanonical inputs instead of reducing aliases mod p. -/
def digest? (r nk rho : Nat) : Option Nat :=
  if hr : r < 57 then
    if nk < modulus ∧ rho < modulus then
      some (hash ⟨r, hr⟩ (nk : F) (rho : F)).val
    else none
  else none

def decodeLE (bytes : List UInt8) : Nat :=
  bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

def encodeLE (n : Nat) : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat (n / 256 ^ i % 256))

/-- Exactly 64 bytes in, exactly 32 canonical little-endian output bytes. -/
def digestBytes? (r : Nat) (message : List UInt8) : Option (List UInt8) :=
  if message.length = 64 then
    (digest? r (decodeLE (message.take 32)) (decodeLE (message.drop 32))).map encodeLE
  else none

/-- Full-output collision relation; it has no witness in this module. -/
def Collision (r nk₁ rho₁ nk₂ rho₂ : Nat) : Prop :=
  (nk₁, rho₁) ≠ (nk₂, rho₂) ∧
    ∃ output, digest? r nk₁ rho₁ = some output ∧ digest? r nk₂ rho₂ = some output

theorem schedule_length (r : Rounds) : (schedule r).length = 8 + r.val := by
  simp [schedule]
  omega

theorem schedule_r3 : schedule ⟨3, by decide⟩ = [0, 1, 2, 3, 4, 5, 6, 60, 61, 62, 63] := by
  decide

theorem schedule_r56 : schedule ⟨56, by decide⟩ = List.range 64 := by
  decide

theorem rejects_alias (r rho : Nat) : digest? r modulus rho = none := by
  simp [digest?]

theorem rejects_rounds (r nk rho : Nat) (h : 57 ≤ r) : digest? r nk rho = none := by
  simp [digest?, Nat.not_lt.mpr h]

#audit_axioms schedule_length
#audit_axioms schedule_r3
#audit_axioms schedule_r56
#audit_axioms rejects_alias
#audit_axioms rejects_rounds

end Scribe.Poseidon.Orchard
