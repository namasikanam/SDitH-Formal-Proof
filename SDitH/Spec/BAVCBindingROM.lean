import SDitH.Spec.BAVCBinding
import SDitH.Spec.RandomOracleCollision

/-! Binding experiment for fully queried two-layer BAVC hash computations.
The adversarial procedure uses the shared lazy oracle on actual bit strings.
Its final choice may depend on the entire final result. Both query lists must
be stored: the experiment does not claim to cover unqueried guesses. Relating
this experiment's total query budget to complete signing/verification remains
a separate proof obligation. The seed/cipher part of BAVC is not modeled here. -/

namespace SDitH.Spec.BAVCBindingROM

open BAVC BAVCBinding RandomOracleCollision

structure Claim (lambda tau N : Nat) where
  leftSalt : Seed lambda
  rightSalt : Seed lambda
  left : Commitments lambda tau N
  right : Commitments lambda tau N

variable {lambda tau N : Nat} {State : Type*}

/-- The supplied seed operations are unchanged and unused by this hash-only
experiment. The default only totalizes lookups; every accepted lookup is checked. -/
def withTable (p : Primitives lambda) (table : List Bool → Option (Digest lambda)) : Primitives lambda :=
  { p with hash := fun input => (table input).getD (fun _ => false) }

def observed (p : Primitives lambda) (table : List Bool → Option (Digest lambda))
    (salt : Seed lambda) (commits : Commitments lambda tau N) : Bool :=
  (hashQueries (withTable p table) salt commits).all (fun input => (table input).isSome)

/-- Distinct salt/leaf-commitment data with the same root, with every row and
outer hash present in the shared table. This is an event, not an assumption. -/
def claimWins (p : Primitives lambda) (claim : Claim lambda tau N)
    (out : Result (List Bool) (Digest lambda) State) : Bool :=
  observed p out.table claim.leftSalt claim.left && observed p out.table claim.rightSalt claim.right &&
    decide (rootHash (withTable p out.table) claim.leftSalt claim.left =
      rootHash (withTable p out.table) claim.rightSalt claim.right ∧
      (claim.leftSalt ≠ claim.rightSalt ∨ claim.left ≠ claim.right))

def bindingWins (p : Primitives lambda) (choose : Result (List Bool) (Digest lambda) State → Option (Claim lambda tau N))
    (out : Result (List Bool) (Digest lambda) State) : Bool :=
  match choose out with
  | none => false
  | some claim => claimWins p claim out

/-- Apply the existing computable two-layer finder to the selected data. -/
def collisionSelector (p : Primitives lambda)
    (choose : Result (List Bool) (Digest lambda) State → Option (Claim lambda tau N))
    (out : Result (List Bool) (Digest lambda) State) : Option QueryPair :=
  (choose out).bind fun claim =>
    if claimWins p claim out then
      findHashCollision (withTable p out.table) claim.leftSalt claim.rightSalt claim.left claim.right
    else none

end SDitH.Spec.BAVCBindingROM
