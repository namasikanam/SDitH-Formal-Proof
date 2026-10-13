import SDitH.Spec.BAVCBindingROM
import SDitH.Spec.OracleProgram
import SDitH.Spec.RandomOraclePipeline

/-! Execute both source two-layer Hashbavc computations after an adaptive
adversary chooses salt/leaf-commitment data. All row queries are made in index
order before the corresponding outer query. Both computations use the same
oracle as the adversary; missing entries are queried, never rejected by a
coverage guard. This is the hash part of binding, not seed/tree/BLC binding. -/

namespace SDitH.Spec.BAVCHashVerification

open BAVC BAVCBinding BAVCBindingROM OracleProgram RandomOracleCollision

variable {lambda tau N : Nat} {State : Type*}

def rootProgram (salt : Seed lambda) (commits : Commitments lambda tau N) :
    Program (List Bool) (Digest lambda) (Digest lambda) :=
  OracleProgram.bind (OracleProgram.array tau (rowQuery commits)) fun rows =>
    .query (byteBits 1 ++ (List.ofFn salt ++ serializeArray rows)) (fun root => .done root)

structure Checked (lambda tau N : Nat) where
  claim : Claim lambda tau N
  leftRoot : Digest lambda
  rightRoot : Digest lambda

def verifyProgram (claim : Claim lambda tau N) : Program (List Bool) (Digest lambda) (Checked lambda tau N) :=
  OracleProgram.bind (rootProgram claim.leftSalt claim.left) fun leftRoot =>
    OracleProgram.bind (rootProgram claim.rightSalt claim.right) fun rightRoot =>
      .done ⟨claim, leftRoot, rightRoot⟩

abbrev VerificationState (lambda tau N : Nat) := Program (List Bool) (Digest lambda) (Checked lambda tau N)

/-- The verification budget includes both complete row/outer computations,
also when inputs repeat or were already queried in the adversarial phase. -/
def verificationBudget (tau : Nat) : Nat := 2 * (tau + 1)

noncomputable def experiment (adversary : Procedure (List Bool) (Digest lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N) :
    PMF (Result (List Bool) (Digest lambda) (VerificationState lambda tau N)) :=
  RandomOraclePipeline.experiment adversary q initial OracleProgram.procedure (verificationBudget tau)
    (fun state => verifyProgram (choose state))

/-- Equal computed roots for different salt/commitment data. There is no
already-queried condition in this event. Program completion is proved. -/
def wins (out : Result (List Bool) (Digest lambda) (VerificationState lambda tau N)) : Bool :=
  match out.state with
  | .query _ _ => false
  | .done checked => decide (checked.leftRoot = checked.rightRoot ∧
      (checked.claim.leftSalt ≠ checked.claim.rightSalt ∨ checked.claim.left ≠ checked.claim.right))

end SDitH.Spec.BAVCHashVerification
