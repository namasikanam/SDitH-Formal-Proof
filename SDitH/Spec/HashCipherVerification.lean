import SDitH.Spec.HashCipherPipeline
import SDitH.Spec.HashCipherProgram
import SDitH.Spec.SeedVerification
import SDitH.Spec.BAVCHashVerification

/-! The existing source seed and root checks following a mixed hash/cipher
adversary. Acceptance is computed from the returned values; completion and
query coverage are proof obligations, never additional winning conditions. -/

namespace SDitH.Spec.HashCipherVerification

open HashCipher HashCipherProgram
open scoped Classical
noncomputable section

variable {Input Digest Key Block Tag State : Type*}

abbrev SeedState (Input Digest Key Block Tag : Type*) :=
  Program Input Digest Key Block (SeedVerification.Checked Key Block Tag)

def seedWins (out : Result Input Digest Key Block (SeedState Input Digest Key Block Tag)) : Bool :=
  match out.state with
  | .done value => decide (value.claim.left ≠ value.claim.right ∧ value.left = value.right)
  | .hash _ _ | .cipher _ _ => false

variable [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]

def seedExperiment (adversary : Procedure Input Digest Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → SeedVerification.Claim Key Block) :
    PMF (Result Input Digest Key Block (SeedState Input Digest Key Block Tag)) :=
  HashCipherPipeline.experiment adversary q initial procedure 4
    (fun state => liftCipher (SeedVerification.verifyProgram project (choose state)))

/-- A direct terminal predicate of the selected state and hidden family,
without a completion, membership or freshness guard. -/
def directExperiment (adversary : Procedure Input Digest Key Block State) (q : Nat) (initial : State)
    (test : IdealCipher.Family Key Block → State → Bool) : PMF Bool :=
  (HashCipher.jointExperiment adversary q initial).map fun joint => test joint.1 joint.2.state

def directFullExperiment {lambda leaves : Nat} (variant : DomainSeparation.Grinding)
    (adversary : Procedure Input Digest (DomainSeparation.Bits lambda) (DomainSeparation.Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → SeedVerification.SourceClaim lambda leaves) : PMF Bool :=
  directExperiment adversary q initial fun family state =>
    SeedVerification.sourceWins variant (fun key input => family key input) (choose state)

def directTruncatedExperiment {leaves : Nat} (variant : DomainSeparation.Grinding)
    (adversary : Procedure Input Digest (DomainSeparation.Bits 256) (DomainSeparation.Bits 256) State)
    (q : Nat) (initial : State) (choose : State → SeedVerification.SourceClaim 192 leaves) : PMF Bool :=
  directExperiment adversary q initial fun family state =>
    SeedVerification.sourceWins variant (SeedPrimitives.encStarIII (fun key input => family key input)) (choose state)

abbrev HashState (lambda tau N : Nat) (Key Block : Type*) :=
  Program (List Bool) (BAVC.Digest lambda) Key Block (BAVCHashVerification.Checked lambda tau N)

def hashWins {lambda tau N : Nat} (out : Result (List Bool) (BAVC.Digest lambda) Key Block (HashState lambda tau N Key Block)) : Bool :=
  match out.state with
  | .done value => decide (value.leftRoot = value.rightRoot ∧
      (value.claim.leftSalt ≠ value.claim.rightSalt ∨ value.claim.left ≠ value.claim.right))
  | .hash _ _ | .cipher _ _ => false

def hashExperiment {lambda tau N : Nat}
    (adversary : Procedure (List Bool) (BAVC.Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → BAVCBindingROM.Claim lambda tau N) :
    PMF (Result (List Bool) (BAVC.Digest lambda) Key Block (HashState lambda tau N Key Block)) :=
  HashCipherPipeline.experiment adversary q initial procedure (BAVCHashVerification.verificationBudget tau)
    (fun state => liftHash (BAVCHashVerification.verifyProgram (choose state)))

end
end SDitH.Spec.HashCipherVerification
