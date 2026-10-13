import SDitH.Spec.SharedSlopeGame
import SDitH.Spec.HashCipherTracePipeline
import SDitH.Spec.HashCipherProgram

/-! The slope-consistency game with the named claim's commitment calls
executed as a second phase. The adversary's selected claim becomes the
return value of a cipher program making both CommitSeed calls of every
leaf seed; the final state carries the claim, so the queried condition of
the one-phase game is derived from execution rather than required. -/

namespace SDitH.Spec.SharedSlopeExec

open BAVC DomainSeparation BAVCChainInputs SlopeConsistency SharedSlopeGame SeedPairing HashCipherProgram ConsistencyMatrix
open Spec.SlopeConsistencyGame (Out)
open scoped Classical
noncomputable section

variable {lambda tau kappa s wit rnd : Nat} {State : Type*}

abbrev ClaimProgram (lambda tau kappa s wit rnd : Nat) :=
  Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Claim lambda tau kappa s wit rnd)

def allPairs (tau kappa : Nat) : List (Fin tau × Fin (2 ^ kappa)) :=
  (List.finRange tau).flatMap fun e => (List.finRange (2 ^ kappa)).map fun i => (e, i)

/-- Both commitment calls of each listed leaf, then the claim as value. -/
def callsProgram (S : Setting lambda tau kappa s wit rnd) (c : Claim lambda tau kappa s wit rnd) :
    List (Fin tau × Fin (2 ^ kappa)) → ClaimProgram lambda tau kappa s wit rnd
  | [] => .done c
  | (e, i) :: rest => .cipher (.encrypt (c.full e i) (input0 S.variant c.salt e i)) fun _ =>
      .cipher (.encrypt (c.full e i) (companion (input0 S.variant c.salt e i))) fun _ => callsProgram S c rest

def commitProgram (S : Setting lambda tau kappa s wit rnd) (c : Claim lambda tau kappa s wit rnd) :
    ClaimProgram lambda tau kappa s wit rnd :=
  callsProgram S c (allPairs tau kappa)

def commitBudget (tau kappa : Nat) : Nat := 2 * (allPairs tau kappa).length

def claimOf : ClaimProgram lambda tau kappa s wit rnd → Option (Claim lambda tau kappa s wit rnd)
  | .done c => some c
  | _ => none

def defaultClaim : Claim lambda tau kappa s wit rnd :=
  ⟨fun _ => false, fun _ _ _ => false, fun _ _ => false, fun _ => false, fun _ => false, ⟨fun _ _ => 0, fun _ => 0, fun _ => 0⟩⟩

/-- The claim read from the final program state. -/
def claimAt (state : ClaimProgram lambda tau kappa s wit rnd) : Claim lambda tau kappa s wit rnd :=
  (claimOf state).getD defaultClaim

abbrev ExecRes (lambda tau kappa s wit rnd : Nat) :=
  HashCipherTrace.Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (ClaimProgram lambda tau kappa s wit rnd)

/-- Adversary phase, then the commitment calls of its selected claim. -/
def jointExperiment (S : Setting lambda tau kappa s wit rnd)
    (adversary : HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd) :
    PMF (CipherFamily lambda × ExecRes lambda tau kappa s wit rnd) :=
  HashCipherTracePipeline.jointExperiment adversary q initial procedure (commitBudget tau kappa)
    (fun state => commitProgram S (choose state))

/-- Winning without any queried condition: the claim in the final state is
chained, its mask is stored and two slopes differ with equal masked images. -/
def winsExec (S : Setting lambda tau kappa s wit rnd) (joint : CipherFamily lambda × ExecRes lambda tau kappa s wit rnd) : Bool :=
  match claimOf joint.2.state with
  | none => false
  | some c => decide (ChainIn' S joint.1 joint.2.hashTable c ∧
      ∃ pair, joint.2.hashTable (maskInput c.auxiliary) = some pair ∧
        ∃ e e', slopeOf S c e ≠ slopeOf S c e' ∧
          ∀ a, masked pair.2 (slopeOf S c e) a = masked pair.2 (slopeOf S c e') a)

end
end SDitH.Spec.SharedSlopeExec
