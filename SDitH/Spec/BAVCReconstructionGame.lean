import SDitH.Spec.BAVCReconstructionProgram
import SDitH.Spec.HashCipherPipeline

/-! Execute both selected reconstructions after mixed adversarial queries.
Both error values are retained, and the second computation runs even if the
first reports an error. The event below concerns disagreement between two
successful reconstructed openings; it is not a signature acceptance predicate. -/

namespace SDitH.Spec.BAVCReconstructionGame

open BAVC BAVCReconstructionProgram HashCipherProgram

structure Input (lambda tau N : Nat) where
  salt : Seed lambda
  hidden : Fin tau → Fin N
  opening : Opening lambda tau
  nodes : NodesBinding lambda tau N

structure Claim (lambda tau N : Nat) where
  left : Input lambda tau N
  right : Input lambda tau N

structure Checked (lambda tau N : Nat) where
  claim : Claim lambda tau N
  left : Except ReconstructionError (Reconstructed lambda tau N)
  right : Except ReconstructionError (Reconstructed lambda tau N)

variable {lambda tau N : Nat} {Key Block State : Type*}

def verifyProgram (layout : BAVCCipherProgram.Layout lambda Key Block) (variant : DomainSeparation.Grinding)
    (Topen : Nat) (claim : Claim lambda tau N) : ReconstructionProgram lambda Key Block (Checked lambda tau N) :=
  HashCipherProgram.bind (BAVCReconstructionProgram.reconstruct layout variant claim.left.salt claim.left.hidden claim.left.opening Topen claim.left.nodes) fun left =>
    HashCipherProgram.bind (BAVCReconstructionProgram.reconstruct layout variant claim.right.salt claim.right.hidden claim.right.opening Topen claim.right.nodes) fun right =>
      .done ⟨claim, left, right⟩

def verificationBudget (tau N : Nat) : Nat := 2 * budget tau N

noncomputable def wins (out : HashCipher.Result (List Bool) (Digest lambda) Key Block
    (ReconstructionProgram lambda Key Block (Checked lambda tau N))) : Bool := by
  classical
  exact match out.state with
  | .done checked => match checked.left, checked.right with
    | .ok left, .ok right => decide (left.hcom = right.hcom ∧
        ∃ (e : Fin tau) (i : Fin N) (leftSeed rightSeed : Seed lambda),
          left.seeds e i = some leftSeed ∧ right.seeds e i = some rightSeed ∧ leftSeed ≠ rightSeed)
    | _, _ => false
  | .hash _ _ | .cipher _ _ => false

noncomputable def experiment [Fintype Key] [Fintype Block]
    (layout : BAVCCipherProgram.Layout lambda Key Block) (variant : DomainSeparation.Grinding) (Topen : Nat)
    (adversary : HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N) :
    PMF (HashCipher.Result (List Bool) (Digest lambda) Key Block (ReconstructionProgram lambda Key Block (Checked lambda tau N))) :=
  HashCipherPipeline.experiment adversary q initial procedure (verificationBudget tau N)
    (fun state => verifyProgram layout variant Topen (choose state))

end SDitH.Spec.BAVCReconstructionGame
