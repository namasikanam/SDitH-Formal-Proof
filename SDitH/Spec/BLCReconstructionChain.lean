import SDitH.Spec.BLCHashChain
import SDitH.Spec.BAVCReconstructionGame

/-! Reconstruction followed by the verifier's Aux/Lines chain. Computations
before and after Hashaux are explicit mixed programs, with errors retained.
Their specification/correspondence is still a caller obligation: this does not
implement Algorithm 12's missing bindings or ill-typed line 21. -/

namespace SDitH.Spec.BLCReconstructionChain

open BAVC HashCipherProgram BLCHashChain

structure Input (lambda tau N : Nat) (Key Block Context Error : Type*) where
  opening : BAVCReconstructionGame.Input lambda tau N
  auxiliaryTail : List Bool
  beforeAux : Reconstructed lambda tau N → ChainProgram lambda Key Block (Except Error Context)
  afterAux : Reconstructed lambda tau N → Context → Digest lambda → ChainProgram lambda Key Block (Except Error (List Bool))

structure Value (lambda tau N : Nat) where
  reconstruction : Reconstructed lambda tau N
  hashes : BLCHashChain.Result lambda

abbrev Outcome (lambda tau N : Nat) (Error : Type*) := Except (Sum ReconstructionError Error) (Value lambda tau N)

structure Claim (lambda tau N : Nat) (Key Block Context Error : Type*) where
  left : Input lambda tau N Key Block Context Error
  right : Input lambda tau N Key Block Context Error

structure Checked (lambda tau N : Nat) (Key Block Context Error : Type*) where
  claim : Claim lambda tau N Key Block Context Error
  left : Outcome lambda tau N Error
  right : Outcome lambda tau N Error

variable {lambda tau N : Nat} {Key Block Context Error State : Type*}

def Bounds (p m : Nat) (input : Input lambda tau N Key Block Context Error) : Prop :=
  (∀ reconstruction, Bounded p (input.beforeAux reconstruction)) ∧
    ∀ reconstruction context auxiliary, Bounded m (input.afterAux reconstruction context auxiliary)

def openProgram (layout : BAVCCipherProgram.Layout lambda Key Block) (variant : DomainSeparation.Grinding)
    (Topen : Nat) (input : Input lambda tau N Key Block Context Error) : ChainProgram lambda Key Block (Outcome lambda tau N Error) :=
  HashCipherProgram.bind (BAVCReconstructionProgram.reconstruct layout variant input.opening.salt input.opening.hidden input.opening.opening Topen input.opening.nodes) fun result =>
    match result with
    | .error cause => .done (.error (.inl cause))
    | .ok reconstruction => HashCipherProgram.bind (input.beforeAux reconstruction) fun before =>
      match before with
      | .error cause => .done (.error (.inr cause))
      | .ok context => HashCipherProgram.bind
          (partialProgram reconstruction.hcom input.auxiliaryTail (input.afterAux reconstruction context)) fun after =>
          .done (match after with
            | .error cause => .error (.inr cause)
            | .ok hashes => .ok ⟨reconstruction, hashes⟩)

def openingBudget (tau N p m : Nat) : Nat := BAVCReconstructionProgram.budget tau N + p + (m + 2)

def verifyProgram (layout : BAVCCipherProgram.Layout lambda Key Block) (variant : DomainSeparation.Grinding)
    (Topen : Nat) (claim : Claim lambda tau N Key Block Context Error) :
    ChainProgram lambda Key Block (Checked lambda tau N Key Block Context Error) :=
  HashCipherProgram.bind (openProgram layout variant Topen claim.left) fun left =>
    HashCipherProgram.bind (openProgram layout variant Topen claim.right) fun right => .done ⟨claim, left, right⟩

def verificationBudget (tau N p m : Nat) : Nat := 2 * openingBudget tau N p m

noncomputable def wins (out : HashCipher.Result (List Bool) (Digest lambda) Key Block
    (ChainProgram lambda Key Block (Checked lambda tau N Key Block Context Error))) : Bool := by
  classical
  exact match out.state with
  | .done checked => match checked.left, checked.right with
    | .ok left, .ok right => decide (left.hashes.lines = right.hashes.lines ∧
        ∃ (e : Fin tau) (i : Fin N) (leftSeed rightSeed : Seed lambda),
          left.reconstruction.seeds e i = some leftSeed ∧ right.reconstruction.seeds e i = some rightSeed ∧ leftSeed ≠ rightSeed)
    | _, _ => false
  | .hash _ _ | .cipher _ _ => false

noncomputable def experiment [Fintype Key] [Fintype Block]
    (layout : BAVCCipherProgram.Layout lambda Key Block) (variant : DomainSeparation.Grinding) (Topen p m : Nat)
    (adversary : HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N Key Block Context Error) :
    PMF (HashCipher.Result (List Bool) (Digest lambda) Key Block (ChainProgram lambda Key Block (Checked lambda tau N Key Block Context Error))) :=
  HashCipherPipeline.experiment adversary q initial procedure (verificationBudget tau N p m)
    (fun state => verifyProgram layout variant Topen (choose state))

def sourceInput (category : FieldRepresentation.Category) {tau kappa s wit rnd : Nat}
    (encoding : ConcreteBLC.Serialization tau kappa s)
    (opening : BAVCReconstructionGame.Input (FieldRepresentation.width category) tau (2 ^ kappa))
    (aux : BLCCommit.Auxiliary tau s wit rnd)
    (before : Reconstructed (FieldRepresentation.width category) tau (2 ^ kappa) →
      ChainProgram (FieldRepresentation.width category) Key Block (Except Error Context))
    (base : Reconstructed (FieldRepresentation.width category) tau (2 ^ kappa) → Context → Digest (FieldRepresentation.width category) →
      ChainProgram (FieldRepresentation.width category) Key Block (Except Error (Fin s → Fin tau → Fin kappa → ZMod 2))) :
    Input (FieldRepresentation.width category) tau (2 ^ kappa) Key Block Context Error :=
  ⟨opening, sourceTail encoding aux.corrections, before,
    fun reconstruction context => partialSourceMiddle category encoding aux.plain (base reconstruction context)⟩

end SDitH.Spec.BLCReconstructionChain
