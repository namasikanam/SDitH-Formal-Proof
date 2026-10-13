import SDitH.Spec.SharedSigner

/-! A named candidate target for Algorithms 8–9, chosen by the user on
2026-10-09 as the simplest corrected opening and reconstruction. The
opening carries every revealed leaf seed and the hidden commitments
directly, without the literal sibling-path compression; the
reconstruction recomputes each revealed leaf's commitment by the cipher,
takes the transmitted commitment at the hidden index, and hashes the rows
and the salted outer string exactly as Algorithm 7 does. The literal
Algorithms 8–9 and their recorded defects are untouched. -/

namespace SDitH.Spec.CandidateBAVC

open BAVC DomainSeparation HashCipherProgram SeedPrimitives SharedSigner
open Spec.SlopeConsistencyGame (Out)
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The candidate opening: revealed seeds (absent at the hidden index) and
the hidden commitments. -/
structure Opening (lambda tau N : Nat) where
  revealed : Fin tau → Fin N → Option (Seed lambda)
  hiddenCommitments : Fin tau → Digest lambda

/-- The candidate opening of a key at hidden indices. -/
def openKey {N : Nat} (key : Key lambda tau N) (hidden : Fin tau → Fin N) : Opening lambda tau N :=
  ⟨fun e i => if i = hidden e then none else some (key.tree (leafNode e i)),
    fun e => key.commitments e (hidden e)⟩

/-- One leaf's commitment: transmitted at the hidden index, recomputed by
the cipher from the revealed seed otherwise; absent if the seed is missing. -/
def leafCommit (layout : BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa))
    (pair : Fin tau × Fin (2 ^ kappa)) : SignerProgram lambda s wit rnd (Option (Digest lambda)) :=
  if pair.2 = hidden pair.1 then Program.done (some (opening.hiddenCommitments pair.1))
  else match opening.revealed pair.1 pair.2 with
    | none => Program.done none
    | some seed => bind (commitCall layout (tau * 2 ^ kappa) variant salt seed (SeedTree.leafOffset pair.1 pair.2))
        fun commitment => Program.done (some commitment)

/-- The commitments as a function, defaulting absent entries. -/
def commitsOf (commits : Fin tau × Fin (2 ^ kappa) → Option (Digest lambda)) : BAVCBinding.Commitments lambda tau (2 ^ kappa) :=
  fun e i => (commits (e, i)).getD (fun _ => false)

/-- The candidate reconstruction: every leaf commitment, then the row hashes
in execution order and the salted outer hash. A missing revealed seed is an
explicit error. -/
def reconstruct (layout : BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (opening : Opening lambda tau (2 ^ kappa)) :
    SignerProgram lambda s wit rnd (Except ReconstructionError (Reconstructed lambda tau (2 ^ kappa))) :=
  bind (collect (leafCommit layout variant salt hidden opening) (SharedSlopeExec.allPairs tau kappa) fun _ => none)
    fun commits =>
      if ∀ pair, (commits pair).isSome then
        bind (collect (fun e => hashCall (BAVCBinding.rowQuery (commitsOf commits) e)) (List.finRange tau)
            fun _ => fun _ => false) fun rowHashes =>
          Program.hash (BAVCChainInputs.outerString salt rowHashes) fun outer =>
            Program.done (Except.ok ⟨outer.1, opening.revealed⟩)
      else Program.done (Except.error ReconstructionError.undefinedNodeRead)

def budget (tau kappa : Nat) : Nat := 2 * (SharedSlopeExec.allPairs tau kappa).length + tau + 1

end
end SDitH.Spec.CandidateBAVC
