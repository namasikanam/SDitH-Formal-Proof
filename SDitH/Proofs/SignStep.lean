import SDitH.Proofs.CandidateSimulator
import SDitH.Proofs.CommitLinesEvents

/-! The per-signature sign step. The honest scheme's signing unfolds to a
uniform salt and root, the commitment run, the PIOP hash query at the
prepared payload and the opening; a hash query at an absent input binds
like a uniform digest with the table programmed, and at a present input
like the stored answer. These anchor the comparison with the simulated
signing, which draws the digest first. -/

namespace SDitH.Proofs.SignStep

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open scoped Classical ENNReal

noncomputable section

section Query

variable {Input Output B : Type*} [Fintype Output] [Nonempty Output]

/-- A hash query at an absent input binds like a uniform digest with the
table programmed at the input. -/
theorem query_bind_fresh (table : Input → Option Output) (input : Input) (h : table input = none)
    (g : Output → (Input → Option Output) → PMF B) :
    (Spec.RandomOracle.query table input).bind (fun result => g result.1 result.2) =
      (PMF.uniformOfFintype Output).bind fun digest => g digest (Function.update table input (some digest)) := by
  unfold Spec.RandomOracle.query
  rw [h, PMF.bind_map]
  rfl

/-- A hash query at a present input binds like the stored answer with the
table unchanged. -/
theorem query_bind_stored (table : Input → Option Output) (input : Input) (answer : Output)
    (h : table input = some answer) (g : Output → (Input → Option Output) → PMF B) :
    (Spec.RandomOracle.query table input).bind (fun result => g result.1 result.2) = g answer table := by
  unfold Spec.RandomOracle.query
  rw [h, PMF.pure_bind]

end Query

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The prepared payload, state and world of a commitment run's result. -/
def preparedOf (salt : Bits lambda)
    (result : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w)
        (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda)
        (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) ×
      World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    Payload F lambda higherCount ×
      SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount ×
      World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)) :=
  match result.1 with
  | Program.done committed => ((stateOf S salt committed).1, (stateOf S salt committed).2, result.2)
  | _ => ((fun _ => false, fun _ => 0), defaultState, result.2)

omit [DecidableEq F] in
/-- The honest signing preparation is the commitment run mapped by the
prepared data. -/
theorem prepareSigning_eq (publicKey : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (message : List Bool) (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    prepareSigning S publicKey witness message world =
      (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
        (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
          (runProgram (commitBudget tau kappa) (commitProgram S.signer salt root witness) world).map (preparedOf S salt) := by
  unfold prepareSigning
  congr 1
  funext salt
  congr 1
  funext root
  congr 1
  funext result
  unfold preparedOf
  rcases result with ⟨state, w⟩
  cases state <;> rfl

variable (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The honest scheme's signing: uniform salt and root, the commitment run,
the PIOP hash query at the prepared payload, and the opening. -/
theorem honest_sign_eq (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness) message
        world =
      (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
        (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
          (runProgram (commitBudget tau kappa) (commitProgram S.signer salt root witness) world.other).bind fun result =>
            (Spec.RandomOracle.query world.hashTable
              (⟨publicKey, message, (preparedOf S salt result).1⟩ : HashInput (List Bool) (List Bool) (Payload F lambda higherCount))).bind
              fun hashResult =>
                (Spec.CandidateScheme.openSigning S (preparedOf S salt result).2.1 hashResult.1 (preparedOf S salt result).2.2).map
                  fun opened => (⟨hashResult.1, opened.1⟩, ⟨hashResult.2, opened.2⟩) := by
  show (prepareSigning S publicKey witness message world.other).bind _ = _
  rw [prepareSigning_eq]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl

end
end SDitH.Proofs.SignStep
