import SDitH.Proofs.CandidateResample

/-! The candidate scheme's verification preparation obeys the resampling
law. A signature without a body is rejected without touching the world;
one with a body runs the verification program on the inner world and
post-processes its answer purely from the outer hash table, so the law
holds by the generic run shape. -/

namespace SDitH.Proofs.CandidatePrepLaw

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open CipherResample GameResample ChargeExpect SharedResample CandidateResample
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The verification answer from an executed verification program. -/
def verifyAnswer (pk message : List Bool) (piop : Digest lambda)
    (body : Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
    (a : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
      (Bits lambda) (Bits lambda) (Except (Sum ReconstructionError Spec.BLCRecompute.Error)
        (Spec.SignatureComposition.Recomputed F lambda (selectorCount widths * w) (lambda * (widths.length - 1))))) :
    Option (Payload F lambda higherCount) :=
  match a with
  | Program.done (Except.ok recovered) =>
      let input := Spec.SignatureComposition.verificationInput widths S.hdegree S.hsize S.signer.xi S.expandBatching S.H'
        S.y pk message
        ⟨body.1, piop, body.2.1, (body.2.2.1.1, ⟨[], fun e => body.2.2.1.2.hiddenCommitments e⟩), body.2.2.2⟩
        recovered
      some (input.lines, input.coefficients)
  | _ => none

/-- The verification preparation obeys the resampling law. -/
theorem prepareVerification_postLaw (pk message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))) :
    PostLaw resample
      ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification pk message
        signature) := by
  rcases signature with ⟨piop, _ | body⟩
  · intro world
    simp only [scheme, Spec.CandidateScheme.components, Spec.CandidateScheme.prepareVerification,
      PMF.pure_bind, PMF.map, Function.comp_def]
    exact (resampleW_bind resample resample_idem world _).symm
  · have h := postLaw_run (HashInput := HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Digest := Digest lambda) verifyBudget (verifyProgram V body.1 body.2.1 piop body.2.2.1)
      (fun a table => PMF.pure ((verifyAnswer S pk message piop body a).map
        (fun payload => (⟨pk, message, payload⟩ : HashInput (List Bool) (List Bool) (Payload F lambda higherCount))), table))
    convert h using 2
    simp only [scheme, Spec.CandidateScheme.components, Spec.CandidateScheme.prepareVerification, PMF.bind_bind,
      PMF.pure_bind, Function.comp_def, PMF.map]
    congr 1
    funext r
    rcases r with ⟨a, o⟩
    cases a with
    | done e => cases e <;> rfl
    | hash _ _ => rfl
    | cipher _ _ => rfl

end
end SDitH.Proofs.CandidatePrepLaw
