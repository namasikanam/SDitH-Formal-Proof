import SDitH.Proofs.CandidatePrune

/-! The game-level pruned-run agreement for the candidate and simulated
schemes: both schemes' oracles obey the resampling laws, the prune laws,
grow and keep consistency, so the game run from the resampled world is
below the run from the resampled pruned world plus the final touching
indicator. -/

namespace SDitH.Proofs.CandidateGamePrune

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.RandomOracleTrap (indicator)
open CipherResample GameResample ChargeExpect CandidateResample CandidatePrepLaw GamePrune PruneLawRun CandidatePrune
open RunWorld
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)
  (K : List (Bits lambda))

/-- The candidate scheme's game run agrees with its pruned run. -/
theorem candidate_runW_le_prune
    (Φ : Terminal (List Bool)
        (Signature (Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) ×
      GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1)) → ℝ≥0∞)
    (hΦ : FamilyFreeT Φ) (hle : ∀ r, Φ r ≤ 1) (fuel : Nat) (pk : List Bool)
    (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (state : State)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
    (hcons : Consistent world) :
    mean (resampleW resample world) (fun w' =>
      mean (runW (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel pk sk
        state w' trace) fun r => Φ (withWorld r.1 (pruneW K r.2), pruneW K r.2)) ≤
    mean (resampleW resample (pruneW K world)) (fun w' =>
      mean (runW (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel pk sk
        state w' trace) fun r => Φ r + indicator (touchesG K r.2)) :=
  runW_le_prune K _ adversary (honest_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (honest_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (publicOracle_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (prepareVerification_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (honest_grows S V verifyBudget publicKey sampleWitness)
    (publicOracle_grows S V verifyBudget publicKey sampleWitness)
    (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
    (honest_keeps S V verifyBudget publicKey sampleWitness)
    (publicOracle_keeps S V verifyBudget publicKey sampleWitness) Φ hΦ hle fuel pk sk state world trace hcons

/-- The simulated scheme's game run agrees with its pruned run. -/
theorem simulated_runW_le_prune
    (Φ : Terminal (List Bool)
        (Signature (Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) ×
      GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1)) → ℝ≥0∞)
    (hΦ : FamilyFreeT Φ) (hle : ∀ r, Φ r ≤ 1) (fuel : Nat) (pk : List Bool)
    (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (state : State)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
    (hcons : Consistent world) :
    mean (resampleW resample world) (fun w' =>
      mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel pk sk state w' trace) fun r =>
        Φ (withWorld r.1 (pruneW K r.2), pruneW K r.2)) ≤
    mean (resampleW resample (pruneW K world)) (fun w' =>
      mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel pk sk state w' trace) fun r =>
        Φ r + indicator (touchesG K r.2)) :=
  runW_le_prune K _ adversary (simulated_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (simulated_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (publicOracle_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (prepareVerification_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (simulated_grows S V verifyBudget publicKey sampleWitness)
    (publicOracle_grows S V verifyBudget publicKey sampleWitness)
    (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
    (simulated_keeps S V verifyBudget publicKey sampleWitness)
    (publicOracle_keeps S V verifyBudget publicKey sampleWitness) Φ hΦ hle fuel pk sk state world trace hcons

end
end SDitH.Proofs.CandidateGamePrune
