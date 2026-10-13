import SDitH.Proofs.CandidateGamePrune
import SDitH.Proofs.GamePruneReverse

/-! The reverse game-level pruned-run agreement for the candidate and
simulated schemes: the game run from the resampled pruned world is below
the run from the resampled world on the pruned result plus the touching
indicator under the pruned run. -/

namespace SDitH.Proofs.CandidateGamePruneReverse

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.RandomOracleTrap (indicator)
open CipherResample GameResample ChargeExpect CandidateResample CandidatePrepLaw GamePrune PruneLawRun CandidatePrune
open RunWorld GamePruneReverse
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

/-- The candidate scheme's pruned run is below its game run on the pruned
result plus the touching indicator. -/
theorem candidate_prune_le_runW
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
    mean (resampleW resample (pruneW K world)) (fun w' =>
      mean (runW (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel pk sk
        state w' trace) Φ) ≤
    mean (resampleW resample world) (fun w' =>
      mean (runW (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel pk sk
        state w' trace) fun r => Φ (withWorld r.1 (pruneW K r.2), pruneW K r.2)) +
    mean (resampleW resample (pruneW K world)) (fun w' =>
      mean (runW (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel pk sk
        state w' trace) fun r => indicator (touchesG K r.2)) :=
  prune_le_runW K _ adversary (honest_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (honest_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (publicOracle_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (prepareVerification_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (honest_grows S V verifyBudget publicKey sampleWitness)
    (publicOracle_grows S V verifyBudget publicKey sampleWitness)
    (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
    (honest_keeps S V verifyBudget publicKey sampleWitness)
    (publicOracle_keeps S V verifyBudget publicKey sampleWitness) Φ hΦ hle fuel pk sk state world trace hcons

/-- The simulated scheme's pruned run is below its game run on the pruned
result plus the touching indicator. -/
theorem simulated_prune_le_runW
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
    mean (resampleW resample (pruneW K world)) (fun w' =>
      mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel pk sk state w' trace) Φ) ≤
    mean (resampleW resample world) (fun w' =>
      mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel pk sk state w' trace) fun r =>
        Φ (withWorld r.1 (pruneW K r.2), pruneW K r.2)) +
    mean (resampleW resample (pruneW K world)) (fun w' =>
      mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel pk sk state w' trace) fun r =>
        indicator (touchesG K r.2)) :=
  prune_le_runW K _ adversary (simulated_postLaw S V verifyBudget publicKey sampleWitness)
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
end SDitH.Proofs.CandidateGamePruneReverse
