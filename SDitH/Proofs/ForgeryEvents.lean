import SDitH.Proofs.SimulatedSolver

/-! The forgery reduction with the simulation gap taken per event. The
composed bound needs the gap only for the eight named events; stating the
hypotheses separately lets each event's gap carry its own side conditions. -/

namespace SDitH.Proofs.ForgeryEvents

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SignatureQuerySelection Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier
open Spec.PIOPArithmetic (selectorCount)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open CandidateReduction ForgeryReduction ExtractionSplit SimulatedSolver
open PIOPExtraction (extractedWitness)
open scoped Classical ENNReal
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)
  (sim : Scheme (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
    (Signature (Spec.BAVC.Digest lambda) (Option (Bod F lambda tau kappa s higherCount w widths)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
    (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))

/-- The forgery reduction with the simulation gap taken for each of the
eight events separately. -/
theorem forgery_le_simulated_events (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) (epsSim : ℝ≥0∞)
    (hgap1 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter fuel) true ≤
      (simEventExperiment adversary sim maskAfter fuel) true + epsSim)
    (hgap2 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => notSeparated V) fuel) true ≤
      (simEventExperiment adversary sim (fun _ => notSeparated V) fuel) true + epsSim)
    (hgap3 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true ≤
      (simEventExperiment adversary sim (seedCollision V) fuel) true + epsSim)
    (hgap4 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => slopeWin S V) fuel) true ≤
      (simEventExperiment adversary sim (fun _ => slopeWin S V) fuel) true + epsSim)
    (hgap5 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) fuel) true ≤
      (simEventExperiment adversary sim (fun _ => zeroChallenge V encode) fuel) true + epsSim)
    (hgap6 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (schwartzZippel S V encode) fuel) true ≤
      (simEventExperiment adversary sim (schwartzZippel S V encode) fuel) true + epsSim)
    (hgap7 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (batchingBad S V) fuel) true ≤
      (simEventExperiment adversary sim (batchingBad S V) fuel) true + epsSim)
    (hgap8 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (rsdSolved S V) fuel) true ≤
      (simEventExperiment adversary sim (rsdSolved S V) fuel) true + epsSim) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary sim maskAfter fuel) true + epsSim) +
         ((simEventExperiment adversary sim (fun _ => notSeparated V) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (seedCollision V) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (fun _ => slopeWin S V) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (fun _ => zeroChallenge V encode) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (schwartzZippel S V encode) fuel) true + epsSim) +
         (((simEventExperiment adversary sim (batchingBad S V) fuel) true + epsSim) +
          (solverSuccess S V adversary sim htau fuel + epsSim)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  refine (forgery_le_events_split S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding
    hlinesEnc hencode bound hcommit hverify hone fuel).trans (mul_le_mul_right ?_ _)
  refine add_le_add_left (add_le_add_left ?_ _) _
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hgap1 hgap2) hgap3) hgap4) hgap5) hgap6)
    (add_le_add hgap7 (hgap8.trans (add_le_add_left (solverSuccess_ge S V adversary sim htau fuel) _)))

end
end SDitH.Proofs.ForgeryEvents
