import SDitH.Spec.CandidateSimulator
import SDitH.Proofs.SimulatedSolver

/-! The simulated scheme reads only the public half of the signing key, and
the forgery bound instantiated at it: the solver on the simulated scheme is
witness-free, and the bound carries the per-event simulation gap as an
explicit hypothesis to be discharged. -/

namespace SDitH.Proofs.CandidateSimulator

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier Spec.CandidateSimulator
open Spec.PIOPArithmetic (selectorCount)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open CandidateReduction ForgeryReduction ExtractionSplit SimulatedSolver
open scoped Classical ENNReal
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- Simulated signing never reads the witness half of the signing key. -/
theorem sign_witness_free (pk : List Bool) (witness witness' : Fin (selectorCount widths * w) → ZMod 2) :
    (simulatedScheme S V verifyBudget publicKey sampleWitness).sign (pk, witness) =
      (simulatedScheme S V verifyBudget publicKey sampleWitness).sign (pk, witness') := rfl

/-- The simulated scheme's key generation, verification, digest and public
oracle are the candidate scheme's. -/
theorem simulated_components :
    (simulatedScheme S V verifyBudget publicKey sampleWitness).keygen =
        (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).keygen ∧
      (simulatedScheme S V verifyBudget publicKey sampleWitness).prepareVerification =
        (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification ∧
      (simulatedScheme S V verifyBudget publicKey sampleWitness).signatureDigest =
        (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).signatureDigest ∧
      (simulatedScheme S V verifyBudget publicKey sampleWitness).publicOracle =
        (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle :=
  ⟨rfl, rfl, rfl, rfl⟩

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The forgery bound against the candidate scheme in terms of the simulated
scheme's events and the witness-free solver's success, under the per-event
simulation gap. -/
theorem forgery_le_simulator (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
    (hgap : ∀ E, (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true + epsSim) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true +
            epsSim) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => notSeparated V)
            fuel) true + epsSim) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (seedCollision V) fuel)
            true + epsSim) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => slopeWin S V)
            fuel) true + epsSim) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (fun _ => zeroChallenge V encode) fuel) true + epsSim) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (schwartzZippel S V encode) fuel) true + epsSim) +
         (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (batchingBad S V) fuel)
            true + epsSim) +
          (solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel + epsSim)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_simulated S V verifyBudget publicKey sampleWitness adversary
    (simulatedScheme S V verifyBudget publicKey sampleWitness) hlambda htau encode hmid hencoding hlinesEnc hencode bound
    hcommit hverify hone fuel epsSim hgap

end
end SDitH.Proofs.CandidateSimulator
