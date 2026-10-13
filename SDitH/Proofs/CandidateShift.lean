import SDitH.Proofs.CandidatePrune
import SDitH.Proofs.HistoryShiftGame

/-! The candidate and simulated schemes' oracles obey the shift law, since
each is program-shaped, so both schemes' game runs with their final worlds
shift with the inner history. -/

namespace SDitH.Proofs.CandidateShift

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open CipherResample GameResample ChargeExpect SharedResample CandidateResample CandidatePrepLaw
open GamePrune PruneLawRun CandidatePrune HistoryShiftGame RunWorld
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The candidate scheme's honest signing obeys the shift law. -/
theorem honest_shiftLaw (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    ShiftLaw ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message) := by
  rw [honest_sign_shape]
  refine shiftLaw_sample _ _ fun salt => shiftLaw_sample _ _ fun root => ?_
  exact shiftLaw_run (commitBudget tau kappa) (commitProgram S.signer salt root sk.2) (honestPost S sk.1 message salt)

/-- The simulated signing obeys the shift law. -/
theorem simulated_shiftLaw (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    ShiftLaw ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message) := by
  rw [simulated_sign_shape]
  refine shiftLaw_sample _ _ fun salt => shiftLaw_sample _ _ fun root => shiftLaw_sample _ _ fun fake =>
    shiftLaw_sample _ _ fun digest => ?_
  exact shiftLaw_run (commitBudget tau kappa) (commitProgram S.signer salt root fake) (simPost S sk.1 message salt digest)

/-- The public oracle obeys the shift law. -/
theorem publicOracle_shiftLaw (query : Query lambda) :
    ShiftLaw ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query) := by
  cases query with
  | hash input => rw [publicOracle_hash_eq]; exact shiftLaw_run _ _ _
  | mask input => rw [publicOracle_mask_eq]; exact shiftLaw_run _ _ _
  | cipher request => rw [publicOracle_cipher_eq]; exact shiftLaw_run _ _ _

/-- The verification preparation obeys the shift law. -/
theorem prepareVerification_shiftLaw (pk message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))) :
    ShiftLaw ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification
      pk message signature) := by
  rcases signature with ⟨piop, _ | body⟩
  · rw [prepareVerification_none_eq]; exact shiftLaw_pure _
  · rw [prepareVerification_some_eq]; exact shiftLaw_run _ _ _

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The candidate scheme's game run shifts with the inner history. -/
theorem candidate_runW_shift (fuel : Nat) (pk : List Bool) (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2))
    (state : State) (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda)) :
    runW (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel pk sk state
        (shiftG H world) trace =
      (runW (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel pk sk state
        world trace).map fun r => (shiftT H r.1, shiftG H r.2) :=
  runW_shift _ adversary (honest_shiftLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_shiftLaw S V verifyBudget publicKey sampleWitness)
    (prepareVerification_shiftLaw S V verifyBudget publicKey sampleWitness) fuel pk sk state H world trace

/-- The simulated scheme's game run shifts with the inner history. -/
theorem simulated_runW_shift (fuel : Nat) (pk : List Bool) (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2))
    (state : State) (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda)) :
    runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel pk sk state (shiftG H world) trace =
      (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel pk sk state world trace).map fun r =>
        (shiftT H r.1, shiftG H r.2) :=
  runW_shift _ adversary (simulated_shiftLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_shiftLaw S V verifyBudget publicKey sampleWitness)
    (prepareVerification_shiftLaw S V verifyBudget publicKey sampleWitness) fuel pk sk state H world trace

end
end SDitH.Proofs.CandidateShift
