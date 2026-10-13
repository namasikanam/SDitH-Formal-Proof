import SDitH.Proofs.CandidatePrune
import SDitH.Proofs.ForkRestore

/-! The candidate and simulated schemes' oracles keep the family, since
each is program-shaped. -/

namespace SDitH.Proofs.CandidateKeepsFamily

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open CipherResample GameResample ChargeExpect SharedResample CandidateResample CandidatePrepLaw
open GamePrune PruneLawRun CandidatePrune ForkRestore
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The candidate scheme's honest signing keeps the family. -/
theorem honest_keepsFamily (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    KeepsFamily ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message) := by
  rw [honest_sign_shape]
  refine keepsFamily_sample _ _ fun salt => keepsFamily_sample _ _ fun root => ?_
  exact keepsFamily_run (commitBudget tau kappa) (commitProgram S.signer salt root sk.2) (honestPost S sk.1 message salt)

/-- The simulated signing keeps the family. -/
theorem simulated_keepsFamily (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    KeepsFamily ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message) := by
  rw [simulated_sign_shape]
  refine keepsFamily_sample _ _ fun salt => keepsFamily_sample _ _ fun root => keepsFamily_sample _ _ fun fake =>
    keepsFamily_sample _ _ fun digest => ?_
  exact keepsFamily_run (commitBudget tau kappa) (commitProgram S.signer salt root fake) (simPost S sk.1 message salt digest)

/-- The public oracle keeps the family. -/
theorem publicOracle_keepsFamily (query : Query lambda) :
    KeepsFamily ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query) := by
  cases query with
  | hash input => rw [publicOracle_hash_eq]; exact keepsFamily_run _ _ _
  | mask input => rw [publicOracle_mask_eq]; exact keepsFamily_run _ _ _
  | cipher request => rw [publicOracle_cipher_eq]; exact keepsFamily_run _ _ _

/-- The verification preparation keeps the family. -/
theorem prepareVerification_keepsFamily (pk message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))) :
    KeepsFamily ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification
      pk message signature) := by
  rcases signature with ⟨piop, _ | body⟩
  · rw [prepareVerification_none_eq]; exact keepsFamily_pure _
  · rw [prepareVerification_some_eq]; exact keepsFamily_run _ _ _

end
end SDitH.Proofs.CandidateKeepsFamily
