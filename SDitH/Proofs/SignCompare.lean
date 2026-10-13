import SDitH.Proofs.SignStep

/-! The honest signing against its digest-first form. The digest-first
honest signing draws the PIOP digest uniformly after the preparation and
programs it at the hash input when the input is absent, giving no body
when it is present (as the simulated signing does). At an absent input the
two coincide, so the honest signing is within the input-present event's
probability of its digest-first form. -/

namespace SDitH.Proofs.SignCompare

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open SignStep CommitLinesEvent
open scoped Classical ENNReal

noncomputable section

section Query

variable {Input Output B : Type*} [Fintype Output] [Nonempty Output]

/-- A hash query at an absent input binds like a uniform digest with the
table programmed at the input (first-order form). -/
theorem query_bind_fresh' (table : Input → Option Output) (input : Input) (h : table input = none)
    (g : Output × (Input → Option Output) → PMF B) :
    (Spec.RandomOracle.query table input).bind g =
      (PMF.uniformOfFintype Output).bind fun digest => g (digest, Function.update table input (some digest)) := by
  unfold Spec.RandomOracle.query
  rw [h, PMF.bind_map]
  rfl

end Query

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The digest-first honest signing: the honest preparation, a uniform
digest programmed at the hash input when absent, and the opening; no body
when the input is present. -/
def digestFirstSign (publicKey : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    PMF (Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :=
  (prepareSigning S publicKey witness message world.other).bind fun prepared =>
    (PMF.uniformOfFintype (Digest lambda)).bind fun digest =>
      match world.hashTable ⟨publicKey, message, prepared.1⟩ with
      | none => (Spec.CandidateScheme.openSigning S prepared.2.1 digest prepared.2.2).map fun opened =>
          (⟨digest, opened.1⟩, ⟨Function.update world.hashTable ⟨publicKey, message, prepared.1⟩ (some digest), opened.2⟩)
      | some _ => (Spec.CandidateScheme.openSigning S prepared.2.1 digest prepared.2.2).map fun opened =>
          (⟨digest, none⟩, ⟨world.hashTable, opened.2⟩)

/-- The input-present event: the honest preparation's hash input is already
in the table. -/
def inputPresent (publicKey : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : PMF Bool :=
  (prepareSigning S publicKey witness message world.other).map fun prepared =>
    decide (world.hashTable ⟨publicKey, message, prepared.1⟩ ≠ none)

variable (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The honest signing is within the input-present event's probability of
its digest-first form. -/
theorem honest_le_digestFirst (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (b : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness) message
        world) b ≤
      (digestFirstSign S publicKey witness message world) b + (inputPresent S publicKey witness message world) true := by
  show ((prepareSigning S publicKey witness message world.other).bind _) b ≤ _
  unfold digestFirstSign inputPresent
  refine bind_le_bind_add_event _ _ _ _ (fun prepared _ hb => ?_) b
  have h : world.hashTable ⟨publicKey, message, prepared.1⟩ = none := by
    simpa using hb
  rw [h, query_bind_fresh' world.hashTable _ h]
  rfl

end
end SDitH.Proofs.SignCompare
