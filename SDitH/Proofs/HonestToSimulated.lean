import SDitH.Proofs.DigestFirstVsSimulated

/-! The honest signing against the simulated signing. Chaining the
input-present step and the retry-failure step, the honest signing is
within those two events of the simulated signing at the honest witness.
With the witness swap of the fixed-witness simulated signing carried as
an explicit term, the honest signing is within the two events plus the
swap term of the simulated scheme's signing. -/

namespace SDitH.Proofs.HonestToSimulated

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open SignStep SignCompare SimulatedWith DigestFirstBody DigestFirstVsSimulated
open scoped Classical ENNReal

noncomputable section

section Generic

variable {A B : Type*}

/-- A distribution within a constant of every continuation is within that
constant of their mixture. -/
theorem le_bind_add_const (p : PMF A) (q : PMF B) (g : A → PMF B) (c : ℝ≥0∞) (b : B)
    (h : ∀ a ∈ p.support, q b ≤ g a b + c) : q b ≤ (p.bind g) b + c := by
  calc q b = ∑' a, p a * q b := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ ∑' a, p a * (g a b + c) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ p.support
        · exact mul_le_mul_right (h a ha) _
        · rw [PMF.mem_support_iff, not_not] at ha
          rw [ha]
          simp
    _ = (p.bind g) b + c := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, PMF.bind_apply]

end Generic

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The honest signing is within the input-present and retry-failure events
of the simulated signing at the honest witness. -/
theorem honest_le_simulatedWith (hpc : PayloadConsistent S) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (hsol : IsSolution S witness) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (b : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness) message
        world) b ≤
      (simulatedSignWith S publicKey witness message world) b +
        ((inputPresent S publicKey witness message world) true + (retryEvent S publicKey witness message world) true) := by
  calc _ ≤ (digestFirstSign S publicKey witness message world) b + (inputPresent S publicKey witness message world) true :=
        honest_le_digestFirst S V verifyBudget publicKey sampleWitness witness message world b
    _ ≤ ((simulatedSignWith S publicKey witness message world) b + (retryEvent S publicKey witness message world) true) +
          (inputPresent S publicKey witness message world) true :=
        add_le_add_left (digestFirst_le_simulatedWith S hpc publicKey witness hsol message world b) _
    _ = _ := by ring

/-- With the witness swap of the fixed-witness simulated signing as an
explicit term, the honest signing is within the two events plus the swap
term of the simulated scheme's signing. -/
theorem honest_le_simulated (hpc : PayloadConsistent S) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (hsol : IsSolution S witness) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (epsSwap : ℝ≥0∞)
    (hswap : ∀ (fake : Fin (selectorCount widths * w) → ZMod 2) (b : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      (simulatedSignWith S publicKey witness message world) b ≤ (simulatedSignWith S publicKey fake message world) b + epsSwap)
    (b : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness) message
        world) b ≤
      ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign (publicKey, witness) message world) b +
        ((inputPresent S publicKey witness message world) true + (retryEvent S publicKey witness message world) true +
          epsSwap) := by
  have hsim : (simulatedScheme S V verifyBudget publicKey sampleWitness).sign (publicKey, witness) message world =
      simulatedSign S publicKey message world := rfl
  rw [hsim, simulatedSign_eq_with]
  calc _ ≤ (simulatedSignWith S publicKey witness message world) b +
        ((inputPresent S publicKey witness message world) true + (retryEvent S publicKey witness message world) true) :=
        honest_le_simulatedWith S V verifyBudget publicKey sampleWitness hpc witness hsol message world b
    _ ≤ (((PMF.uniformOfFintype (Fin (selectorCount widths * w) → ZMod 2)).bind fun fake =>
          simulatedSignWith S publicKey fake message world) b + epsSwap) +
        ((inputPresent S publicKey witness message world) true + (retryEvent S publicKey witness message world) true) :=
        add_le_add_left (le_bind_add_const _ _ _ epsSwap b (fun fake _ => hswap fake b)) _
    _ = _ := by ring

end
end SDitH.Proofs.HonestToSimulated
