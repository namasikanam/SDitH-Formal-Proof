import SDitH.Proofs.SignCompare

/-! The simulated signing at a given witness. The simulated signing draws
its fake witness uniformly; with the witness fixed it is the simulated
signing at that witness, so the simulated signing is the uniform mixture
of the fixed-witness forms. The payload consistency of the honest signer
(its hashed coefficients equal the simulator's recomputed tuple at every
admissible hidden vector, for a solution witness) is the named explicit
hypothesis that the comparison with the digest-first honest signing
uses. -/

namespace SDitH.Proofs.SimulatedWith

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.HashCipherEvaluation Spec.SlopeConsistencyGame
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The simulated signing at a given witness: uniform salt, root and digest,
the commitment run, the candidate retry on the digest, the recomputed
tuple, and the programmed answer. -/
def simulatedSignWith (publicKey : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    PMF (Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :=
  (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
    (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
      (PMF.uniformOfFintype (Digest lambda)).bind fun digest =>
        (runProgram (commitBudget tau kappa) (commitProgram S.signer salt root witness) world.other).map fun result =>
          match result.1 with
          | Program.done committed =>
            let state := (stateOf S salt committed).2
            match Spec.BLCRetry.observe (attempt state.key (S.expandEvaluation digest) S.encode) S.fuel 0 with
            | .returned ctr opening =>
              let hidden := (S.expandEvaluation digest ctr).hidden
              let input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) :=
                ⟨publicKey, message, (committed.result.lines, simulatedCoefficients S salt committed hidden)⟩
              match world.hashTable input with
              | none => (⟨digest, some (salt, committed.result.auxiliary, (ctr, opening), state.higher)⟩,
                  ⟨Function.update world.hashTable input (some digest), result.2⟩)
              | some _ => (⟨digest, none⟩, ⟨world.hashTable, result.2⟩)
            | _ => (⟨digest, none⟩, ⟨world.hashTable, result.2⟩)
          | _ => (⟨digest, none⟩, ⟨world.hashTable, result.2⟩)

/-- The simulated signing is the uniform mixture over the fake witness of the
fixed-witness forms. -/
theorem simulatedSign_eq_with (publicKey message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    simulatedSign S publicKey message world =
      (PMF.uniformOfFintype (Fin (selectorCount widths * w) → ZMod 2)).bind fun fake =>
        simulatedSignWith S publicKey fake message world := by
  unfold simulatedSign simulatedSignWith
  conv_lhs => arg 2; ext salt; rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  congr 1

/-- Payload consistency of the honest signer: for a solution witness, the
hashed coefficients of an executed commitment equal the simulator's
recomputed tuple at every hidden vector with nonzero encoding. -/
def PayloadConsistent : Prop :=
  ∀ (salt root : Bits lambda) (witness : Fin (selectorCount widths * w) → ZMod 2),
    IsSolution S witness →
    ∀ (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
      (table : List Bool → Option (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
      (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
      (committed : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))),
      Evaluates family table ciphers (commitProgram S.signer salt root witness) committed →
      ∀ hidden : Fin tau → Fin (2 ^ kappa), S.encode hidden ≠ 0 →
        (stateOf S salt committed).1.2 = simulatedCoefficients S salt committed hidden

end
end SDitH.Proofs.SimulatedWith
