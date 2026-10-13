import SDitH.Spec.CandidateSimulator
import SDitH.Proofs.SharedSigning

/-! Provenance of simulated signatures: every output of the simulated
signing comes from an executed commitment with a uniformly chosen fake
witness and a uniformly chosen digest; a signature with a body carries the
candidate retry's return on that digest, and the digest is then stored at
the hash input of the committed lines digest and the simulator's
coefficient tuple, an input that was absent before; a bodiless signature
leaves the hash table unchanged. The shared world of the output is the
world after the commitment program, with the family unchanged. -/

namespace SDitH.Proofs.SimulatedSign

open Spec.DomainSeparation Spec.SharedScheme Spec.SharedSigner Spec.SharedSigning Spec.CandidateScheme
open Spec.CandidateSimulator Spec.HashCipherEvaluation Spec.HashCipherProgram Spec.AbstractSignature
open Spec.PIOPArithmetic (selectorCount)
open scoped Classical
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]

theorem simulatedSign_support (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (publicKey message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (result : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (hr : result ∈ (simulatedSign S publicKey message world).support) :
    ∃ (salt root : Bits lambda) (fake : Fin (selectorCount widths * w) → ZMod 2)
      (committed : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))),
      Evaluates world.other.family result.2.other.hashTable result.2.other.cipherHistory
        (commitProgram S.signer salt root fake) committed ∧
      result.2.other.family = world.other.family ∧
      ((result.1.body = none ∧ result.2.hashTable = world.hashTable) ∨
        ∃ counter opening, Spec.BLCRetry.observe
            (Spec.CandidateScheme.attempt (stateOf S salt committed).2.key (S.expandEvaluation result.1.piop) S.encode)
            S.fuel 0 = .returned counter opening ∧
          result.1.body = some (salt, committed.result.auxiliary, (counter, opening), (stateOf S salt committed).2.higher) ∧
          let input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) :=
            ⟨publicKey, message, (committed.result.lines,
              simulatedCoefficients S salt committed (S.expandEvaluation result.1.piop counter).hidden)⟩
          world.hashTable input = none ∧
          result.2.hashTable = Function.update world.hashTable input (some result.1.piop)) := by
  obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
  obtain ⟨fake, _, hfake⟩ := (PMF.mem_support_bind_iff _ _ _).mp hroot
  obtain ⟨digest, _, hdigest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfake
  obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hdigest
  obtain ⟨committed, hstate, heval, hfam⟩ := SharedSigning.runProgram_support (commitBudget tau kappa) _
    (SharedSigner.commit_bounded S.signer salt root fake) world.other run hrun
  refine ⟨salt, root, fake, committed, ?_, ?_, ?_⟩
  · rw [← hres, hstate]
    dsimp only
    split <;> (try split) <;> exact heval
  · rw [← hres, hstate]
    dsimp only
    split <;> (try split) <;> exact hfam
  · rw [← hres, hstate]
    dsimp only
    split
    · rename_i counter opening hobs
      split
      · rename_i hnone
        right
        exact ⟨counter, opening, hobs, rfl, hnone, rfl⟩
      · left
        exact ⟨rfl, rfl⟩
    · left
      exact ⟨rfl, rfl⟩

end
end SDitH.Proofs.SimulatedSign
