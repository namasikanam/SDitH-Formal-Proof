import SDitH.Proofs.SimulatedWith
import SDitH.Proofs.BLCRetry

/-! The bodies of the digest-first and simulated signing at a returned
retry. A ready candidate attempt certifies the grinding check, a nonzero
encoding of the hidden vector and the candidate opening; a returned
observation certifies these at its counter. Under payload consistency,
for a solution witness and an executed commitment, the honest prepared
payload equals the simulator's payload at the returned counter's hidden
vector, so the two hash inputs coincide. The retry-failure event (no
returned observation at the digest) is named. -/

namespace SDitH.Proofs.DigestFirstBody

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.HashCipherEvaluation Spec.SlopeConsistencyGame Spec.BLCRetry Spec.CandidateBAVC
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open SimulatedWith
open scoped Classical ENNReal

noncomputable section

section Attempt

variable {F : Type*} [Field F] [DecidableEq F] {lambda tau kappa wpow : Nat}

/-- A ready candidate attempt certifies the grinding check, a nonzero
encoding and the candidate opening at the hidden vector. -/
theorem attempt_ready (key : Key lambda tau (2 ^ kappa)) (expand : Counter → Challenge tau (2 ^ kappa) wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (ctr : Counter) (opening : Opening lambda tau (2 ^ kappa))
    (h : Spec.CandidateScheme.attempt key expand encode ctr = Attempt.ready opening) :
    GrindingPassed (expand ctr).grinding ∧ encode (expand ctr).hidden ≠ 0 ∧ opening = openKey key (expand ctr).hidden := by
  unfold Spec.CandidateScheme.attempt at h
  dsimp only at h
  split at h
  · rename_i hc
    exact ⟨hc.1, hc.2, (Attempt.ready.inj h).symm⟩
  · exact absurd h (by simp)

/-- A returned observation of the candidate attempt certifies a nonzero
encoding of the hidden vector at its counter and the candidate opening. -/
theorem observe_returned_candidate (key : Key lambda tau (2 ^ kappa)) (expand : Counter → Challenge tau (2 ^ kappa) wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat) (ctr : Counter) (opening : Opening lambda tau (2 ^ kappa))
    (h : observe (Spec.CandidateScheme.attempt key expand encode) fuel 0 = Observation.returned ctr opening) :
    encode (expand ctr).hidden ≠ 0 ∧ opening = openKey key (expand ctr).hidden :=
  (attempt_ready key expand encode ctr opening (BLCRetry.observe_returned _ fuel 0 ctr opening h).1).2

end Attempt

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- Under payload consistency, for a solution witness and an executed
commitment, the honest prepared payload equals the simulator's payload at
the returned counter's hidden vector. -/
theorem payload_eq (hpc : PayloadConsistent S) (salt root : Bits lambda)
    (witness : Fin (selectorCount widths * w) → ZMod 2) (hsol : IsSolution S witness)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (committed : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (heval : Evaluates family table ciphers (commitProgram S.signer salt root witness) committed)
    (digest : Digest lambda) (ctr : Counter) (opening : Opening lambda tau (2 ^ kappa))
    (hobs : observe (Spec.CandidateScheme.attempt (F := F) (stateOf S salt committed).2.key (S.expandEvaluation digest)
      S.encode) S.fuel 0 = Observation.returned ctr opening) :
    (stateOf S salt committed).1 =
      (committed.result.lines, simulatedCoefficients S salt committed (S.expandEvaluation digest ctr).hidden) := by
  obtain ⟨hne, _⟩ := observe_returned_candidate _ _ _ _ ctr opening hobs
  exact Prod.ext rfl (hpc salt root witness hsol family table ciphers committed heval _ hne)

/-- The retry-failure event: no returned observation of the candidate
attempt at the digest. -/
def retryFails (state : SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
    (digest : Digest lambda) : Bool :=
  decide (∀ (ctr : Counter) (opening : Opening lambda tau (2 ^ kappa)),
    observe (Spec.CandidateScheme.attempt (F := F) state.key (S.expandEvaluation digest) S.encode) S.fuel 0 ≠
      Observation.returned ctr opening)

omit [Algebra (ZMod 2) F] [NeZero tau] in
/-- When the retry-failure event is off, some observation is returned. -/
theorem returned_of_not_retryFails
    (state : SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
    (digest : Digest lambda) (h : retryFails S state digest = false) :
    ∃ (ctr : Counter) (opening : Opening lambda tau (2 ^ kappa)),
      observe (Spec.CandidateScheme.attempt (F := F) state.key (S.expandEvaluation digest) S.encode) S.fuel 0 =
        Observation.returned ctr opening := by
  unfold retryFails at h
  simpa using h

end
end SDitH.Proofs.DigestFirstBody
