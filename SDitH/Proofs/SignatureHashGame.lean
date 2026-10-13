import SDitH.Spec.SignatureHashGame
import SDitH.Proofs.SignatureSecurity
import SDitH.Proofs.AbstractSignature
import SDitH.Proofs.SignatureForgeryFork

namespace SDitH.Proofs.SignatureHashGame

open Spec.SignatureComposition Spec.SignatureSecurity Spec.SignatureHashGame
open Spec.PIOPArithmetic Spec.Batching
open scoped Classical ENNReal
noncomputable section

variable {F Aux Other Query : Type*} [Field F] [Algebra (ZMod 2) F]
variable {r k w lambda tau higherCount : Nat}
variable (widths : List Nat) (hdegree : widths.length = higherCount + 1)
variable (hsize : leafCount widths * w = r + k) (xi : F)
variable (expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F))
variable (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
variable (publicKey message : List Bool) (signature : Signature F Aux lambda tau higherCount)
variable (opening : Option (Recomputed F lambda (selectorCount widths * w)
  (lambda * (widths.length - 1))))
variable (world : World (HashInput F lambda higherCount) (Digest lambda) Other)
variable (trace : Trace (List Bool) (HashInput F lambda higherCount) Query)

/-- The exact Algorithm-4 final predicate, once its required hash answer is
available. The only oracle premise concerns that one lookup, not security or
correctness of recomputation. Freshness is the extra §5.3 game condition. -/
theorem resolved_final_test
    (hashPiop : HashInput F lambda higherCount → Digest lambda)
    (hanswer : ∀ recovered, opening = some recovered →
      world.hashTable
        (verificationInput widths hdegree hsize xi expandBatching H' y publicKey message signature recovered) =
      some (hashPiop
        (verificationInput widths hdegree hsize xi expandBatching H' y publicKey message signature recovered))) :
    ((finalize (postRecomputeTerminal widths hdegree hsize xi expandBatching H' y
      publicKey message signature opening world trace)).map Checked.wins) =
      PMF.pure (decide (message ∉ trace.signingRequests) &&
        verifyPostRecompute widths hdegree hsize xi expandBatching hashPiop H' y
          publicKey message signature opening) := by
  cases opening with
  | none => simp [postRecomputeTerminal, finalize, PMF.pure_map, verifyPostRecompute]
  | some recovered =>
    simp [postRecomputeTerminal, finalize, Spec.RandomOracle.query, hanswer recovered rfl,
      PMF.pure_map, verifyPostRecompute]

/-- Source message binding is present in the actual verifier hash tuple.
Byte-level injectivity and the origin of all table entries remain separate. -/
theorem fresh_verification_input_not_in_signing_inputs
    (recovered : Recomputed F lambda (selectorCount widths * w)
      (lambda * (widths.length - 1)))
    (signingInputs : List (HashInput F lambda higherCount))
    (hlogged : ∀ input ∈ signingInputs, input.message ∈ trace.signingRequests)
    (hfresh : message ∉ trace.signingRequests) :
    verificationInput widths hdegree hsize xi expandBatching H' y publicKey message
      signature recovered ∉ signingInputs := by
  intro hmem
  exact hfresh (hlogged _ hmem)

omit [Field F] [Algebra (ZMod 2) F] in
/-- The unqueried final-hash term for arbitrary adaptive distributions over
the actual typed SDitH terminal interface. No full Scheme instance is asserted. -/
theorem sdith_unqueried_final_hash
    (terminals : PMF (Terminal (List Bool) (Signature F Aux lambda tau higherCount)
      (HashInput F lambda higherCount) (Digest lambda) Other Query)) :
    ((terminals.bind finalize).map
      (fun checked => checked.wins && !checked.inputWasPresent)) true ≤
      ((2 : ℝ≥0∞) ^ (2 * lambda))⁻¹ := by
  simpa only [SignatureSecurity.sdith_digest_card] using
    SignatureSecurity.terminal_law_unqueried_bound terminals

omit [Field F] [Algebra (ZMod 2) F] in
/-- The first reduction step specialized to the source's exact typed payload,
signature-body and 2*lambda-bit digest shapes. Components still need their
source implementations and security proofs; they have no assumed contracts. -/
theorem typed_forgery_to_prior_query {SecretKey CommitState Answer State : Type*}
    (components : Spec.AbstractSignature.Components (List Bool) SecretKey (List Bool)
      (Digest lambda × (Fin (higherCount + 1) → F)) (Digest lambda)
      (SignatureBody F Aux lambda tau higherCount) CommitState Other Query Answer)
    (adversary : Adversary (List Bool) (List Bool)
      (Spec.AbstractSignature.Signature (Digest lambda) (SignatureBody F Aux lambda tau higherCount))
      (Spec.AbstractSignature.HashInput (List Bool) (List Bool)
        (Digest lambda × (Fin (higherCount + 1) → F)))
      (Digest lambda) Query Answer State)
    (fuel : Nat) :
    advantage (Spec.AbstractSignature.scheme components) adversary fuel ≤
      ((experiment (Spec.AbstractSignature.scheme components) adversary fuel).map
        AbstractSignature.queriedWinning) true + ((2 : ℝ≥0∞) ^ (2 * lambda))⁻¹ := by
  simpa only [SignatureSecurity.sdith_digest_card] using
    AbstractSignature.forgery_to_prior_hash_query components adversary fuel

omit [Field F] [Algebra (ZMod 2) F] in
/-- The proved uniform-index replay bound at the source's typed record shapes.
Subtraction is truncated at zero. The replay still uses the honest signing
secret; neither a full source Scheme instance nor RSD extraction is asserted. -/
theorem typed_forgery_to_fork {SecretKey CommitState Answer State : Type*}
    (components : Spec.AbstractSignature.Components (List Bool) SecretKey (List Bool)
      (Digest lambda × (Fin (higherCount + 1) → F)) (Digest lambda)
      (SignatureBody F Aux lambda tau higherCount) CommitState Other Query Answer)
    (adversary : Adversary (List Bool) (List Bool)
      (Spec.AbstractSignature.Signature (Digest lambda) (SignatureBody F Aux lambda tau higherCount))
      (Spec.AbstractSignature.HashInput (List Bool) (List Bool)
        (Digest lambda × (Fin (higherCount + 1) → F)))
      (Digest lambda) Query Answer State)
    (fuel : Nat) :
    (advantage (Spec.AbstractSignature.scheme components) adversary (fuel + 1) -
      ((2 : ℝ≥0∞) ^ (2 * lambda))⁻¹) ^ 2 ≤
        ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
          (Spec.SignatureQuerySelection.randomForkExperiment
            (Spec.AbstractSignature.scheme components) adversary fuel true +
            ((2 : ℝ≥0∞) ^ (2 * lambda))⁻¹) := by
  simpa only [SignatureSecurity.sdith_digest_card] using
    SignatureForgeryFork.forgery_to_fork components adversary fuel

end
end SDitH.Proofs.SignatureHashGame
