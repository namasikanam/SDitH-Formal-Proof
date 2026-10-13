import SDitH.Spec.Signing
import SDitH.Proofs.SignatureComposition
import SDitH.Proofs.BLCCommit

namespace SDitH.Proofs.Signing

open Spec.Signing Spec.SignatureComposition Spec.DomainSeparation Spec.PIOPArithmetic Spec.Batching

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]
variable {r k w lambda tau kappa B higherCount : Nat} [NeZero tau]
variable (widths : List Nat) (hdegree : widths.length = higherCount + 1)
variable (hsize : leafCount widths * w = r + k) (xi : F)
variable (primitives : Spec.BLCCommit.Primitives lambda tau kappa (lambda + B)
  (selectorCount widths * w) (lambda * (widths.length - 1)))
variable (expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F))
variable (hashPiop : HashInput F lambda higherCount → Digest lambda)
variable (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
variable (publicKey message : List Bool) (salt root : Bits lambda)
variable (witness : Fin (selectorCount widths * w) → ZMod 2)
variable (randomCount consistencyCount : Nat)
variable (hrandom : lambda + B + (selectorCount widths * w + lambda * (widths.length - 1)) ≤ 8 * randomCount)
variable (hconsistency : selectorCount widths * w + lambda * (widths.length - 1) ≤ 8 * consistencyCount)

/-- The degree premise for coefficient compression now follows through the
actual BLC commitment, without passing polynomial degrees as an interface contract. -/
theorem prepared_degree (hd : 2 ≤ widths.length) :
    (prepareFromSeeds widths hdegree hsize xi primitives expandBatching hashPiop H' y
      publicKey message salt root witness randomCount consistencyCount hrandom hconsistency).polynomial.natDegree ≤
      higherCount + 1 := by
  have hlines := BLCCommit.line_properties xi primitives salt root witness randomCount consistencyCount
    hrandom hconsistency
  exact SignatureComposition.prepared_degree widths hdegree hsize xi expandBatching hashPiop H' y
    publicKey message salt _ hd hlines.2.1 hlines.2.2

/-- Hash-input agreement through actual Algorithm-10 line construction still
requires a zero output constant. The equivalence does not assume that disputed
source claim. The compared opening is explicitly the committed evaluation record. -/
theorem hash_input_eq_iff (counter : Spec.BLCRetry.Counter)
    (opening : Spec.BAVC.Opening lambda tau) (delta : F) (hdelta : delta ≠ 0)
    (hd : 2 ≤ widths.length) :
    let committed := Spec.BLCCommit.commit xi primitives salt root witness randomCount consistencyCount
      hrandom hconsistency
    let prepared := prepareFromSeeds widths hdegree hsize xi primitives expandBatching hashPiop H' y
      publicKey message salt root witness randomCount consistencyCount hrandom hconsistency
    verificationInput widths hdegree hsize xi expandBatching H' y publicKey message
      (attachOpening prepared counter opening)
      (SignatureComposition.evaluatedCommitment widths (commitmentRecord committed) delta) =
      ⟨publicKey, committed.lines, Spec.CoefficientCompression.hashedCoefficients higherCount prepared.polynomial, message⟩ ↔
      prepared.polynomial.coeff 0 = 0 := by
  have hlines := BLCCommit.line_properties xi primitives salt root witness randomCount consistencyCount
    hrandom hconsistency
  exact SignatureComposition.verification_input_eq_iff widths hdegree hsize xi expandBatching hashPiop H' y
    publicKey message salt _ counter opening delta hdelta hd hlines.2.1 hlines.2.2

end SDitH.Proofs.Signing
