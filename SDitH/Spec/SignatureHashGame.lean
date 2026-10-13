import SDitH.Spec.SignatureSecurity
import SDitH.Spec.SignatureComposition
import SDitH.Spec.AbstractSignature

/-! Algorithm 4's parsed post-recomputation suffix at the final-hash game
boundary. The existing verificationInput is used without replacing its PIOP or
coefficient computation. Supplied recomputation is still a boundary; this file
does not provide Algorithm 12's unresolved line 21 or a full Scheme instance. -/

namespace SDitH.Spec.SignatureHashGame

open SignatureComposition SignatureSecurity PIOPArithmetic Batching
noncomputable section

/-- Exact typed correspondence for the message-bound HashPiop tuple. This is
an equivalence of records, not a claim about the unspecified byte serializer. -/
def hashInputEquiv (F : Type*) (lambda higherCount : Nat) :
    AbstractSignature.HashInput (List Bool) (List Bool)
        (Digest lambda × (Fin (higherCount + 1) → F)) ≃ HashInput F lambda higherCount where
  toFun input := ⟨input.publicKey, input.payload.1, input.payload.2, input.message⟩
  invFun input := ⟨input.publicKey, input.message, (input.lines, input.coefficients)⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev SignatureBody (F Aux : Type*) (lambda tau higherCount : Nat) :=
  DomainSeparation.Bits lambda × Aux × (BLCRetry.Counter × BAVC.Opening lambda tau) ×
    (Fin higherCount → F)

/-- Exact typed correspondence for the parsed signature: its digest is the
abstract piop field; the body retains salt, auxiliary data, opening and higher
coefficients. No correctness relation between those fields is assumed. -/
def signatureEquiv (F Aux : Type*) (lambda tau higherCount : Nat) :
    AbstractSignature.Signature (Digest lambda) (SignatureBody F Aux lambda tau higherCount) ≃
      Signature F Aux lambda tau higherCount where
  toFun sig := ⟨sig.body.1, sig.piop, sig.body.2.1, sig.body.2.2.1, sig.body.2.2.2⟩
  invFun sig := ⟨sig.piop, sig.salt, sig.auxiliary, sig.decomposition, sig.higher⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {F Aux Other Query : Type*} [Field F] [Algebra (ZMod 2) F]

def postRecomputeTerminal {r k w lambda tau higherCount : Nat}
    (widths : List Nat) (hdegree : widths.length = higherCount + 1)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F))
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (publicKey message : List Bool) (signature : Signature F Aux lambda tau higherCount)
    (opening : Option (Recomputed F lambda (selectorCount widths * w)
      (lambda * (widths.length - 1))))
    (world : World (HashInput F lambda higherCount) (Digest lambda) Other)
    (trace : Trace (List Bool) (HashInput F lambda higherCount) Query) :
    Terminal (List Bool) (Signature F Aux lambda tau higherCount)
      (HashInput F lambda higherCount) (Digest lambda) Other Query :=
  match opening with
  | none => .rejected trace
  | some recovered => .attempt
      ⟨message, signature,
        verificationInput widths hdegree hsize xi expandBatching H' y publicKey message signature recovered,
        signature.piop, world, trace⟩

end
end SDitH.Spec.SignatureHashGame
