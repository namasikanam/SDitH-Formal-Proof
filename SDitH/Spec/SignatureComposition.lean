import SDitH.Spec.PIOPComposition
import SDitH.Spec.CoefficientCompression
import SDitH.Spec.BLCRetry

/-! Algorithms 3/4 at explicit parsed-key, BLC-commit and BLC-recompute
boundaries. The PIOP computation, coefficient handling, hash-input component
order and actual Algorithm-11 retry loop are composed here. This is not a
replacement implementation of the missing/ambiguous BLC reconstruction or byte
serialization. HashPiop consumes a typed tuple at that representation boundary.
No security or correctness contract for the supplied functions is assumed.
-/

namespace SDitH.Spec.SignatureComposition

open DomainSeparation PIOPArithmetic PIOPComposition CoefficientCompression Batching

abbrev Digest (lambda : Nat) := Bits (2 * lambda)

/-- The ordered fields of Algorithm 3 line 7 and Algorithm 4 line 10. Public
key and message are already bit strings; coefficient bytes remain a boundary.
Messages are not restricted to byte-aligned lengths. -/
structure HashInput (F : Type*) (lambda higherCount : Nat) where
  publicKey : List Bool
  lines : Digest lambda
  coefficients : Fin (higherCount + 1) → F
  message : List Bool

/-- The output of BLC.Commit consumed by Algorithm 3. These fields assert no
unproved relation between the commitment digest, key and polynomial arrays. -/
structure Commitment (F Aux : Type*) [CommRing F] (lambda tau N wit rnd : Nat) where
  witness : Fin wit → Polynomial F
  randomness : Fin rnd → Polynomial F
  lines : Digest lambda
  key : BAVC.Key lambda tau N
  auxiliary : Aux

/-- Parsed components of Algorithm 3 line 9, preserving its order. -/
structure Signature (F Aux : Type*) (lambda tau higherCount : Nat) where
  salt : Bits lambda
  piop : Digest lambda
  auxiliary : Aux
  decomposition : BLCRetry.Counter × BAVC.Opening lambda tau
  higher : Fin higherCount → F

/-- Successful BLC.RecomputeEvaluation output. Rejection is represented by
Option.none at the caller. No consistency or nonzero-delta property is hidden
in this record; those properties must be proved for the actual routine. -/
structure Recomputed (F : Type*) (lambda wit rnd : Nat) where
  delta : F
  witness : Fin wit → F
  randomness : Fin rnd → F
  lines : Digest lambda

structure Prepared (F Aux : Type*) [CommRing F] (lambda tau N higherCount : Nat) where
  polynomial : Polynomial F
  salt : Bits lambda
  piop : Digest lambda
  auxiliary : Aux
  key : BAVC.Key lambda tau N
  higher : Fin higherCount → F

noncomputable section

variable {F Aux : Type*} [Field F]

/-- Algorithm 3 lines 6–7 and the coefficient extraction for line 9. The
positive degree is widths.length = higherCount+1, retained as a source premise.
The other size equality is the source's unresolved Table-3 dimension condition. -/
def prepare {r k w lambda tau N higherCount : Nat}
    (widths : List Nat) (_degree : widths.length = higherCount + 1)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F))
    (hashPiop : HashInput F lambda higherCount → Digest lambda)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (publicKey message : List Bool) (salt : Bits lambda)
    (commit : Commitment F Aux lambda tau N (selectorCount widths * w)
      (lambda * (widths.length - 1))) [Algebra (ZMod 2) F] :
    Prepared F Aux lambda tau N higherCount :=
  let challenge := expandBatching commit.lines
  let p := proverRun widths hsize xi challenge.1 challenge.2 H' y commit.witness commit.randomness
  { polynomial := p
    salt := salt
    piop := hashPiop ⟨publicKey, commit.lines, hashedCoefficients higherCount p, message⟩
    auxiliary := commit.auxiliary
    key := commit.key
    higher := transmittedCoefficients higherCount p }

/-- Complete Algorithm 3's typed signature record after Algorithm 11 returns. -/
def attachOpening {lambda tau N higherCount : Nat}
    (prepared : Prepared F Aux lambda tau N higherCount)
    (counter : BLCRetry.Counter) (opening : BAVC.Opening lambda tau) :
    Signature F Aux lambda tau higherCount :=
  ⟨prepared.salt, prepared.piop, prepared.auxiliary, (counter, opening), prepared.higher⟩

/-- Algorithm 3 lines 8–10, using the actual retry/opening implementation.
Fuel limits observation, not source execution. Pending and undefined outcomes
remain distinct and are not converted to invented signature failures. -/
def observeSigning [DecidableEq F] {lambda tau N wpow higherCount : Nat}
    (prepared : Prepared F Aux lambda tau N higherCount) (Topen : Nat)
    (expandEvaluation : Digest lambda → BLCRetry.Counter → BLCRetry.Challenge tau N wpow)
    (encode : (Fin tau → Fin N) → F) (fuel : Nat) :
    BLCRetry.Observation (Signature F Aux lambda tau higherCount) :=
  match BLCRetry.openRandomEvaluation prepared.key Topen (expandEvaluation prepared.piop) encode fuel with
  | .pending counter => .pending counter
  | .undefined fault => .undefined fault
  | .returned counter opening => .returned counter (attachOpening prepared counter opening)

/-- Algorithm 4 lines 8–10 on a successful recomputation. The supplied
evaluation arrays feed the actual composed verifier, then alpha_1 is recovered
from the transmitted higher coefficients. -/
def verificationInput {r k w lambda tau higherCount : Nat}
    (widths : List Nat) (_degree : widths.length = higherCount + 1)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F))
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (publicKey message : List Bool) (signature : Signature F Aux lambda tau higherCount)
    (opening : Recomputed F lambda (selectorCount widths * w) (lambda * (widths.length - 1)))
    [Algebra (ZMod 2) F] : HashInput F lambda higherCount :=
  let challenge := expandBatching opening.lines
  let value := verifierRun widths hsize xi opening.delta challenge.1 challenge.2 H' y
    opening.witness opening.randomness
  ⟨publicKey, opening.lines, restoredCoefficients opening.delta value signature.higher, message⟩

/-- Algorithm 4's rejection on failed recomputation, followed by its final
hash equality test. Parsing and the unresolved Algorithm-12 body remain explicit
boundaries; this function does not replace them with a correctness premise. -/
def verifyPostRecompute {r k w lambda tau higherCount : Nat}
    (widths : List Nat) (hdegree : widths.length = higherCount + 1)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F))
    (hashPiop : HashInput F lambda higherCount → Digest lambda)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (publicKey message : List Bool) (signature : Signature F Aux lambda tau higherCount)
    (opening : Option (Recomputed F lambda (selectorCount widths * w) (lambda * (widths.length - 1))))
    [Algebra (ZMod 2) F] : Bool :=
  match opening with
  | none => false
  | some recovered => decide
      (hashPiop (verificationInput widths hdegree hsize xi expandBatching H' y publicKey message
        signature recovered) = signature.piop)

end
end SDitH.Spec.SignatureComposition
