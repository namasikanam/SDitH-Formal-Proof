import SDitH.Spec.CipherBLCRetry
import SDitH.Spec.PartialSignature

/-! Cipher-based callers for Algorithms 3/4. The initial prepared record is
the same actual BLC/PIOP preparation used by Signing.prepareFromSeeds. The
left Except outcome preserves unresolved cipher-source operations. The right
outcome retains the partial signing/verifier observations and never fabricates
an acceptance from a stopped computation. The verifier still stops before
Algorithm-12 line 21; its existing separately specified suffix is unchanged.
-/

namespace SDitH.Spec.CipherSignature

open DomainSeparation FieldRepresentation ConcreteChallenges CipherEvaluation SignatureComposition

def finishSigning {F Aux : Type*} [Field F] {lambda tau kappa higherCount : Nat}
    (prepared : Prepared F Aux lambda tau (2 ^ kappa) higherCount)
    (observation : Except (BLCRetry.Counter × Boundary lambda)
      (PartialBLCRetry.Observation lambda tau kappa)) :
    Except (BLCRetry.Counter × Boundary lambda)
      (PartialSignature.SigningObservation F Aux lambda tau kappa higherCount) :=
  observation.map (PartialSignature.finishSigning prepared)

def signWithBindings {F Aux : Type*} [Field F] [DecidableEq F]
    (category : Category) {tau kappa higherCount : Nat} (wpow : Nat)
    (prepared : Prepared F Aux (width category) tau (2 ^ kappa) higherCount)
    (Topen : Nat) (encoding : CounterEncoding) (bindings : Bindings category wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel : Nat) :
    Except (BLCRetry.Counter × Boundary (width category))
      (PartialSignature.SigningObservation F Aux (width category) tau kappa higherCount) :=
  finishSigning prepared (CipherBLCRetry.openWithBindings category tau kappa wpow prepared.key
    Topen encoding prepared.piop bindings encode innerFuel outerFuel)

def signLiteral {F Aux : Type*} [Field F] [DecidableEq F]
    (category : Category) {tau kappa higherCount : Nat} (wpow : Nat)
    (prepared : Prepared F Aux (width category) tau (2 ^ kappa) higherCount)
    (Topen : Nat) (encoding : CounterEncoding)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel : Nat) :
    Except (BLCRetry.Counter × Boundary (width category))
      (PartialSignature.SigningObservation F Aux (width category) tau kappa higherCount) :=
  signWithBindings category wpow prepared Topen encoding (absentBindings category wpow)
    encode innerFuel outerFuel

/-- The parsed signature's digest and transmitted counter feed the complete
cipher expansion. Only a genuine returned challenge reaches the existing
Algorithm-12 prefix, including its distinct source-Reject/undefined outcomes. -/
noncomputable def recomputeWithBindings {F : Type} [Field F] [DecidableEq F]
    (category : Category) {tau kappa B wit rnd higherCount : Nat} (wpow : Nat)
    (p : BLCCommit.Primitives (width category) tau kappa (width category + B) wit rnd)
    (signature : Signature F (BLCCommit.Auxiliary tau (width category + B) wit rnd)
      (width category) tau higherCount)
    (encoding : CounterEncoding) (cipherBindings : Bindings category wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
    (blcBindings : BLCRecompute.Bindings (width category) tau kappa
      ((width category + B) + (wit + rnd)))
    (randomCount consistencyCount : Nat)
    (hrandom : (width category + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount) (fuel : Nat) :
    Except (Boundary (width category)) (PartialSignature.VerificationPrefix F (width category) tau kappa B wit rnd) :=
  match evaluateWithBindings category tau kappa wpow encoding signature.piop
      signature.decomposition.1 cipherBindings fuel with
  | .error fault => .error fault
  | .ok observation => .ok (PartialSignature.recompute p signature (fun _ _ => observation)
      encode Topen blcBindings randomCount consistencyCount hrandom hconsistency)

noncomputable def recomputeLiteral {F : Type} [Field F] [DecidableEq F]
    (category : Category) {tau kappa B wit rnd higherCount : Nat} (wpow : Nat)
    (p : BLCCommit.Primitives (width category) tau kappa (width category + B) wit rnd)
    (signature : Signature F (BLCCommit.Auxiliary tau (width category + B) wit rnd)
      (width category) tau higherCount)
    (encoding : CounterEncoding) (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
    (blcBindings : BLCRecompute.Bindings (width category) tau kappa
      ((width category + B) + (wit + rnd)))
    (randomCount consistencyCount : Nat)
    (hrandom : (width category + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount) (fuel : Nat) :
    Except (Boundary (width category)) (PartialSignature.VerificationPrefix F (width category) tau kappa B wit rnd) :=
  recomputeWithBindings category wpow p signature encoding (absentBindings category wpow)
    encode Topen blcBindings randomCount consistencyCount hrandom hconsistency fuel

end SDitH.Spec.CipherSignature
