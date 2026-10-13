import SDitH.Spec.Signing
import SDitH.Spec.PartialBLCRetry
import SDitH.Spec.BLCRecompute

/-! Algorithms 3/4 at their partial subroutine call sites. Parsed keys,
serialization, primitive interfaces and the documented source bindings remain
explicit. Finite observation is not a source failure. Algorithm 12's explicit
bottom tuple becomes verification rejection, but an undefined read does not.
The verifier prefix stops before the ill-typed line 21. Its separately callable
suffix takes a supplied base matrix without asserting that it implements line 21.
-/

namespace SDitH.Spec.PartialSignature

open DomainSeparation SignatureComposition ConcreteChallenges

inductive SigningObservation (F Aux : Type*) (lambda tau kappa higherCount : Nat) where
  | pending (counter : BLCRetry.Counter)
  | expansionPending (counter : BLCRetry.Counter)
      (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
  | undefinedExpansion (counter : BLCRetry.Counter)
      (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
      (candidate : IntegerSampling.Candidate)
  | returned (signature : Signature F Aux lambda tau higherCount)
  | undefinedOpening (fault : BLCRetry.Fault)

def finishSigning {F Aux : Type*} [Field F] {lambda tau kappa higherCount : Nat}
    (prepared : Prepared F Aux lambda tau (2 ^ kappa) higherCount) :
    PartialBLCRetry.Observation lambda tau kappa →
      SigningObservation F Aux lambda tau kappa higherCount
  | .pending counter => .pending counter
  | .expansionPending counter state => .expansionPending counter state
  | .undefinedExpansion counter state candidate => .undefinedExpansion counter state candidate
  | .returned counter opening => .returned (attachOpening prepared counter opening)
  | .undefinedOpening fault => .undefinedOpening fault

/-- Algorithm 3 lines 8–10 after actual phases 1–2. Only a returned opening
constructs the typed signature components; no raw serialization is selected. -/
def observeSigning {F Aux : Type*} [Field F] [DecidableEq F]
    {lambda tau kappa wpow higherCount : Nat}
    (prepared : Prepared F Aux lambda tau (2 ^ kappa) higherCount) (Topen : Nat)
    (expand : Digest lambda → BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat) :
    SigningObservation F Aux lambda tau kappa higherCount :=
  finishSigning prepared (PartialBLCRetry.observe prepared.key Topen
    (expand prepared.piop) encode fuel 0)

/-- Concrete hash challenge expansion at the actual signing call site. -/
def hashSigning {F Aux : Type*} [Field F] [DecidableEq F]
    (category : FieldRepresentation.Category) {tau kappa higherCount : Nat} (wpow : Nat)
    (prepared : Prepared F Aux (FieldRepresentation.width category) tau (2 ^ kappa) higherCount)
    (Topen : Nat) (encoding : CounterEncoding)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel count : Nat)
    (enough : wpow ≤ 8 * count) :
    SigningObservation F Aux (FieldRepresentation.width category) tau kappa higherCount :=
  finishSigning prepared (PartialBLCRetry.hashOpen category tau kappa wpow prepared.key
    Topen encoding prepared.piop encode innerFuel outerFuel count enough)

/-- Actual BLC commitment and PIOP preparation feed the partial opening caller.
The source initialization and existing primitive interfaces remain explicit. -/
noncomputable def signAfterInitialization {F : Type*} [Field F] [Algebra (ZMod 2) F]
    [DecidableEq F] {r k w lambda tau kappa B wpow higherCount : Nat} [NeZero tau]
    (widths : List Nat) (hdegree : widths.length = higherCount + 1)
    (hsize : PIOPArithmetic.leafCount widths * w = r + k) (xi : F)
    (primitives : BLCCommit.Primitives lambda tau kappa (lambda + B)
      (PIOPArithmetic.selectorCount widths * w) (lambda * (widths.length - 1)))
    (expandBatching : Digest lambda → (Fin (Batching.blockCount r lambda) → F) × (Fin w → F))
    (hashPiop : HashInput F lambda higherCount → Digest lambda)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (publicKey message : List Bool) (salt root : Bits lambda)
    (witness : Fin (PIOPArithmetic.selectorCount widths * w) → ZMod 2)
    (randomCount consistencyCount : Nat)
    (hrandom : lambda + B + (PIOPArithmetic.selectorCount widths * w + lambda * (widths.length - 1)) ≤
      8 * randomCount)
    (hconsistency : PIOPArithmetic.selectorCount widths * w + lambda * (widths.length - 1) ≤
      8 * consistencyCount) (Topen : Nat)
    (expand : Digest lambda → BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat) :
    SigningObservation F (BLCCommit.Auxiliary tau (lambda + B)
      (PIOPArithmetic.selectorCount widths * w) (lambda * (widths.length - 1)))
      lambda tau kappa higherCount :=
  observeSigning (Signing.prepareFromSeeds widths hdegree hsize xi primitives expandBatching
    hashPiop H' y publicKey message salt root witness randomCount consistencyCount hrandom hconsistency)
    Topen expand encode fuel

def liftTotalSigning {F Aux : Type*} {lambda tau kappa higherCount : Nat} :
    BLCRetry.Observation (Signature F Aux lambda tau higherCount) →
      SigningObservation F Aux lambda tau kappa higherCount
  | .pending counter => .pending counter
  | .undefined fault => .undefinedOpening fault
  | .returned _ signature => .returned signature

/-- No Accept outcome exists in this prefix. The stopped consistency state
is not a completed BLC recomputation. -/
inductive VerificationPrefix (F : Type) (lambda tau kappa B wit rnd : Nat) where
  | expansionPending (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
  | undefinedExpansion (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
      (candidate : IntegerSampling.Candidate)
  | rejected
  | undefinedRecomputation (cause : BLCRecompute.Error)
  | consistencyBoundary (state : BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd)

def finishRecompute {F : Type} {lambda tau kappa B wit rnd : Nat} :
    Except BLCRecompute.Error (BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd) →
      VerificationPrefix F lambda tau kappa B wit rnd
  | .error .headerRejected => .rejected
  | .error cause => .undefinedRecomputation cause
  | .ok state => .consistencyBoundary state

/-- Algorithm 4's recomputation call, including partial challenge expansion.
Only the explicit bottom tuple in Algorithm 12 reaches the source Reject branch.
In particular an Algorithm-9 error is preserved as an undefined tuple read. -/
noncomputable def recompute {F : Type} [Field F] [DecidableEq F]
    {lambda tau kappa B wit rnd wpow higherCount : Nat}
    (p : BLCCommit.Primitives lambda tau kappa (lambda + B) wit rnd)
    (signature : Signature F (BLCCommit.Auxiliary tau (lambda + B) wit rnd) lambda tau higherCount)
    (expand : Digest lambda → BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
    (bindings : BLCRecompute.Bindings lambda tau kappa ((lambda + B) + (wit + rnd)))
    (randomCount consistencyCount : Nat)
    (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount) : VerificationPrefix F lambda tau kappa B wit rnd :=
  match expand signature.piop signature.decomposition.1 with
  | .pending state => .expansionPending state
  | .undefinedIntegerAssignment state candidate => .undefinedExpansion state candidate
  | .returned challenge _ => finishRecompute (BLCRecompute.prepareWithBindings p
      signature.salt signature.auxiliary signature.decomposition (fun _ => challenge)
      encode Topen bindings randomCount consistencyCount hrandom hconsistency)

/-- The concrete SHAKE/integer routine is called on the parsed signature's
digest and transmitted counter, before the recomputation header test. -/
noncomputable def hashRecompute {F : Type} [Field F] [DecidableEq F]
    (category : FieldRepresentation.Category) {tau kappa B wit rnd higherCount : Nat} (wpow : Nat)
    (p : BLCCommit.Primitives (FieldRepresentation.width category) tau kappa
      (FieldRepresentation.width category + B) wit rnd)
    (signature : Signature F (BLCCommit.Auxiliary tau (FieldRepresentation.width category + B) wit rnd)
      (FieldRepresentation.width category) tau higherCount)
    (encoding : CounterEncoding) (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
    (bindings : BLCRecompute.Bindings (FieldRepresentation.width category) tau kappa
      ((FieldRepresentation.width category + B) + (wit + rnd)))
    (randomCount consistencyCount : Nat)
    (hrandom : (FieldRepresentation.width category + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount)
    (fuel count : Nat) (enough : wpow ≤ 8 * count) :
    VerificationPrefix F (FieldRepresentation.width category) tau kappa B wit rnd :=
  recompute p signature
    (fun digest counter => hashEvaluation category tau kappa wpow encoding digest counter fuel count enough)
    encode Topen bindings randomCount consistencyCount hrandom hconsistency

/-- Independent suffix: Algorithm 12 lines 22–27 then Algorithm 4 lines 8–13.
The base argument is an external source-resolution boundary, not a proved
implementation of Algorithm 12 line 21. This function cannot consume a prefix
error, pending observation or undefined operation as if it were a returned state. -/
noncomputable def verifySuffix {F : Type} [Field F] [Algebra (ZMod 2) F]
    {r k w lambda tau kappa B higherCount : Nat}
    (widths : List Nat) (hdegree : widths.length = higherCount + 1)
    (hsize : PIOPArithmetic.leafCount widths * w = r + k) (xi : F)
    (expandBatching : Digest lambda → (Fin (Batching.blockCount r lambda) → F) × (Fin w → F))
    (hashPiop : HashInput F lambda higherCount → Digest lambda)
    (hashLines : BLCRecompute.LinesHashInput lambda tau kappa (lambda + B) → Digest lambda)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (publicKey message : List Bool)
    (signature : Signature F (BLCCommit.Auxiliary tau (lambda + B)
      (PIOPArithmetic.selectorCount widths * w) (lambda * (widths.length - 1))) lambda tau higherCount)
    (state : BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B)
      (PIOPArithmetic.selectorCount widths * w) (lambda * (widths.length - 1)))
    (base : Fin (lambda + B) → Fin tau → Fin kappa → ZMod 2) : Bool :=
  verifyPostRecompute widths hdegree hsize xi expandBatching hashPiop H' y publicKey message signature
    (some (BLCRecompute.suffix xi hashLines state base))

end SDitH.Spec.PartialSignature
