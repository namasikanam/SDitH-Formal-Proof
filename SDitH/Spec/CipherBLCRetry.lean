import SDitH.Spec.CipherEvaluation
import SDitH.Spec.PartialBLCRetry

/-! Algorithm 11 at the complete staged cipher-expansion boundary. The left
side of Except records an undefined source interpretation and its counter,
not a retry, source abort, or fabricated challenge. The right side retains
every earlier integer/BAVC observation without merging their fault meanings.
-/

namespace SDitH.Spec.CipherBLCRetry

open DomainSeparation ConcreteChallenges CipherEvaluation

def step {F : Type*} [Zero F] [DecidableEq F] {lambda tau kappa wpow : Nat}
    (key : BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : BLCRetry.Counter → Except (Boundary lambda) (EvaluationObservation tau kappa wpow))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (counter : BLCRetry.Counter) :
    Except (Boundary lambda) (PartialBLCRetry.PartialStep lambda tau kappa) :=
  match expand counter with
  | .error fault => .error fault
  | .ok observation => .ok (PartialBLCRetry.step key Topen (fun _ => observation) encode counter)

def observe {F : Type*} [Zero F] [DecidableEq F] {lambda tau kappa wpow : Nat}
    (key : BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : BLCRetry.Counter → Except (Boundary lambda) (EvaluationObservation tau kappa wpow))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) :
    Nat → BLCRetry.Counter → Except (BLCRetry.Counter × Boundary lambda)
      (PartialBLCRetry.Observation lambda tau kappa)
  | 0, counter => .ok (.pending counter)
  | fuel + 1, counter =>
    match step key Topen expand encode counter with
    | .error fault => .error (counter, fault)
    | .ok (.expansionPending state) => .ok (.expansionPending counter state)
    | .ok (.undefinedExpansion state candidate) => .ok (.undefinedExpansion counter state candidate)
    | .ok (.decided (.again next)) => observe key Topen expand encode fuel next
    | .ok (.decided (.done result opening)) => .ok (.returned result opening)
    | .ok (.decided (.undefined fault)) => .ok (.undefinedOpening fault)

def openWithBindings {F : Type*} [Zero F] [DecidableEq F] (category : FieldRepresentation.Category)
    (tau kappa wpow : Nat) (key : BAVC.Key (FieldRepresentation.width category) tau (2 ^ kappa))
    (Topen : Nat) (encoding : CounterEncoding) (digest : Bits (2 * FieldRepresentation.width category))
    (bindings : Bindings category wpow) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (innerFuel outerFuel : Nat) :
    Except (BLCRetry.Counter × Boundary (FieldRepresentation.width category))
      (PartialBLCRetry.Observation (FieldRepresentation.width category) tau kappa) :=
  observe key Topen
    (fun counter => evaluateWithBindings category tau kappa wpow encoding digest counter bindings innerFuel)
    encode outerFuel 0

def openLiteral {F : Type*} [Zero F] [DecidableEq F] (category : FieldRepresentation.Category)
    (tau kappa wpow : Nat) (key : BAVC.Key (FieldRepresentation.width category) tau (2 ^ kappa))
    (Topen : Nat) (encoding : CounterEncoding) (digest : Bits (2 * FieldRepresentation.width category))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel : Nat) :
    Except (BLCRetry.Counter × Boundary (FieldRepresentation.width category))
      (PartialBLCRetry.Observation (FieldRepresentation.width category) tau kappa) :=
  openWithBindings category tau kappa wpow key Topen encoding digest (absentBindings category wpow)
    encode innerFuel outerFuel

end SDitH.Spec.CipherBLCRetry
