import SDitH.Spec.ConcreteChallenges

/-! Algorithm 11 with partial challenge generation at its actual call site.
The earlier total-challenge interface is retained, with a proved refinement
when expansion returns. A pending inner observation does not advance the outer
counter, and an undefined integer assignment is not a grinding rejection.
Inner fuel observes integer attempts; outer fuel observes Algorithm-11 attempts.
Neither is a source abort condition. Cipher parser/extraction gaps remain before
the separately staged cipher expander, rather than being filled by this module.
-/

namespace SDitH.Spec.PartialBLCRetry

open DomainSeparation BLCRetry ConcreteChallenges

inductive PartialStep (lambda tau kappa : Nat) where
  | expansionPending (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
  | undefinedExpansion (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
      (candidate : IntegerSampling.Candidate)
  | decided (result : BLCRetry.Step (BAVC.Opening lambda tau))

/-- BAVC.Open, the grinding/nonzero test and counter advancement execute only
after an actual returned challenge. The next XOF cursor is unused by Algorithm 11. -/
def step {F : Type*} [Zero F] [DecidableEq F] {lambda tau kappa wpow : Nat}
    (key : BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (counter : Counter) : PartialStep lambda tau kappa :=
  match expand counter with
  | .pending state => .expansionPending state
  | .undefinedIntegerAssignment state candidate => .undefinedExpansion state candidate
  | .returned challenge _ => .decided
    (BLCRetry.step (BLCRetry.attempt key Topen (fun _ => challenge) encode) counter)

inductive Observation (lambda tau kappa : Nat) where
  | pending (counter : Counter)
  | expansionPending (counter : Counter) (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
  | undefinedExpansion (counter : Counter) (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
      (candidate : IntegerSampling.Candidate)
  | returned (counter : Counter) (opening : BAVC.Opening lambda tau)
  | undefinedOpening (fault : BLCRetry.Fault)

/-- Observe the whole retry loop starting at an explicit counter. -/
def observe {F : Type*} [Zero F] [DecidableEq F] {lambda tau kappa wpow : Nat}
    (key : BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) : Nat → Counter → Observation lambda tau kappa
  | 0, counter => .pending counter
  | fuel + 1, counter =>
    match step key Topen expand encode counter with
    | .expansionPending state => .expansionPending counter state
    | .undefinedExpansion state candidate => .undefinedExpansion counter state candidate
    | .decided (.again next) => observe key Topen expand encode fuel next
    | .decided (.done result opening) => .returned result opening
    | .decided (.undefined fault) => .undefinedOpening fault

def liftTotal {lambda tau kappa : Nat} : BLCRetry.Observation (BAVC.Opening lambda tau) →
    Observation lambda tau kappa
  | .pending counter => .pending counter
  | .returned counter opening => .returned counter opening
  | .undefined fault => .undefinedOpening fault

/-- Algorithm 11's actual hash-based caller, from counter zero and the full
concrete SHAKE/integer expansion with the source B left absent. -/
def hashOpen {F : Type*} [Zero F] [DecidableEq F] (category : FieldRepresentation.Category)
    (tau kappa wpow : Nat) (key : BAVC.Key (FieldRepresentation.width category) tau (2 ^ kappa))
    (Topen : Nat) (counterEncoding : CounterEncoding)
    (digest : Bits (2 * FieldRepresentation.width category))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel grindingCount : Nat)
    (enough : wpow ≤ 8 * grindingCount) : Observation (FieldRepresentation.width category) tau kappa :=
  observe key Topen
    (fun counter => hashEvaluation category tau kappa wpow counterEncoding digest counter
      innerFuel grindingCount enough) encode outerFuel 0

end SDitH.Spec.PartialBLCRetry
