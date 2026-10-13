import SDitH.Spec.BAVCOpening
import Mathlib.Algebra.Field.Defs

/-! Algorithm 11 and Algorithm 12 lines 3–7, printed pp. 29–30.

The evaluator and index encoding are explicit function inputs at their source
subroutine boundaries. No relation between raw-index and Gray encodings is
silently assumed. Counter overflow has no stated source behavior and is marked
undefined, rather than choosing wraparound, unbounded arithmetic, or an abort.
Finite observations report pending execution; they do not assert termination.
-/

namespace SDitH.Spec.BLCRetry

open DomainSeparation

abbrev Counter := Fin (2 ^ 32)

structure Challenge (tau N wpow : Nat) where
  hidden : Fin tau → Fin N
  grinding : Bits wpow

def GrindingPassed {wpow : Nat} (bits : Bits wpow) : Prop := ∀ j, bits j = false

instance {wpow : Nat} (bits : Bits wpow) : Decidable (GrindingPassed bits) :=
  inferInstanceAs (Decidable (∀ j, bits j = false))

inductive Attempt (α : Type*) where
  | retry
  | ready (opening : α)
  | undefinedOpening (error : BAVC.OpeningError)

/-- Lines 3–6. The actual Algorithm-8 opening is evaluated on every attempt,
including attempts with failed grinding, as in the printed order. -/
def attempt {F : Type*} [Zero F] [DecidableEq F] {lambda tau N wpow : Nat}
    (key : BAVC.Key lambda tau N) (Topen : Nat)
    (expand : Counter → Challenge tau N wpow) (encode : (Fin tau → Fin N) → F)
    (ctr : Counter) : Attempt (BAVC.Opening lambda tau) :=
  let challenge := expand ctr
  let deltaInv := encode challenge.hidden
  match BAVC.openCommitment key challenge.hidden Topen with
  | .error .boundExceeded => .retry
  | .error other => .undefinedOpening other
  | .ok opening =>
    if GrindingPassed challenge.grinding ∧ deltaInv ≠ 0 then .ready opening else .retry

inductive Fault where
  | counterOverflow
  | undefinedOpening (error : BAVC.OpeningError)
  deriving DecidableEq, Repr

inductive Step (α : Type*) where
  | again (counter : Counter)
  | done (counter : Counter) (opening : α)
  | undefined (fault : Fault)

/-- Line 7 on its specified 32-bit domain. The overflow tag is an unresolved
source operation, not an invented source rejection rule. -/
def advance {α : Type*} (ctr : Counter) : Step α :=
  if h : ctr.val + 1 < 2 ^ 32 then .again ⟨ctr.val + 1, h⟩
  else .undefined .counterOverflow

def step {α : Type*} (evaluate : Counter → Attempt α) (ctr : Counter) : Step α :=
  match evaluate ctr with
  | .retry => advance ctr
  | .ready opening => .done ctr opening
  | .undefinedOpening err => .undefined (.undefinedOpening err)

inductive Observation (α : Type*) where
  /-- Execution has not been observed far enough to report its outcome. -/
  | pending (counter : Counter)
  | returned (counter : Counter) (opening : α)
  | undefined (fault : Fault)

/-- Observe at most `fuel` attempts of lines 2–10, preserving unfinished and
undefined outcomes separately. The algorithm itself has no fuel-based abort. -/
def observe {α : Type*} (evaluate : Counter → Attempt α) : Nat → Counter → Observation α
  | 0, ctr => .pending ctr
  | fuel + 1, ctr =>
    match step evaluate ctr with
    | .again next => observe evaluate fuel next
    | .done result opening => .returned result opening
    | .undefined fault => .undefined fault

/-- Algorithm 11 starts at counter zero. -/
def openRandomEvaluation {F : Type*} [Zero F] [DecidableEq F]
    {lambda tau N wpow : Nat} (key : BAVC.Key lambda tau N) (Topen : Nat)
    (expand : Counter → Challenge tau N wpow) (encode : (Fin tau → Fin N) → F)
    (fuel : Nat) : Observation (BAVC.Opening lambda tau) :=
  observe (attempt key Topen expand encode) fuel 0

/-- Algorithm 12's header check. Nothing is asserted here about its later
reconstruction or hash calculations. -/
def checkEvaluationHeader {F : Type*} [Field F] [DecidableEq F] {tau N wpow : Nat}
    (expand : Counter → Challenge tau N wpow) (encode : (Fin tau → Fin N) → F)
    (ctr : Counter) : Option F :=
  let challenge := expand ctr
  let deltaInv := encode challenge.hidden
  if GrindingPassed challenge.grinding ∧ deltaInv ≠ 0 then some deltaInv⁻¹ else none

end SDitH.Spec.BLCRetry
