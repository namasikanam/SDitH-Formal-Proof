import SDitH.Spec.RandomOracle

/-! Adaptive collision experiment for the same lazy random oracle used by the
signature game. The budget counts every query made by this whole procedure,
including repeats; integration must account for honest and adversarial calls.
The private table/log are experiment instrumentation, not procedure arguments.
This does not postulate collision resistance or model SHAKE as random. -/

namespace SDitH.Spec.RandomOracleCollision

open scoped Classical
noncomputable section

inductive Action (Input Output State : Type*) where
  | stop
  | query (input : Input) (next : Output → State)

structure Procedure (Input Output State : Type*) where
  step : State → PMF (Action Input Output State)

structure Result (Input Output State : Type*) where
  state : State
  table : Input → Option Output
  history : List (Input × Output)
  collided : Bool

variable {Input Output State : Type*}
variable [Fintype Output] [Nonempty Output]

/-- A repeat is not a collision. Only a newly sampled answer can raise this
flag, and it is compared against all earlier answers, including repetitions. -/
def freshHit (table : Input → Option Output) (history : List (Input × Output))
    (input : Input) (answer : Output) : Bool :=
  (table input).isNone && history.any (fun old => decide (old.2 = answer))

def run (procedure : Procedure Input Output State) :
    Nat → State → (Input → Option Output) → List (Input × Output) → PMF (Result Input Output State)
  | 0, state, table, history => PMF.pure ⟨state, table, history, false⟩
  | fuel + 1, state, table, history => (procedure.step state).bind fun action =>
      match action with
      | .stop => PMF.pure ⟨state, table, history, false⟩
      | .query input next => (RandomOracle.query table input).bind fun result =>
          (run procedure fuel (next result.1) result.2 ((input, result.1) :: history)).map
            (fun out => { out with collided := freshHit table history input result.1 || out.collided })

def experiment (procedure : Procedure Input Output State) (budget : Nat) (initial : State) :
    PMF (Result Input Output State) :=
  run procedure budget initial (fun _ => none) []

/-- Exact correspondence of stored entries and observed queries. Repeated
queries may occur in the list. This is an invariant to prove, not a state field. -/
def Recorded (table : Input → Option Output) (history : List (Input × Output)) : Prop :=
  ∀ input answer, table input = some answer ↔ (input, answer) ∈ history

def CollisionFree (table : Input → Option Output) : Prop :=
  ∀ left right answer, table left = some answer → table right = some answer → left = right

/-- A pair succeeds only when both distinct inputs really occur in the final
table with the same answer. Unqueried guesses do not satisfy this event. -/
def storedCollision (pair : Input × Input) (out : Result Input Output State) : Bool :=
  decide (pair.1 ≠ pair.2 ∧ ∃ answer, out.table pair.1 = some answer ∧ out.table pair.2 = some answer)

/-- A final selector may inspect the complete instrumented result. Success
still requires two distinct inputs actually queried to this shared oracle. -/
def selectionWins (pick : Result Input Output State → Option (Input × Input))
    (out : Result Input Output State) : Bool :=
  match pick out with
  | none => false
  | some pair => storedCollision pair out

end
end SDitH.Spec.RandomOracleCollision
