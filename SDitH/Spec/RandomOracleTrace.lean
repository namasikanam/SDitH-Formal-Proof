import SDitH.Spec.RandomOracleTrap

/-! The adaptive lazy-oracle experiment instrumented with, for every fresh
query, the table as it stood before that query. A trap predicate may then
depend on that earlier table, which is how a mask query can be related to
the commitment chain already present when the mask was sampled. Repeated
queries are answered from the table and are not recorded as fresh entries.
This is experiment instrumentation, not a change to the oracle's law. -/

namespace SDitH.Spec.RandomOracleTrace

open RandomOracleCollision
open scoped Classical
noncomputable section

structure Entry (Input Output : Type*) where
  before : Input → Option Output
  input : Input
  answer : Output

structure Result (Input Output State : Type*) where
  state : State
  table : Input → Option Output
  trace : List (Entry Input Output)

variable {Input Output State : Type*}
variable [Fintype Output] [Nonempty Output]

def record (table : Input → Option Output) (input : Input) (answer : Output)
    (trace : List (Entry Input Output)) : List (Entry Input Output) :=
  match table input with
  | some _ => trace
  | none => ⟨table, input, answer⟩ :: trace

def run (procedure : Procedure Input Output State) :
    Nat → State → (Input → Option Output) → List (Entry Input Output) → PMF (Result Input Output State)
  | 0, state, table, trace => PMF.pure ⟨state, table, trace⟩
  | fuel + 1, state, table, trace => (procedure.step state).bind fun action =>
      match action with
      | .stop => PMF.pure ⟨state, table, trace⟩
      | .query input next => (RandomOracle.query table input).bind fun result =>
          run procedure fuel (next result.1) result.2 (record table input result.1 trace)

def experiment (procedure : Procedure Input Output State) (budget : Nat) (initial : State) :
    PMF (Result Input Output State) :=
  run procedure budget initial (fun _ => none) []

/-- Some fresh query satisfied the trap, evaluated at the table before it. -/
def traceBad (bad : (Input → Option Output) → Input → Output → Bool) (trace : List (Entry Input Output)) : Bool :=
  trace.any fun entry => bad entry.before entry.input entry.answer

/-- Table growth: every stored entry persists. -/
def Extends (small large : Input → Option Output) : Prop :=
  ∀ input answer, small input = some answer → large input = some answer

/-- Every stored value has a fresh trace entry whose earlier table lacked it
and is extended by the final table, and every fresh entry persists. -/
def Traced (table : Input → Option Output) (trace : List (Entry Input Output)) : Prop :=
  (∀ input answer, table input = some answer →
    ∃ entry ∈ trace, entry.input = input ∧ entry.answer = answer ∧ entry.before input = none ∧ Extends entry.before table) ∧
  ∀ entry ∈ trace, table entry.input = some entry.answer

end
end SDitH.Spec.RandomOracleTrace
