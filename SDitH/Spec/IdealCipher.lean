import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Perm

/-! An adaptive ideal-cipher experiment. A keyed permutation family is drawn
once; encryption and decryption use its forward and inverse maps. A separate
posterior interpreter samples only families compatible with the observations.
Its equivalence to the once-sampled experiment is a proof obligation, not an
assumption. This is a probability model, not security of AES or Rijndael. -/

namespace SDitH.Spec.IdealCipher

open scoped Classical
noncomputable section

abbrev Family (Key Block : Type*) := Key → Equiv.Perm Block

structure Entry (Key Block : Type*) where
  key : Key
  input : Block
  output : Block

inductive Query (Key Block : Type*) where
  | encrypt (key : Key) (input : Block)
  | decrypt (key : Key) (output : Block)

variable {Key Block State : Type*}

def answer (family : Family Key Block) : Query Key Block → Block
  | .encrypt key input => family key input
  | .decrypt key output => (family key).symm output

def entry : Query Key Block → Block → Entry Key Block
  | .encrypt key input, output => ⟨key, input, output⟩
  | .decrypt key output, input => ⟨key, input, output⟩

def Matches (family : Family Key Block) (history : List (Entry Key Block)) : Prop :=
  ∀ e ∈ history, family e.key e.input = e.output

/-- Nonempty compatibility is a structural well-formedness condition. It
ensures conditional sampling exists, without asserting any security property. -/
structure World (Key Block : Type*) where
  history : List (Entry Key Block)
  possible : ∃ family : Family Key Block, Matches family history

def empty : World Key Block := ⟨[], fun key => Equiv.refl Block, by simp [Matches]⟩

abbrev Candidates (world : World Key Block) := {family : Family Key Block // Matches family world.history}

instance candidates_nonempty (world : World Key Block) : Nonempty (Candidates world) := by
  obtain ⟨family, h⟩ := world.possible
  exact ⟨⟨family, h⟩⟩

def observe (world : World Key Block) (query : Query Key Block) (value : Block)
    (h : ∃ family : Family Key Block, Matches family world.history ∧ answer family query = value) : World Key Block :=
  ⟨entry query value :: world.history, by
    obtain ⟨family, hf, ha⟩ := h
    refine ⟨family, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · cases query with
      | encrypt key input => exact ha
      | decrypt key output =>
        change family key value = output
        rw [← ha]
        exact (family key).apply_symm_apply output
    · exact hf e he⟩

variable [Fintype Key] [Fintype Block]

def query (world : World Key Block) (request : Query Key Block) : PMF (Block × World Key Block) :=
  (PMF.uniformOfFintype (Candidates world)).map fun family =>
    (answer family.val request, observe world request (answer family.val request) ⟨family.val, family.property, rfl⟩)

inductive Action (Key Block State : Type*) where
  | stop
  | query (request : Query Key Block) (next : Block → State)

structure Procedure (Key Block State : Type*) where
  step : State → PMF (Action Key Block State)

structure Result (Key Block State : Type*) where
  state : State
  history : List (Entry Key Block)

/-- Execution against one fixed, hidden family. There is no fresh sampling
when a query repeats, switches direction, or changes key. -/
def runFixed (procedure : Procedure Key Block State) (family : Family Key Block) :
    Nat → State → List (Entry Key Block) → PMF (Result Key Block State)
  | 0, state, history => PMF.pure ⟨state, history⟩
  | fuel + 1, state, history => (procedure.step state).bind fun action =>
      match action with
      | .stop => PMF.pure ⟨state, history⟩
      | .query request next =>
          let value := answer family request
          runFixed procedure family fuel (next value) (entry request value :: history)

def runPosterior (procedure : Procedure Key Block State) :
    Nat → State → World Key Block → PMF (Result Key Block State)
  | 0, state, world => PMF.pure ⟨state, world.history⟩
  | fuel + 1, state, world => (procedure.step state).bind fun action =>
      match action with
      | .stop => PMF.pure ⟨state, world.history⟩
      | .query request next => (query world request).bind fun result =>
          runPosterior procedure fuel (next result.1) result.2

def experimentFixed (procedure : Procedure Key Block State) (budget : Nat) (initial : State) : PMF (Result Key Block State) :=
  (PMF.uniformOfFintype (Family Key Block)).bind fun family => runFixed procedure family budget initial []

def experimentPosterior (procedure : Procedure Key Block State) (budget : Nat) (initial : State) : PMF (Result Key Block State) :=
  runPosterior procedure budget initial empty

end
end SDitH.Spec.IdealCipher
