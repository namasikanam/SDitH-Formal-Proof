import SDitH.Spec.IdealCipher

/-! Joint laws retaining the hidden ideal-cipher family for a terminal test.
The procedure still sees only its state and each requested answer. In the
posterior interpreter the family is sampled only after the procedure stops. -/

namespace SDitH.Spec.IdealCipherJoint

open IdealCipher
open scoped Classical
noncomputable section

variable {Key Block State : Type*} [Fintype Key] [Fintype Block]

def finish (state : State) (world : World Key Block) : PMF (Family Key Block × Result Key Block State) :=
  (PMF.uniformOfFintype (Candidates world)).map fun family => (family.val, ⟨state, world.history⟩)

def runPosterior (procedure : Procedure Key Block State) :
    Nat → State → World Key Block → PMF (Family Key Block × Result Key Block State)
  | 0, state, world => finish state world
  | fuel + 1, state, world => (procedure.step state).bind fun action =>
      match action with
      | .stop => finish state world
      | .query request next => (query world request).bind fun result =>
          runPosterior procedure fuel (next result.1) result.2

def experiment (procedure : Procedure Key Block State) (budget : Nat) (initial : State) :
    PMF (Family Key Block × Result Key Block State) :=
  runPosterior procedure budget initial empty

end
end SDitH.Spec.IdealCipherJoint
