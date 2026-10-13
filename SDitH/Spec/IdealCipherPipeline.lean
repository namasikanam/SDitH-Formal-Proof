import SDitH.Spec.IdealCipherJoint

/-! Two adaptive phases sharing one hidden cipher family and observation graph.
The second phase starts from a function of the first phase's returned state.
Early stopping transfers to that second phase; it does not discard verification. -/

namespace SDitH.Spec.IdealCipherPipeline

open IdealCipher
open scoped Classical
noncomputable section

variable {Key Block A B : Type*} [Fintype Key] [Fintype Block]

def runPosterior (first : Procedure Key Block A) (second : Procedure Key Block B)
    (k : Nat) (next : A → B) : Nat → A → World Key Block → PMF (Family Key Block × Result Key Block B)
  | 0, state, world => IdealCipherJoint.runPosterior second k (next state) world
  | q + 1, state, world => (first.step state).bind fun action =>
      match action with
      | .stop => IdealCipherJoint.runPosterior second k (next state) world
      | .query request advance => (query world request).bind fun result =>
          runPosterior first second k next q (advance result.1) result.2

def jointExperiment (first : Procedure Key Block A) (q : Nat) (initial : A)
    (second : Procedure Key Block B) (k : Nat) (next : A → B) : PMF (Family Key Block × Result Key Block B) :=
  (PMF.uniformOfFintype (Family Key Block)).bind fun family =>
    (runFixed first family q initial []).bind fun start =>
      (runFixed second family k (next start.state) start.history).map fun out => (family, out)

def experiment (first : Procedure Key Block A) (q : Nat) (initial : A)
    (second : Procedure Key Block B) (k : Nat) (next : A → B) : PMF (Result Key Block B) :=
  (jointExperiment first q initial second k next).map Prod.snd

end
end SDitH.Spec.IdealCipherPipeline
