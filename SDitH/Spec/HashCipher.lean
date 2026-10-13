import SDitH.Spec.RandomOracleCollision
import SDitH.Spec.IdealCipher
import SDitH.Spec.IdealCipherPairCollision

/-! A shared ROM/ICM execution. Hash queries use one lazy table; forward and
inverse cipher queries use one hidden family. The procedure can adaptively
switch between services. Fresh hash draws are defined inside this execution,
not supplied as an independence or security premise. The budget counts both
kinds of query and stopping actions, not machine time. -/

namespace SDitH.Spec.HashCipher

open scoped Classical
noncomputable section

inductive Action (Input Digest Key Block State : Type*) where
  | stop
  | hash (input : Input) (next : Digest → State)
  | cipher (request : IdealCipher.Query Key Block) (next : Block → State)

structure Procedure (Input Digest Key Block State : Type*) where
  step : State → PMF (Action Input Digest Key Block State)

structure Result (Input Digest Key Block State : Type*) where
  state : State
  hashTable : Input → Option Digest
  hashHistory : List (Input × Digest)
  cipherHistory : List (IdealCipher.Entry Key Block)
  hashCollided : Bool

variable {Input Digest Key Block State Tag : Type*}

def hashView (out : Result Input Digest Key Block State) : RandomOracleCollision.Result Input Digest State :=
  ⟨out.state, out.hashTable, out.hashHistory, out.hashCollided⟩

def markHash (hit : Bool) (out : Result Input Digest Key Block State) : Result Input Digest Key Block State :=
  { out with hashCollided := hit || out.hashCollided }

def markJoint (hit : Bool) (joint : IdealCipher.Family Key Block × Result Input Digest Key Block State) :=
  (joint.1, markHash hit joint.2)

variable [Fintype Digest] [Nonempty Digest]

def runFixed (procedure : Procedure Input Digest Key Block State) (family : IdealCipher.Family Key Block) :
    Nat → State → (Input → Option Digest) → List (Input × Digest) → List (IdealCipher.Entry Key Block) →
      PMF (Result Input Digest Key Block State)
  | 0, state, table, hashes, ciphers => PMF.pure ⟨state, table, hashes, ciphers, false⟩
  | fuel + 1, state, table, hashes, ciphers => (procedure.step state).bind fun action =>
      match action with
      | .stop => PMF.pure ⟨state, table, hashes, ciphers, false⟩
      | .hash input next => (RandomOracle.query table input).bind fun result =>
          (runFixed procedure family fuel (next result.1) result.2 ((input, result.1) :: hashes) ciphers).map
            (markHash (RandomOracleCollision.freshHit table hashes input result.1))
      | .cipher request next =>
          runFixed procedure family fuel (next (IdealCipher.answer family request)) table hashes
            (IdealCipher.entry request (IdealCipher.answer family request) :: ciphers)

variable [Fintype Key] [Fintype Block]

def finish (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (world : IdealCipher.World Key Block) : PMF (IdealCipher.Family Key Block × Result Input Digest Key Block State) :=
  (PMF.uniformOfFintype (IdealCipher.Candidates world)).map fun family =>
    (family.val, ⟨state, table, hashes, world.history, false⟩)

def runPosterior (procedure : Procedure Input Digest Key Block State) :
    Nat → State → (Input → Option Digest) → List (Input × Digest) → IdealCipher.World Key Block →
      PMF (IdealCipher.Family Key Block × Result Input Digest Key Block State)
  | 0, state, table, hashes, world => finish state table hashes world
  | fuel + 1, state, table, hashes, world => (procedure.step state).bind fun action =>
      match action with
      | .stop => finish state table hashes world
      | .hash input next => (RandomOracle.query table input).bind fun result =>
          (runPosterior procedure fuel (next result.1) result.2 ((input, result.1) :: hashes) world).map
            (markJoint (RandomOracleCollision.freshHit table hashes input result.1))
      | .cipher request next => (IdealCipher.query world request).bind fun result =>
          runPosterior procedure fuel (next result.1) table hashes result.2

def jointExperiment (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State) :
    PMF (IdealCipher.Family Key Block × Result Input Digest Key Block State) :=
  (PMF.uniformOfFintype (IdealCipher.Family Key Block)).bind fun family =>
    (runFixed procedure family budget initial (fun _ => none) [] []).map fun out => (family, out)

def experiment (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State) :
    PMF (Result Input Digest Key Block State) :=
  (jointExperiment procedure budget initial).map Prod.snd

def cipherEvent (project : Block → Tag) (companion : Block → Block)
    (joint : IdealCipher.Family Key Block × Result Input Digest Key Block State) : Bool :=
  decide (IdealCipherPairCollision.Witnessed project companion joint.1 joint.2.cipherHistory)

def combinedEvent (project : Block → Tag) (companion : Block → Block)
    (joint : IdealCipher.Family Key Block × Result Input Digest Key Block State) : Bool :=
  joint.2.hashCollided || cipherEvent project companion joint

end
end SDitH.Spec.HashCipher
