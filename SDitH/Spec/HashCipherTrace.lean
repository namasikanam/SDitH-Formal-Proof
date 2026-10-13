import SDitH.Spec.HashCipher
import SDitH.Spec.RandomOracleMention

/-! The shared hash/cipher execution instrumented with the fresh-query log
of `RandomOracleTrace`: every fresh hash query records the table before
it. Cipher queries leave the hash table and the log unchanged. Forgetting
the log gives exactly the existing shared execution, so earlier results
about the shared model transfer, while the log carries the trap bounds. -/

namespace SDitH.Spec.HashCipherTrace

open HashCipher RandomOracleTrace RandomOracleCollision
open scoped Classical
noncomputable section

structure Result (Input Digest Key Block State : Type*) where
  state : State
  hashTable : Input → Option Digest
  hashHistory : List (Input × Digest)
  cipherHistory : List (IdealCipher.Entry Key Block)
  hashCollided : Bool
  trace : List (Entry Input Digest)

variable {Input Digest Key Block State : Type*}

def forget (out : Result Input Digest Key Block State) : HashCipher.Result Input Digest Key Block State :=
  ⟨out.state, out.hashTable, out.hashHistory, out.cipherHistory, out.hashCollided⟩

def mark (hit : Bool) (out : Result Input Digest Key Block State) : Result Input Digest Key Block State :=
  { out with hashCollided := hit || out.hashCollided }

variable [Fintype Digest] [Nonempty Digest]

def runFixed (procedure : Procedure Input Digest Key Block State) (family : IdealCipher.Family Key Block) :
    Nat → State → (Input → Option Digest) → List (Input × Digest) → List (IdealCipher.Entry Key Block) →
      List (Entry Input Digest) → PMF (Result Input Digest Key Block State)
  | 0, state, table, hashes, ciphers, log => PMF.pure ⟨state, table, hashes, ciphers, false, log⟩
  | fuel + 1, state, table, hashes, ciphers, log => (procedure.step state).bind fun action =>
      match action with
      | .stop => PMF.pure ⟨state, table, hashes, ciphers, false, log⟩
      | .hash input next => (RandomOracle.query table input).bind fun result =>
          (runFixed procedure family fuel (next result.1) result.2 ((input, result.1) :: hashes) ciphers
            (record table input result.1 log)).map (mark (freshHit table hashes input result.1))
      | .cipher request next =>
          runFixed procedure family fuel (next (IdealCipher.answer family request)) table hashes
            (IdealCipher.entry request (IdealCipher.answer family request) :: ciphers) log

variable [Fintype Key] [Fintype Block]

def jointExperiment (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State) :
    PMF (IdealCipher.Family Key Block × Result Input Digest Key Block State) :=
  (PMF.uniformOfFintype (IdealCipher.Family Key Block)).bind fun family =>
    (runFixed procedure family budget initial (fun _ => none) [] [] []).map fun out => (family, out)

end
end SDitH.Spec.HashCipherTrace
