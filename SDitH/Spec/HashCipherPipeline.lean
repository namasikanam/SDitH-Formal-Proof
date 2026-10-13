import SDitH.Spec.HashCipher

/-! Sequential adaptive phases in the shared hash/cipher model. The second
phase starts even when the first stops early. It receives the selected state;
the interpreter retains the same hidden family, table and both histories.
Earlier hash collisions are retained in the final flag. -/

namespace SDitH.Spec.HashCipherPipeline

open HashCipher
open scoped Classical
noncomputable section

variable {Input Digest Key Block A B : Type*}
variable [Fintype Digest] [Nonempty Digest]

def runFixed (first : Procedure Input Digest Key Block A) (second : Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) (family : IdealCipher.Family Key Block) (q : Nat) (state : A)
    (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (IdealCipher.Entry Key Block)) : PMF (Result Input Digest Key Block B) :=
  (HashCipher.runFixed first family q state table hashes ciphers).bind fun start =>
    (HashCipher.runFixed second family k (next start.state) start.hashTable start.hashHistory start.cipherHistory).map
      (markHash start.hashCollided)

variable [Fintype Key] [Fintype Block]

def runPosterior (first : Procedure Input Digest Key Block A) (second : Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) : Nat → A → (Input → Option Digest) → List (Input × Digest) →
      IdealCipher.World Key Block → PMF (IdealCipher.Family Key Block × Result Input Digest Key Block B)
  | 0, state, table, hashes, world => HashCipher.runPosterior second k (next state) table hashes world
  | q + 1, state, table, hashes, world => (first.step state).bind fun action =>
      match action with
      | .stop => HashCipher.runPosterior second k (next state) table hashes world
      | .hash input advance => (RandomOracle.query table input).bind fun result =>
          (runPosterior first second k next q (advance result.1) result.2 ((input, result.1) :: hashes) world).map
            (markJoint (RandomOracleCollision.freshHit table hashes input result.1))
      | .cipher request advance => (IdealCipher.query world request).bind fun result =>
          runPosterior first second k next q (advance result.1) table hashes result.2

def jointExperiment (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B) :
    PMF (IdealCipher.Family Key Block × Result Input Digest Key Block B) :=
  (PMF.uniformOfFintype (IdealCipher.Family Key Block)).bind fun family =>
    (runFixed first second k next family q initial (fun _ => none) [] []).map fun out => (family, out)

def experiment (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B) :
    PMF (Result Input Digest Key Block B) :=
  (jointExperiment first q initial second k next).map Prod.snd

end
end SDitH.Spec.HashCipherPipeline
