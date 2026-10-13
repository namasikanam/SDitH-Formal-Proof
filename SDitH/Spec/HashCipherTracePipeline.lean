import SDitH.Spec.HashCipherTrace
import SDitH.Spec.HashCipherPipeline

/-! Two adaptive phases of the instrumented shared execution: the second
phase starts from the first's selected state with the same family, table,
histories and fresh-query log, even after early stopping. Forgetting the
log gives exactly the existing two-phase execution. -/

namespace SDitH.Spec.HashCipherTracePipeline

open HashCipher HashCipherTrace RandomOracleTrace
open scoped Classical
noncomputable section

variable {Input Digest Key Block A B : Type*} [Fintype Digest] [Nonempty Digest]

def runFixed (first : Procedure Input Digest Key Block A) (second : Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) (family : IdealCipher.Family Key Block) (q : Nat) (state : A)
    (table : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (IdealCipher.Entry Key Block))
    (log : List (Entry Input Digest)) : PMF (HashCipherTrace.Result Input Digest Key Block B) :=
  (HashCipherTrace.runFixed first family q state table hashes ciphers log).bind fun start =>
    (HashCipherTrace.runFixed second family k (next start.state) start.hashTable start.hashHistory
      start.cipherHistory start.trace).map (mark start.hashCollided)

variable [Fintype Key] [Fintype Block]

def jointExperiment (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B) :
    PMF (IdealCipher.Family Key Block × HashCipherTrace.Result Input Digest Key Block B) :=
  (PMF.uniformOfFintype (IdealCipher.Family Key Block)).bind fun family =>
    (runFixed first second k next family q initial (fun _ => none) [] [] []).map fun out => (family, out)

end
end SDitH.Spec.HashCipherTracePipeline
