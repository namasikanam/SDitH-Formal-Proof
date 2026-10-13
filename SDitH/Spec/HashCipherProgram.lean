import SDitH.Spec.HashCipher
import SDitH.Spec.IdealCipherProgram

/-! Finite programs for the shared hash/cipher interpreter. The lifts preserve
the already specified source hash and seed-query programs; they do not replace
the hash table or cipher family at service boundaries. -/

namespace SDitH.Spec.HashCipherProgram

inductive Program (Input Digest Key Block A : Type*) where
  | done (value : A)
  | hash (input : Input) (next : Digest → Program Input Digest Key Block A)
  | cipher (request : IdealCipher.Query Key Block) (next : Block → Program Input Digest Key Block A)

variable {Input Digest Key Block A B : Type*}

def bind (program : Program Input Digest Key Block A) (next : A → Program Input Digest Key Block B) : Program Input Digest Key Block B :=
  match program with
  | .done value => next value
  | .hash input tail => .hash input (fun answer => bind (tail answer) next)
  | .cipher request tail => .cipher request (fun answer => bind (tail answer) next)

def liftHash : OracleProgram.Program Input Digest A → Program Input Digest Key Block A
  | .done value => .done value
  | .query input next => .hash input (fun answer => liftHash (next answer))

def liftCipher : OracleProgram.Program (IdealCipher.Query Key Block) Block A → Program Input Digest Key Block A
  | .done value => .done value
  | .query request next => .cipher request (fun answer => liftCipher (next answer))

def Bounded : Nat → Program Input Digest Key Block A → Prop
  | _, .done _ => True
  | 0, .hash _ _ => False
  | 0, .cipher _ _ => False
  | n + 1, .hash _ next => ∀ answer, Bounded n (next answer)
  | n + 1, .cipher _ next => ∀ answer, Bounded n (next answer)

noncomputable def procedure : HashCipher.Procedure Input Digest Key Block (Program Input Digest Key Block A) where
  step program := PMF.pure (match program with
    | .done _ => .stop
    | .hash input next => .hash input next
    | .cipher request next => .cipher request next)

def liftHashResult (ciphers : List (IdealCipher.Entry Key Block))
    (out : RandomOracleCollision.Result Input Digest (OracleProgram.Program Input Digest A)) :
    HashCipher.Result Input Digest Key Block (Program Input Digest Key Block A) :=
  ⟨liftHash out.state, out.table, out.history, ciphers, out.collided⟩

def liftCipherResult (table : Input → Option Digest) (hashes : List (Input × Digest))
    (out : IdealCipher.Result Key Block (OracleProgram.Program (IdealCipher.Query Key Block) Block A)) :
    HashCipher.Result Input Digest Key Block (Program Input Digest Key Block A) :=
  ⟨liftCipher out.state, table, hashes, out.history, false⟩

end SDitH.Spec.HashCipherProgram
