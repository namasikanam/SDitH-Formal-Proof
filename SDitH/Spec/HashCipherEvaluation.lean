import SDitH.Spec.HashCipherProgram

/-! Evaluation against the actual final hash table and cipher graph. Each
constructor requires its query's stored answer or graph entry. Operational
execution must establish this relation; it is not an assumed coverage property. -/

namespace SDitH.Spec.HashCipherEvaluation

open HashCipherProgram

inductive Evaluates {Input Digest Key Block A : Type*} (family : IdealCipher.Family Key Block)
    (table : Input → Option Digest) (ciphers : List (IdealCipher.Entry Key Block)) :
    Program Input Digest Key Block A → A → Prop where
  | done (value : A) : Evaluates family table ciphers (.done value) value
  | hash (input : Input) (next : Digest → Program Input Digest Key Block A) (answer : Digest) (value : A)
      (stored : table input = some answer) (tail : Evaluates family table ciphers (next answer) value) :
      Evaluates family table ciphers (.hash input next) value
  | cipher (request : IdealCipher.Query Key Block) (next : Block → Program Input Digest Key Block A) (value : A)
      (recorded : IdealCipher.entry request (IdealCipher.answer family request) ∈ ciphers)
      (tail : Evaluates family table ciphers (next (IdealCipher.answer family request)) value) :
      Evaluates family table ciphers (.cipher request next) value

end SDitH.Spec.HashCipherEvaluation
