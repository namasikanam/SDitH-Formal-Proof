import SDitH.Spec.BLCBinding
import SDitH.Spec.HashCipherEvaluation

/-! The verifier's two hash calls, on the shared hash/cipher interpreter.
The intervening computation is an explicit oracle program, so its queries are
neither hidden in a pure function nor omitted from the budget. The source
constructor preserves Algorithm 12's three-field Hashlines payload. Its base
program is an explicit unresolved line-21 implementation boundary. -/

namespace SDitH.Spec.BLCHashChain

open BAVC HashCipherProgram

abbrev ChainProgram (lambda : Nat) (Key Block A : Type*) := Program (List Bool) (Digest lambda) Key Block A

structure Result (lambda : Nat) where
  auxiliary : Digest lambda
  tail : List Bool
  lines : Digest lambda

variable {lambda : Nat} {Key Block : Type*}

def auxQuery (root : Digest lambda) (tail : List Bool) : List Bool :=
  byteBits 2 ++ (List.ofFn root ++ tail)

def linesQuery (auxiliary : Digest lambda) (tail : List Bool) : List Bool :=
  byteBits 3 ++ (List.ofFn auxiliary ++ tail)

def program (root : Digest lambda) (auxiliaryTail : List Bool)
    (middle : Digest lambda → ChainProgram lambda Key Block (List Bool)) : ChainProgram lambda Key Block (Result lambda) :=
  .hash (auxQuery root auxiliaryTail) fun auxiliary =>
    HashCipherProgram.bind (middle auxiliary) fun tail =>
      .hash (linesQuery auxiliary tail) fun lines => .done ⟨auxiliary, tail, lines⟩

def partialProgram {Error : Type*} (root : Digest lambda) (auxiliaryTail : List Bool)
    (middle : Digest lambda → ChainProgram lambda Key Block (Except Error (List Bool))) :
    ChainProgram lambda Key Block (Except Error (Result lambda)) :=
  .hash (auxQuery root auxiliaryTail) fun auxiliary =>
    HashCipherProgram.bind (middle auxiliary) fun result =>
      match result with
      | .error cause => .done (.error cause)
      | .ok tail => .hash (linesQuery auxiliary tail) fun lines => .done (.ok ⟨auxiliary, tail, lines⟩)

def sourceTail {tau kappa s wit rnd : Nat} (encoding : ConcreteBLC.Serialization tau kappa s)
    (corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2) : List Bool :=
  (List.ofFn fun j => encoding.vector (corrections j)).flatten

def sourceMiddle (category : FieldRepresentation.Category) {tau kappa s : Nat}
    (encoding : ConcreteBLC.Serialization tau kappa s) (plain : Fin s → ZMod 2)
    (base : Digest (FieldRepresentation.width category) → ChainProgram (FieldRepresentation.width category) Key Block
      (Fin s → Fin tau → Fin kappa → ZMod 2))
    (auxiliary : Digest (FieldRepresentation.width category)) : ChainProgram (FieldRepresentation.width category) Key Block (List Bool) :=
  HashCipherProgram.bind (base auxiliary) fun value => .done (encoding.vector plain ++ encoding.base value)

def sourceProgram (category : FieldRepresentation.Category) {tau kappa s wit rnd : Nat}
    (encoding : ConcreteBLC.Serialization tau kappa s) (root : Digest (FieldRepresentation.width category))
    (corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2) (plain : Fin s → ZMod 2)
    (base : Digest (FieldRepresentation.width category) → ChainProgram (FieldRepresentation.width category) Key Block
      (Fin s → Fin tau → Fin kappa → ZMod 2)) : ChainProgram (FieldRepresentation.width category) Key Block (Result (FieldRepresentation.width category)) :=
  program root (sourceTail encoding corrections) (sourceMiddle category encoding plain base)

def partialSourceMiddle {Error : Type*} (category : FieldRepresentation.Category) {tau kappa s : Nat}
    (encoding : ConcreteBLC.Serialization tau kappa s) (plain : Fin s → ZMod 2)
    (base : Digest (FieldRepresentation.width category) → ChainProgram (FieldRepresentation.width category) Key Block
      (Except Error (Fin s → Fin tau → Fin kappa → ZMod 2)))
    (auxiliary : Digest (FieldRepresentation.width category)) : ChainProgram (FieldRepresentation.width category) Key Block (Except Error (List Bool)) :=
  HashCipherProgram.bind (base auxiliary) fun result =>
    .done (result.map (fun value => encoding.vector plain ++ encoding.base value))

def partialSourceProgram {Error : Type*} (category : FieldRepresentation.Category) {tau kappa s wit rnd : Nat}
    (encoding : ConcreteBLC.Serialization tau kappa s) (root : Digest (FieldRepresentation.width category))
    (corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2) (plain : Fin s → ZMod 2)
    (base : Digest (FieldRepresentation.width category) → ChainProgram (FieldRepresentation.width category) Key Block
      (Except Error (Fin s → Fin tau → Fin kappa → ZMod 2))) :
    ChainProgram (FieldRepresentation.width category) Key Block (Except Error (Result (FieldRepresentation.width category))) :=
  partialProgram root (sourceTail encoding corrections) (partialSourceMiddle category encoding plain base)

end SDitH.Spec.BLCHashChain
