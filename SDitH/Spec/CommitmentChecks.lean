import Mathlib.Data.List.Basic

/-!
Literal, explicitly delimited fragments of Algorithms 9, 10, and 12.
These definitions do not purport to specify the rest of the algorithms.
-/

namespace SDitH.Spec

inductive SiblingAction where
  | skip
  | dropSibling
  | readSibling
  | reject
  deriving DecidableEq, Repr

/-- Algorithm 9 lines 8–15, after the dequeue on line 7.
`queueLength` is the remaining queue length and `pathBits` the remaining path
length. When `queueLength ≥ 2`, the head exists, so `nextNode` is meaningful. -/
def reconstructSiblingAction (queueLength node nextNode pathBits Topen lambda : Nat) :
    SiblingAction :=
  if queueLength ≥ 2 then
    if nextNode = Nat.xor node 1 then .dropSibling
    else if pathBits < Topen * lambda then .readSibling
    else .reject
  else .skip

/-- The path length after Algorithm 8 line 17. -/
def paddedPathBits (Topen lambda : Nat) : Nat := Topen * lambda

/-- Algorithm 10 line 24: the serialized components after the domain byte.
Each argument is an already serialized component. This definition makes no
unstated claim about the serialization format itself. -/
def commitLinesInput {Byte : Type*} (haux plain base deltaWitness : List Byte) : List Byte :=
  haux ++ plain ++ base ++ deltaWitness

/-- Algorithm 12 line 26: `deltaWitness` is absent in the printed algorithm. -/
def reconstructLinesInput {Byte : Type*} (haux plain base : List Byte) : List Byte :=
  haux ++ plain ++ base

end SDitH.Spec
