import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

/-! Algorithm 5 and the domain prefixes of §3.2.3, printed pp. 16 and 21.
Bits are indexed least-significant-first, as required by LittleEndian(twk).
No hash or cipher security property is assumed in this module. -/

namespace SDitH.Spec.DomainSeparation

abbrev Bits (n : Nat) := Fin n → Bool
abbrev Byte := Fin 256
abbrev Tweak := Fin (2 ^ 24)

inductive Grinding where
  | hash
  | cipher
  deriving DecidableEq, Repr

/-- Algorithm 5. The top-bit assignments occur after the low-24-bit assignment
in the pseudocode, and therefore take priority in this functional expression.
All submitted instances have lambda ≥ 128; proofs below use the weaker bound 26. -/
def tweakSalt {lambda : Nat} (variant : Grinding) (salt : Bits lambda)
    (tweak : Tweak) (bit : Bool) : Bits lambda :=
  match variant with
  | .hash => fun j =>
      if j.val + 1 = lambda then bit
      else if j.val < 24 then tweak.val.testBit j.val else salt j
  | .cipher => fun j =>
      if j.val + 1 = lambda then false
      else if j.val + 2 = lambda then bit
      else if j.val < 24 then tweak.val.testBit j.val else salt j

/-- The one-byte domain prefix is prepended to the already serialized payload. -/
def hashInput (domain : Byte) (data : List Byte) : List Byte := domain :: data

def hashBavcInput (data : List Byte) : List Byte := hashInput 1 data
def hashAuxInput (data : List Byte) : List Byte := hashInput 2 data
def hashLinesInput (data : List Byte) : List Byte := hashInput 3 data
def hashPiopInput (data : List Byte) : List Byte := hashInput 4 data

end SDitH.Spec.DomainSeparation
