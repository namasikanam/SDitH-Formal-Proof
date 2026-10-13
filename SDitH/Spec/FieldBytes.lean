import SDitH.Spec.FieldRepresentation
import SDitH.Spec.ByteSampling

/-! The representation boundary of SampleFieldElements, printed p. 18.
The PDF gives a bit decomposition for binary sampling, but says only that a
pack of lambda/8 bytes is a field element for extension sampling. Table 2
specifies the polynomial basis, not the byte-to-coefficient ordering.

This module therefore gives a family of polynomial-basis decoders with an
explicit ordering argument. It does not select an undocumented wire format or
assert that an external implementation uses one of these orders. Connecting a
concrete serializer to this family remains a human correspondence obligation.
-/

namespace SDitH.Spec.FieldBytes

open DomainSeparation FieldRepresentation

def byteCount (category : Category) : Nat := width category / 8

/-- Which byte and which little-endian bit supplies coefficient i. -/
abbrev ByteOrder (category : Category) :=
  Fin (width category) ≃ Fin (byteCount category) × Fin 8

def bitCoefficient (bit : Bool) : ZMod 2 := if bit then 1 else 0

def byteCoefficients (byte : Byte) : Fin 8 → ZMod 2 :=
  fun j => bitCoefficient (byte.val.testBit j.val)

def coefficients (category : Category) (order : ByteOrder category)
    (bytes : Fin (byteCount category) → Byte) : Fin (width category) → ZMod 2 :=
  fun i => byteCoefficients (bytes (order i).1) (order i).2

/-- Decode with the supplied ordering into the exact submitted quotient. -/
noncomputable def decode (category : Category) (order : ByteOrder category)
    (bytes : Fin (byteCount category) → Byte) : QuotientRing category :=
  encodeCoefficients category (coefficients category order bytes)

noncomputable def sample (category : Category) (order : ByteOrder category)
    (src : ByteSampling.Reader) (n count : Nat) (enough : n * byteCount category ≤ count) :
    ByteSampling.Result (Fin n → QuotientRing category) :=
  ByteSampling.sampleExtension src (byteCount category) n count enough (decode category order)

noncomputable def expandBatching (category : Category) (order : ByteOrder category)
    (xof : Nat → Byte) (gammaCount w count₁ count₂ : Nat)
    (enough₁ : gammaCount * byteCount category ≤ count₁)
    (enough₂ : w * byteCount category ≤ count₂) :
    ByteSampling.Result
      ((Fin gammaCount → QuotientRing category) × (Fin w → QuotientRing category)) :=
  ByteSampling.expandBatching xof (byteCount category) gammaCount w count₁ count₂
    enough₁ enough₂ (decode category order)

end SDitH.Spec.FieldBytes
