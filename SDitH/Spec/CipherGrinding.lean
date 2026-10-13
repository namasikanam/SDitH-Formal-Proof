import SDitH.Spec.BLCRetry

/-! Cipher grinding input preparation, printed p. 19, lines 3–9.
The source's GetBytes(4*lambda), parsing, MapToBits order, and one-subscript
Extract on line 10 remain explicit correspondence boundaries. This module starts
with the relevant lambda-bit windows and a supplied 32-bit counter encoding.
-/

namespace SDitH.Spec.CipherGrinding

open DomainSeparation

structure Material (lambda : Nat) where
  p0 : Bits lambda
  p1 : Bits lambda
  k0 : Bits lambda
  k1 : Bits lambda

/-- Lines 3–4: b concatenated with bits 1 through lambda-1 of the key. -/
def prepareKey {lambda : Nat} (bit : Bool) (key : Bits lambda) : Bits lambda :=
  fun j => if j.val = 0 then bit else key j

/-- Lines 6–7 on the stated domain lambda >= 33. The final bit assignment has
priority; behavior at smaller lambda is only a total extension, not a source
interpretation. Counter encoding is an input rather than an unstated endianness. -/
def preparePlaintext {lambda : Nat} (counterBits : Bits 32) (plaintext : Bits lambda) :
    Bits lambda :=
  fun j => if j.val + 1 = lambda then true
    else if h : j.val < 32 then counterBits ⟨j.val, h⟩ else plaintext j

/-- Lines 8–9, including both prepared keys and plaintexts. -/
def cipherCalls {lambda : Nat} (encStar : Bits lambda → Bits lambda → Bits lambda)
    (counterBits : Bits 32) (material : Material lambda) : Bits lambda × Bits lambda :=
  (encStar (prepareKey false material.k0) (preparePlaintext counterBits material.p0),
   encStar (prepareKey true material.k1) (preparePlaintext counterBits material.p1))

def xorCiphertexts {lambda : Nat} (ciphertexts : Bits lambda × Bits lambda) : Bits lambda :=
  fun j => Bool.xor (ciphertexts.1 j) (ciphertexts.2 j)

/-- A candidate least-significant-first MapToBits, matching the explicit salt
convention. The grinding text does not specify this order, so it is not wired
into cipherCalls by default. -/
def counterBitsLE (counter : BLCRetry.Counter) : Bits 32 :=
  fun j => counter.val.testBit j.val

/-- Keep the counter in the initial material expansion, as printed on line 1.
This does not apply the contradictory prose claim that it can be factored out. -/
def counterDependentCalls {lambda : Nat}
    (encStar : Bits lambda → Bits lambda → Bits lambda)
    (encodeCounter : BLCRetry.Counter → Bits 32)
    (expandMaterial : BLCRetry.Counter → Material lambda) (counter : BLCRetry.Counter) :
    Bits lambda × Bits lambda :=
  cipherCalls encStar (encodeCounter counter) (expandMaterial counter)

end SDitH.Spec.CipherGrinding
