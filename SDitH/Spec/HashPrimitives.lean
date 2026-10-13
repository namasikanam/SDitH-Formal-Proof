import SDitH.Spec.SHAKE
import SDitH.Spec.SeedPrimitives

/-! SDitH's concrete SHAKE-based hash and XOF primitive calls. The input
payloads here are already serialized bit strings. No unspecified field,
counter or structured-transcript serialization is selected by this module.
Enc* remains a function argument at this reusable boundary; CipherPrimitives
instantiates it with the actual AES/Rijndael bodies.
-/

namespace SDitH.Spec.HashPrimitives

open DomainSeparation FieldRepresentation

def domainHash (category : Category) (domain : Byte) (payload : List Bool) :
    Bits (2 * width category) :=
  SHAKE.hash category (BAVC.byteBits domain ++ payload)

def digestXOF (category : Category) (digest : Bits (2 * width category)) : Nat → Byte :=
  SHAKE.byteStream category (List.ofFn digest)

/-- Algorithm 7 with the actual Table-1 SHAKE choice, the source's seed
formulas, and the actual domain-prefix/array serialization in BAVC. -/
def bavcPrimitives (category : Category) (leafCount : Nat) (variant : Grinding)
    (encStar : Bits (width category) → Bits (width category) → Bits (width category)) :
    BAVC.Primitives (width category) :=
  SeedPrimitives.bavcPrimitives leafCount variant encStar (SHAKE.hash category)

end SDitH.Spec.HashPrimitives
