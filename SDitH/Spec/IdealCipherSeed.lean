import SDitH.Spec.IdealCipher
import SDitH.Spec.SeedPrimitives

/-! The Category-III Enc* call in the ideal-cipher experiment. The shared cipher
has 256-bit keys and blocks. Both 192-bit inputs are zero-padded; only the
returned answer is truncated. The private transcript keeps the full blocks. -/

namespace SDitH.Spec.IdealCipherSeed

open DomainSeparation IdealCipher

def project192 (block : Bits 256) : Bits 192 :=
  fun i => block ⟨i.val, by have hi := i.isLt; omega⟩

noncomputable def queryIII (world : World (Bits 256) (Bits 256)) (key input : Bits 192) :
    PMF (Bits 192 × World (Bits 256) (Bits 256)) :=
  (query world (.encrypt (SeedPrimitives.pad192 key) (SeedPrimitives.pad192 input))).map
    fun result => (project192 result.1, result.2)

end SDitH.Spec.IdealCipherSeed
