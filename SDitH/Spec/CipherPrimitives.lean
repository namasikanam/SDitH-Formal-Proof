import SDitH.Spec.Rijndael
import SDitH.Spec.HashPrimitives

/-! SDitH Table 1's concrete cipher choices, with explicit byte packing.
DomainSeparation.Bits uses low-bit-first indexing, and byte i contains positions
8*i through 8*i+7 in that order. FIPS 197's displayed bitstrings use the reverse
order within a byte; `fipsBitIndex` makes that conversion explicit.
Category III retains its 64 zero padding bits and its 192-bit truncation.
-/

namespace SDitH.Spec.CipherPrimitives

open DomainSeparation FieldRepresentation

def fromBits (p : Rijndael.Profile) (input : Bits (32 * Rijndael.columns p)) : Rijndael.State p :=
  Vector.ofFn fun byte => Keccak.word fun bit : Fin 8 =>
    input ⟨8 * byte.val + bit.val, by omega⟩

def toBits (p : Rijndael.Profile) (s : Rijndael.State p) : Bits (32 * Rijndael.columns p) :=
  fun i => (s[(⟨i.val / 8, by omega⟩ : Fin (4 * Rijndael.columns p))]).getLsbD (i.val % 8)

/-- The position in a FIPS-style displayed bitstring of the same physical bit.
Bytes keep their order; only their eight internal bit positions are reversed. -/
def fipsBitIndex (p : Rijndael.Profile) (i : Fin (32 * Rijndael.columns p)) :
    Fin (32 * Rijndael.columns p) :=
  ⟨8 * (i.val / 8) + (7 - i.val % 8), by omega⟩

def fromFipsBits (p : Rijndael.Profile) (input : Bits (32 * Rijndael.columns p)) : Rijndael.State p :=
  fromBits p (fun i => input (fipsBitIndex p i))

def encryptBits (p : Rijndael.Profile) (key plaintext : Bits (32 * Rijndael.columns p)) :
    Bits (32 * Rijndael.columns p) :=
  toBits p (Rijndael.encrypt p (fromBits p key) (fromBits p plaintext))

def ciphertextWidth : Category → Nat
  | .i => 128
  | .iii => 256
  | .v => 256

def enc (category : Category) : Bits (width category) → Bits (width category) → Bits (ciphertextWidth category) :=
  match category with
  | .i => encryptBits .aes128
  | .iii => SeedPrimitives.encIII (encryptBits .rijndael256)
  | .v => encryptBits .rijndael256

def encStar (category : Category) : Bits (width category) → Bits (width category) → Bits (width category) :=
  match category with
  | .i => encryptBits .aes128
  | .iii => SeedPrimitives.encStarIII (encryptBits .rijndael256)
  | .v => encryptBits .rijndael256

/-- Algorithm 7's primitive calls now have concrete Table-1 cipher and SHAKE
bodies. This is a functional instantiation, not a security model or theorem. -/
def bavcPrimitives (category : Category) (leafCount : Nat) (variant : Grinding) :
    BAVC.Primitives (width category) :=
  HashPrimitives.bavcPrimitives category leafCount variant (encStar category)

end SDitH.Spec.CipherPrimitives
