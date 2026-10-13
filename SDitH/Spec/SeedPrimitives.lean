import SDitH.Spec.BAVC

/-! ExpandSeed and CommitSeed, printed pp. 18 and 21, linked to Algorithm 7.
Enc* and Hash are explicit function arguments. This does not implement AES,
Rijndael, or SHAKE. The displayed routines are introduced for Categories I/V;
their application to Category III remains a source-correspondence question.
-/

namespace SDitH.Spec.SeedPrimitives

open DomainSeparation

/-- A finite representation of `2*address + side`. Modulo only totalizes inputs
outside the source's 24-bit tweak precondition. The separate proofs establish
that no reduction occurs in seed calls for the submitted parameter tables. -/
def callTweak (address : Nat) (right : Bool) : Tweak :=
  ⟨(2 * address + if right then 1 else 0) % 2 ^ 24, Nat.mod_lt _ (by decide)⟩

def cipherInput {lambda : Nat} (variant : Grinding) (salt : Bits lambda)
    (address : Nat) (right : Bool) : Bits lambda :=
  tweakSalt variant salt (callTweak address right) true

/-- ExpandSeed's two Enc* calls, with the left output first. -/
def expandSeed {lambda : Nat} (variant : Grinding)
    (encStar : Bits lambda → Bits lambda → Bits lambda)
    (salt : Bits lambda) (address : Nat) (seed : Bits lambda) : Bits lambda × Bits lambda :=
  (encStar seed (cipherInput variant salt address false),
   encStar seed (cipherInput variant salt address true))

def concatenate {lambda : Nat} (left right : Bits lambda) : Bits (2 * lambda) :=
  fun j => if h : j.val < lambda then left ⟨j.val, h⟩
    else right ⟨j.val - lambda, by have hj := j.isLt; omega⟩

/-- CommitSeed adds the leaf count before generating the two cipher inputs. -/
def commitSeed {lambda : Nat} (leafCount : Nat) (variant : Grinding)
    (encStar : Bits lambda → Bits lambda → Bits lambda)
    (salt seed : Bits lambda) (index : Nat) : Bits (2 * lambda) :=
  let pair := expandSeed variant encStar salt (leafCount + index) seed
  concatenate pair.1 pair.2

/-- Explicit linkage to Algorithm 7. The only remaining primitive function
arguments are Enc* and Hash, not abstract seed expansion/commitment functions. -/
def bavcPrimitives {lambda : Nat} (leafCount : Nat) (variant : Grinding)
    (encStar : Bits lambda → Bits lambda → Bits lambda)
    (hash : List Bool → Bits (2 * lambda)) : BAVC.Primitives lambda :=
  { expandSeed := expandSeed variant encStar
    commitSeed := commitSeed leafCount variant encStar
    hash := hash }

/-- Section 3.2.1's zero extension of 192-bit Category-III inputs to 256 bits. -/
def pad192 (input : Bits 192) : Bits 256 :=
  fun j => if h : j.val < 192 then input ⟨j.val, h⟩ else false

def encIII (rijndael : Bits 256 → Bits 256 → Bits 256)
    (key plaintext : Bits 192) : Bits 256 :=
  rijndael (pad192 key) (pad192 plaintext)

/-- LSB192 with the common least-significant-first bit indexing convention.
No permutation property is imposed on this truncated function. -/
def encStarIII (rijndael : Bits 256 → Bits 256 → Bits 256)
    (key plaintext : Bits 192) : Bits 192 :=
  fun j => encIII rijndael key plaintext ⟨j.val, by have hj := j.isLt; omega⟩

end SDitH.Spec.SeedPrimitives
