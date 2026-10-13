import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Literal Tables 3–5 and the size formulas in §4.2.
Parameters are data; no unproved consistency invariant is embedded in the type. -/

namespace SDitH.Spec

structure RSDParameters where
  lambda : Nat
  claimedSecurityBits : Nat
  q : Nat
  n : Nat
  codimension : Nat
  k : Nat
  w : Nat
  arities : List Nat
  deriving DecidableEq, Repr

namespace RSDParameters

/-- Table 3, printed p. 40. -/
def categoryI : RSDParameters := ⟨128, 143, 2, 10360, 432, 9928, 56, [4,4,4,3]⟩
def categoryIII : RSDParameters := ⟨192, 207, 2, 18396, 592, 17804, 73, [4,4,4,4]⟩
def categoryV : RSDParameters := ⟨256, 272, 2, 19864, 800, 19064, 104, [4,4,4,3]⟩

/-- Table 7, printed p. 46. -/
def categoryI256 : RSDParameters := ⟨128, 143, 256, 2176, 64, 2112, 34, [4,4,4]⟩
def categoryIII256 : RSDParameters := ⟨192, 207, 256, 3200, 96, 3104, 50, [4,4,4]⟩
def categoryV256 : RSDParameters := ⟨256, 272, 256, 4224, 120, 4104, 66, [4,4,4]⟩

/-- Required by the tensor model on printed p. 8: `∏ μj = n / w`.
The multiplication form avoids hiding any truncation in natural division. -/
def TensorDimensionsMatch (p : RSDParameters) : Prop :=
  p.n = p.w * p.arities.prod

instance (p : RSDParameters) : Decidable (TensorDimensionsMatch p) :=
  inferInstanceAs (Decidable (p.n = p.w * p.arities.prod))

/-- Unpadded binary witness length; §4.2, printed p. 39. -/
def witnessBits (p : RSDParameters) : Nat :=
  p.w * (p.arities.map (fun μ => μ - 1)).sum

end RSDParameters

def ceilBytes (bits : Nat) : Nat := (bits + 7) / 8
def ceil8 (bits : Nat) : Nat := 8 * ceilBytes bits

/-- Algorithm 6 line 5 names this many bytes on the left of Parse. This literal
shape is kept separate from the actual ciphertext size in Section 3.2.1. -/
def prgDeclaredParseBytes (lambda blocks : Nat) : Nat := blocks * (lambda / 8)

/-- Bit length of the concatenated Enc outputs on the right of that line. -/
def prgCiphertextBits (ciphertextWidth blocks : Nat) : Nat := blocks * ciphertextWidth

structure ProofParameters where
  kappa : Nat
  tau : Nat
  grindingBits : Nat
  openingBound : Nat
  consistencySlack : Nat
  deriving DecidableEq, Repr

/-- Table 4 in row order: L1 short/fast, L3 short/fast, L5 short/fast. -/
def hashProofParameters : List ProofParameters :=
  [⟨11,11,9,109,16⟩, ⟨7,18,4,107,16⟩,
   ⟨11,17,7,169,16⟩, ⟨7,27,5,161,16⟩,
   ⟨11,23,5,228,16⟩, ⟨7,36,6,216,16⟩]

/-- Table 5 in the same order, printed p. 41. -/
def cipherProofParameters : List ProofParameters :=
  [⟨11,11,9,109,16⟩, ⟨7,17,11,101,16⟩,
   ⟨11,17,7,169,16⟩, ⟨7,26,12,155,16⟩,
   ⟨11,23,5,228,16⟩, ⟨7,36,6,216,16⟩]

/-- Binary key size formula, printed p. 39. -/
def publicKeyBytes (p : RSDParameters) : Nat :=
  (p.lambda + p.n - p.k) / 8

def secretKeyBytes (p : RSDParameters) : Nat :=
  ceilBytes (p.lambda + (p.n - p.k) + p.witnessBits)

/-- Binary signature size formula, printed p. 40, before byte conversion. -/
def signatureBits (p : RSDParameters) (s : ProofParameters) : Nat :=
  let L := p.lambda
  let wit := ceil8 p.witnessBits
  let rnd := (p.arities.length - 1) * L
  3 * L + (s.tau - 1) * (wit + rnd + (L + s.consistencySlack)) +
    (L + s.consistencySlack) + wit + rnd +
    L * s.openingBound + s.tau * (2 * L) + 32

end SDitH.Spec
