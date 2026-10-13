import SDitH.Spec.Parameters
import Mathlib.Data.Rat.Defs

/-! Literal size formulas and Tables 8–10 in §6, printed pp. 45–48.
Constraint degree is an explicit argument: scaling a three-layer tensor by
one more witness value can give degree four. It is not silently identified
with the number of tensor factors. The source uses d in both contexts.
These are arithmetic specifications, not security or executable-layout claims.
-/

namespace SDitH.Spec.VariantParameters

open RSDParameters

/-- Round a bit length to a multiple of a positive granularity, as on p. 47.
The source's intended uses have granularity > 0. -/
def ceilMultiple (granularity bits : Nat) : Nat :=
  granularity * ((bits + granularity - 1) / granularity)

def scaledWitnessBits (p : RSDParameters) (fieldBits : Nat) : Nat :=
  p.w * fieldBits + p.witnessBits

def scaledPublicKeyBytes (p : RSDParameters) (fieldBits : Nat) : Nat :=
  ceilBytes (p.lambda + (p.n - p.k) * fieldBits)

def scaledSecretKeyBytes (p : RSDParameters) (fieldBits : Nat) : Nat :=
  ceilBytes (p.lambda + (p.n - p.k) * fieldBits + scaledWitnessBits p fieldBits)

/-- The Fq signature formula on p. 45, with q=2^fieldBits. -/
def scaledSignatureBits (p : RSDParameters) (s : ProofParameters)
    (fieldBits degree : Nat) : Nat :=
  let L := p.lambda
  let wit := ceil8 (scaledWitnessBits p fieldBits)
  let rnd := (degree - 1) * L
  3 * L + (s.tau - 1) * (wit + rnd + (L + s.consistencySlack)) +
    (L + s.consistencySlack) + wit + rnd +
    L * s.openingBound + s.tau * (2 * L) + 32

structure ScaledRow where
  rsd : RSDParameters
  proof : ProofParameters
  publicBytes : Nat
  secretBytes : Nat
  signatureBytes : Nat
  baselineBytes : Nat
  deriving DecidableEq, Repr

/-- Table 8 in printed row order. -/
def table8 : List ScaledRow :=
  [⟨categoryI256, ⟨11,11,9,109,16⟩, 80,153,3677,3721⟩,
   ⟨categoryI256, ⟨7,18,4,107,16⟩, 80,153,4842,4914⟩,
   ⟨categoryIII256, ⟨11,17,7,169,16⟩, 120,227,8433,8484⟩,
   ⟨categoryIII256, ⟨7,27,5,161,16⟩, 120,227,10771,10852⟩,
   ⟨categoryV256, ⟨11,23,5,228,16⟩, 152,293,15101,15147⟩,
   ⟨categoryV256, ⟨7,36,6,216,16⟩, 152,293,19072,19144⟩]

structure TCParameters where
  kappa : Nat
  tau : Nat
  grindingBits : Nat
  openingBound : Nat
  deriving DecidableEq, Repr

def tcSignatureBits (p : RSDParameters) (s : TCParameters) (degree : Nat) : Nat :=
  3 * p.lambda + s.tau * ceil8 p.witnessBits +
    s.tau * (degree - 1) * ceilMultiple s.kappa p.lambda +
    p.lambda * s.openingBound + s.tau * (2 * p.lambda) + 32

structure TCRow where
  rsd : RSDParameters
  proof : TCParameters
  signatureBytes : Nat
  baselineBytes : Nat
  reportedReductionPercent : Nat
  deriving DecidableEq, Repr

/-- Table 9 in printed row order. Percentages are data, not exact equalities. -/
def table9 : List TCRow :=
  [⟨categoryI, ⟨11,14,2,127⟩, 4303,3721,14⟩,
   ⟨categoryI, ⟨7,24,8,144⟩, 6169,4914,20⟩,
   ⟨categoryIII, ⟨11,21,3,198⟩, 9706,8484,13⟩,
   ⟨categoryIII, ⟨7,37,7,219⟩, 13898,10852,22⟩,
   ⟨categoryV, ⟨11,28,4,268⟩, 17244,15147,12⟩,
   ⟨categoryV, ⟨7,50,6,294⟩, 24715,19144,23⟩]

structure SimpleParameters where
  kappa : Nat
  tau : Nat
  deriving DecidableEq, Repr

/-- The displayed formula retains its final 32 bits even though the prose
says there is no grinding. No unprinted counter-removal optimization is made. -/
def simpleSignatureBits (p : RSDParameters) (s : SimpleParameters) (B degree : Nat) : Nat :=
  let L := p.lambda
  let wit := ceil8 p.witnessBits
  let rnd := (degree - 1) * L
  3 * L + (s.tau - 1) * (wit + rnd + (L + B)) +
    (L + B) + wit + rnd + L * s.tau * s.kappa + s.tau * (2 * L) + 32

structure SimpleRow where
  rsd : RSDParameters
  proof : SimpleParameters
  signatureBytes : Nat
  baselineBytes : Nat
  reportedReductionPercent : Nat
  deriving DecidableEq, Repr

/-- Table 10 in printed row order. B is not printed in this table. -/
def table10 : List SimpleRow :=
  [⟨categoryI, ⟨11,12⟩, 4264,3721,13⟩,
   ⟨categoryI, ⟨7,19⟩, 5505,4914,11⟩,
   ⟨categoryIII, ⟨11,18⟩, 9436,8484,10⟩,
   ⟨categoryIII, ⟨7,28⟩, 11948,10852,9⟩,
   ⟨categoryV, ⟨11,24⟩, 16636,15147,9⟩,
   ⟨categoryV, ⟨7,37⟩, 20857,19144,8⟩]

/-- The claimed VOLE and TCitH error-budget inequalities, cleared of their
positive power-of-two denominators. These are parameter predicates only. -/
def VoleBudget (lambda degree kappa tau grindingBits : Nat) : Prop :=
  degree * 2 ^ lambda ≤ 2 ^ (kappa * tau + grindingBits)

def TCBudget (lambda degree kappa tau grindingBits : Nat) : Prop :=
  degree ^ tau * 2 ^ lambda ≤ 2 ^ (kappa * tau + grindingBits)

/-- Rational versions of the displayed error expressions, including grinding.
No assertion is made that a protocol's acceptance probability equals these. -/
def voleError (degree kappa tau grindingBits : Nat) : Rat :=
  degree / (2 ^ (kappa * tau + grindingBits) : Rat)

def tcError (degree kappa tau grindingBits : Nat) : Rat :=
  (degree : Rat) ^ tau / (2 ^ (kappa * tau + grindingBits) : Rat)

end SDitH.Spec.VariantParameters
