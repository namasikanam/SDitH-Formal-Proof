import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot

/-! The exact three quotient constructions in Table 2, printed p. 39.
They are introduced as quotient rings. Irreducibility and hence their field
instances are separate proof obligations, not facts installed by this module.
-/

namespace SDitH.Spec.FieldRepresentation

open Polynomial
open scoped BigOperators

inductive Category where
  | i
  | iii
  | v
  deriving DecidableEq, Repr

def width : Category → Nat
  | .i => 128
  | .iii => 192
  | .v => 256

noncomputable def modulus : Category → (ZMod 2)[X]
  | .i => X ^ 128 + X ^ 7 + X ^ 2 + X + 1
  | .iii => X ^ 192 + X ^ 7 + X ^ 2 + X + 1
  | .v => X ^ 256 + X ^ 10 + X ^ 5 + X ^ 2 + 1

abbrev QuotientRing (category : Category) := AdjoinRoot (modulus category)

noncomputable def generator (category : Category) : QuotientRing category :=
  AdjoinRoot.root (modulus category)

/-- Coefficient encoding in the submitted polynomial basis. This is the
displayed power-sum encoding, not an unspecified byte decoder. -/
noncomputable def encodeCoefficients (category : Category) {n : Nat}
    (coefficients : Fin n → ZMod 2) : QuotientRing category :=
  ∑ i, algebraMap (ZMod 2) (QuotientRing category) (coefficients i) * generator category ^ i.val

end SDitH.Spec.FieldRepresentation
