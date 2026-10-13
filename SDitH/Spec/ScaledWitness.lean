import SDitH.Spec.WitnessExpansion
import SDitH.Spec.PIOPArithmetic

/-! The scaled regular witness and post-mux multiplication outlined in §6.1,
printed p. 45. This records positions and nonzero values separately. The source
does not give a complete F256 signing algorithm, serializer, field polynomial,
or a constraint enforcing nonzero amplitudes; none is invented here.
The literal mux convention from §3 is retained rather than repaired.
-/

namespace SDitH.Spec.ScaledWitness

open PIOPArithmetic

@[ext] structure Witness (F : Type*) [Zero F] (w m : Nat) where
  positions : Fin w → Fin m
  amplitudes : Fin w → {a : F // a ≠ 0}

noncomputable def vector {F : Type*} [Field F] {w m : Nat} (wit : Witness F w m) :
    Fin (w * m) → F :=
  fun j => (wit.amplitudes (finProdFinEquiv.symm j).1).val *
    elementary (wit.positions (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

/-- The position part is the unchanged binary tensor encoding. Values are
stored as a separate typed vector; no unspecified concatenation order is chosen. -/
noncomputable def positionBits {F : Type*} [Zero F] {w m d : Nat}
    (width : Fin d → Nat) (wit : Witness F w m) : List (ZMod 2) :=
  (WitnessExpansion.expandAfterSampling width wit.positions).witness

def scaledMux {R : Type*} [CommRing R] (amplitude : R) (widths : List Nat)
    (selectors : Selectors R widths) (leaves : Fin (leafCount widths) → R) : R :=
  amplitude * muxTree widths selectors leaves

end SDitH.Spec.ScaledWitness
