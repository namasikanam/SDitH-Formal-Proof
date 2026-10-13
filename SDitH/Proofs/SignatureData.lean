import SDitH.Proofs.HonestView
import SDitH.Proofs.PRGHypothesis

/-! The committed arithmetic's signature data as the honest data of
execution zero's hidden vector. Over the submitted field with its
generator, the witness correction, the hashed coefficients below the top
and the plain check of the committed arithmetic are the honest data map
applied to the hidden party's vector, with the other parties' constants,
the zero-randomness hashed coefficients and the slope terms as the
(witness-dependent) constants. With the hidden party's vector the PRG
vector of its seed, the PRG hypothesis makes this data uniform over the
seed and independent of the witness. -/

namespace SDitH.Proofs.SignatureData

open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Spec.CoefficientCompression Spec.BLC Spec.BLCCommit
open Spec.FieldRepresentation Spec.DomainSeparation Polynomial
open HashedPads HashedView HonestView HonestViewUniform ViewBijection TranscriptRevealed RevealedBijection PRGHypothesis
open scoped BigOperators Classical

noncomputable section

variable (category : Category)

section Arithmetic

variable {r k w higherCount tau N kappa s : Nat} [NeZero tau] (widths : List Nat)
  (hsize : leafCount widths * w = r + k) (gamma : Fin (blockCount r (width category)) → QuotientRing category)
  (gammaPrime : Fin w → QuotientRing category) (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
  (phi : Fin N → Fin kappa → ZMod 2)
  (random : Fin tau → Fin N → Fin (s + (selectorCount widths * w + width category * (widths.length - 1))) → ZMod 2)
  (M : Matrix (Fin s) (Fin (selectorCount widths * w + width category * (widths.length - 1))) (ZMod 2))
  (witness : Fin (selectorCount widths * w) → ZMod 2) (h : Fin N)

/-- The other parties' packed layers. -/
def othersPacked (i : Fin (widths.length - 1)) : QuotientRing category :=
  packedConst (generator category) (layerBitsOf (HiddenShareTranslation.others random h) i)

/-- The zero-randomness hashed coefficients below the top. -/
def zeroRandomnessHashed (hdeg : widths.length = higherCount + 1) (i : Fin (widths.length - 1)) : QuotientRing category :=
  hashedCoefficients higherCount (proverRun widths hsize (generator category) gamma gammaPrime H' y
    (commitArithmetic (generator category) phi random M witness).witnessLines 0) ⟨i.val, by omega⟩

/-- The slope terms of the hashed coefficients below the top. -/
def slopeTerm (i : Fin (widths.length - 1)) : QuotientRing category :=
  if h1 : 1 ≤ i.val then ∑ j, generator category ^ j.val *
    psi (generator category) (baseRow phi random (randomnessIndex (blockIndex
      (⟨widths.length - 1 - i.val, by have := i.isLt; omega⟩ : Fin (widths.length - 1)) j)))
  else 0

/-- The hashed coefficients below the top are the honest data's middle component. -/
theorem hashed_eq_honestData (hdeg : widths.length = higherCount + 1) (i : Fin (widths.length - 1)) :
    let arithmetic := commitArithmetic (generator category) phi random M witness
    hashedCoefficients higherCount
        (proverRun widths hsize (generator category) gamma gammaPrime H' y arithmetic.witnessLines arithmetic.randomnessLines)
        ⟨i.val, by omega⟩ =
      (honestData category M (constantsA random witness h) (othersPacked category widths random h)
        (constantsC random M h) (zeroRandomnessHashed category widths hsize gamma gammaPrime H' y phi random M witness hdeg)
        (slopeTerm category widths phi random (r := r) (k := k)) (random 0 h)).2.1 i := by
  intro arithmetic
  have hi : (⟨i.val, by omega⟩ : Fin (higherCount + 1)).val + 2 ≤ widths.length := by
    have := i.isLt
    simp only
    omega
  rw [hashed_below_top category widths hsize gamma gammaPrime H' y phi random M witness h ⟨i.val, by omega⟩ hi]
  simp only [honestData, viewMap, layerRev, othersPacked, zeroRandomnessHashed, slopeTerm]
  unfold layerBitsOf
  by_cases h1 : 1 ≤ i.val
  · simp only [h1, ↓reduceDIte]
    ring
  · simp only [h1, ↓reduceDIte]
    ring

/-- The witness correction and plain check are the honest data's outer
components. -/
theorem aux_eq_honestData (hdeg : widths.length = higherCount + 1) :
    let arithmetic := commitArithmetic (generator category) phi random M witness
    let data := honestData category M (constantsA random witness h) (othersPacked category widths random h)
      (constantsC random M h) (zeroRandomnessHashed category widths hsize gamma gammaPrime H' y phi random M witness hdeg)
      (slopeTerm category widths phi random (r := r) (k := k)) (random 0 h)
    arithmetic.witnessCorrection = data.1 ∧ arithmetic.plainCheck = data.2.2 := by
  intro arithmetic data
  obtain ⟨h1, h2⟩ := aux_components category phi random M witness h
  exact ⟨h1, h2⟩

end Arithmetic

end
end SDitH.Proofs.SignatureData
