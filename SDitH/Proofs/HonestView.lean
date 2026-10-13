import SDitH.Proofs.HashedView
import SDitH.Proofs.TranscriptRevealed
import SDitH.Proofs.FieldIrreducibility

/-! The honest signer's hashed coefficients below the top and auxiliary
data in terms of execution zero's hidden vector. Over the binary field
with the submitted quotient ring, each hashed coefficient below the top is
the zero-randomness coefficient plus the hidden party's packed layer plus
the other parties' packed layer plus a slope term, and the witness
correction and plain check are the revealed map's components; the
hidden-vector contributions are exactly the view map's components. This
is the deterministic core of the hidden-share step: the honest revealed
data is a fixed function of the view and of witness-free data. -/

namespace SDitH.Proofs.HonestView

open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Spec.CoefficientCompression Spec.BLC
open Spec.FieldRepresentation Polynomial HashedPads HashedView
open scoped BigOperators Classical

noncomputable section

variable (category : Category)

/-- A hashed coefficient below the top of the honest prover polynomial: the
zero-randomness coefficient, the hidden party's packed layer, the others'
packed layer and the slope term. -/
theorem hashed_below_top {r k w higherCount tau N kappa s : Nat} [NeZero tau] (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (gamma : Fin (blockCount r (width category)) → QuotientRing category)
    (gammaPrime : Fin w → QuotientRing category) (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (phi : Fin N → Fin kappa → ZMod 2)
    (random : Fin tau → Fin N → Fin (s + (selectorCount widths * w + width category * (widths.length - 1))) → ZMod 2)
    (M : Matrix (Fin s) (Fin (selectorCount widths * w + width category * (widths.length - 1))) (ZMod 2))
    (witness : Fin (selectorCount widths * w) → ZMod 2) (h : Fin N) (j : Fin (higherCount + 1)) (hj : j.val + 2 ≤ widths.length) :
    let arithmetic := commitArithmetic (generator category) phi random M witness
    hashedCoefficients higherCount
        (proverRun widths hsize (generator category) gamma gammaPrime H' y arithmetic.witnessLines arithmetic.randomnessLines) j =
      hashedCoefficients higherCount (proverRun widths hsize (generator category) gamma gammaPrime H' y arithmetic.witnessLines 0) j +
        (packedConst (generator category) (layerBitsOf (random 0 h) ⟨widths.length - 2 - j.val, by omega⟩) +
          packedConst (generator category)
            (layerBitsOf (HiddenShareTranslation.others random h) ⟨widths.length - 2 - j.val, by omega⟩)) +
        (if h1 : 1 ≤ j.val then ∑ i, generator category ^ i.val *
          psi (generator category) (baseRow phi random (randomnessIndex (blockIndex (⟨widths.length - 1 - j.val, by omega⟩ : Fin (widths.length - 1)) i)))
         else 0) := by
  intro arithmetic
  rw [hashed_eq_padded, formatRandomness_lines, formatMask_coeff_below _ _ _ _ hj, layerBits_translate phi random h,
    packedConst_add]
  ring

/-- The auxiliary triple of the honest commitment: the witness correction and
plain check are the revealed map's components (the base-ring randomness
coordinates are not transmitted). -/
theorem aux_components {tau N kappa s wit rnd : Nat} [NeZero tau] (phi : Fin N → Fin kappa → ZMod 2)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → ZMod 2) (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2))
    (witness : Fin wit → ZMod 2) (h : Fin N) :
    (commitArithmetic (generator category) phi random M witness).witnessCorrection =
        (RevealedBijection.revealedMap M (TranscriptRevealed.constantsA random witness h) (TranscriptRevealed.constantsB random h)
          (TranscriptRevealed.constantsC random M h) (random 0 h)).1 ∧
      (commitArithmetic (generator category) phi random M witness).plainCheck =
        (RevealedBijection.revealedMap M (TranscriptRevealed.constantsA random witness h) (TranscriptRevealed.constantsB random h)
          (TranscriptRevealed.constantsC random M h) (random 0 h)).2.2 := by
  have h := TranscriptRevealed.triple_eq_revealed (generator category) phi random M witness h
  exact ⟨congrArg Prod.fst h, congrArg (fun t => t.2.2) h⟩

end
end SDitH.Proofs.HonestView
