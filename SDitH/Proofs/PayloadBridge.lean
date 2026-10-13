import SDitH.Proofs.BLCArithmetic
import SDitH.Proofs.BLCSeedLines
import SDitH.Proofs.CandidateVerifier

/-! The bridge between the honest commitment arithmetic and the verifier's
affine share matrix. The verifier's slope at every execution is the common
accumulator of the random table (the transmitted corrections restore it),
so its share matrix at the hidden indices is the corrected opening of the
honest arithmetic; hence the honest witness and randomness lines evaluated
at the inverse challenge are the verifier's recomputed values. -/

namespace SDitH.Proofs.PayloadBridge

open Spec.BLC Spec.BLCSeedFold Spec.BLCSeedLines Spec.BLCCommit Spec.BLCRecompute Spec.DomainSeparation
open scoped Classical

noncomputable section

variable {lambda tau kappa s wit rnd : Nat} [NeZero tau]

/-- The packaged positive corrections at a positive execution. -/
theorem correctionTerm_positive (random : Fin tau → Fin (2 ^ kappa) → Fin (s + (wit + rnd)) → ZMod 2)
    (aux : Auxiliary tau s wit rnd)
    (haux : aux.corrections = positiveCorrections (correction Spec.GrayCode.grayFieldRow random)) (e : Fin tau)
    (he : 0 < e.val) (c : Fin (s + (wit + rnd))) :
    correctionTerm aux e c = correction Spec.GrayCode.grayFieldRow random e c := by
  unfold correctionTerm
  rw [dif_pos he, haux]
  unfold positiveCorrections
  congr 2
  ext
  simp [positiveIndex, correctionIndex]
  omega

/-- The verifier's slope at every execution is the common accumulator. -/
theorem slope_eq_commonAcc (p : Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (aux : Auxiliary tau s wit rnd)
    (haux : aux.corrections = positiveCorrections
      (correction Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough)))
    (e : Fin tau) (c : Fin (s + (wit + rnd))) :
    Spec.BLCSeedFold.slope p salt full randomCount enough aux e c =
      commonAcc Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough) c := by
  unfold Spec.BLCSeedFold.slope folded
  by_cases he : 0 < e.val
  · rw [correctionTerm_positive _ aux haux e he c]
    unfold correction
    simp only [Pi.sub_apply, foldExecutions]
    ring
  · have he0 : e = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    subst he0
    unfold correctionTerm
    rw [dif_neg he]
    simp [commonAcc, foldExecutions]

/-- The verifier's share matrix at the hidden indices is the corrected
opening of the honest arithmetic. -/
theorem shareMatrix_eq_correctedOpening (p : Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (aux : Auxiliary tau s wit rnd)
    (haux : aux.corrections = positiveCorrections
      (correction Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough)))
    (hidden : Fin tau → Fin (2 ^ kappa)) (c : Fin (s + (wit + rnd))) :
    shareMatrix p salt full randomCount enough aux hidden c =
      correctedOpening Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough) hidden c := by
  funext e j
  rw [BLC.correctedOpening_formula]
  simp only [shareMatrix, affine, intercept, folded, challengeRow, baseRow, foldExecutions]
  rw [slope_eq_commonAcc p salt full randomCount enough aux haux e c]

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- The honest witness line at the inverse challenge is the verifier's
recomputed witness value. -/
theorem witnessLine_eval (xi : F) (p : Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (witness : Fin wit → ZMod 2) (aux : Auxiliary tau s wit rnd)
    (haux : aux.corrections = positiveCorrections
      (correction Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough)))
    (hidden : Fin tau → Fin (2 ^ kappa)) (hd : psi xi (challengeRow Spec.GrayCode.grayFieldRow hidden) ≠ 0) (j : Fin wit) :
    ((commitArithmetic xi Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough) M witness).witnessLines j).eval
        (psi xi (challengeRow Spec.GrayCode.grayFieldRow hidden))⁻¹ =
      algebraMap (ZMod 2) F
          ((commitArithmetic xi Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough) M witness).witnessCorrection j) +
        (psi xi (challengeRow Spec.GrayCode.grayFieldRow hidden))⁻¹ *
          psi xi (shareMatrix p salt full randomCount enough aux hidden (witnessIndex j)) := by
  rw [shareMatrix_eq_correctedOpening p salt full randomCount enough aux haux hidden,
    ← (BLC.commitArithmetic_evaluations xi Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough) M witness
      hidden hd).1 j]
  rfl

/-- The honest randomness line at the inverse challenge is the verifier's
recomputed randomness value. -/
theorem randomnessLine_eval (xi : F) (p : Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (witness : Fin wit → ZMod 2) (aux : Auxiliary tau s wit rnd)
    (haux : aux.corrections = positiveCorrections
      (correction Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough)))
    (hidden : Fin tau → Fin (2 ^ kappa)) (hd : psi xi (challengeRow Spec.GrayCode.grayFieldRow hidden) ≠ 0) (j : Fin rnd) :
    ((commitArithmetic xi Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough) M witness).randomnessLines j).eval
        (psi xi (challengeRow Spec.GrayCode.grayFieldRow hidden))⁻¹ =
      (psi xi (challengeRow Spec.GrayCode.grayFieldRow hidden))⁻¹ *
        psi xi (shareMatrix p salt full randomCount enough aux hidden (randomnessIndex j)) := by
  rw [shareMatrix_eq_correctedOpening p salt full randomCount enough aux haux hidden,
    ← (BLC.commitArithmetic_evaluations xi Spec.GrayCode.grayFieldRow (randomTable p salt full randomCount enough) M witness
      hidden hd).2 j]
  simp [reciprocalEvaluation]

end
end SDitH.Proofs.PayloadBridge
