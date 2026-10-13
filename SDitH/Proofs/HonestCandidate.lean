import SDitH.Proofs.CandidateVerifier
import SDitH.Proofs.BLCSeedFold

/-! The candidate verifier against the honest signer. With the honest
corrections computed from the same seeds, the slope of every execution is
the committed common accumulator, so the masked slope is Algorithm 10's
plain check and the intercept matrix is its base row matrix. Hence the
candidate base computed from the honest shares at any hidden indices is
exactly the honest base check. This is the algebraic half of the
candidate target's completeness: an honest signature recomputes the same
lines payload under the candidate reading, independently of the hidden
indices and of the mask. -/

namespace SDitH.Proofs.HonestCandidate

open Spec.BLCRecompute Spec.BLCSeedFold Spec.BLCSeedLines Spec.DomainSeparation Spec.CandidateVerifier
open scoped BigOperators

variable {lambda tau kappa s wit rnd : Nat}

/-- Honest auxiliary data: the transmitted corrections computed from the seeds. -/
def honestAux [NeZero tau] (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (plain : Fin s → ZMod 2) (witnessCorrection : Fin wit → ZMod 2) :
    Spec.BLCCommit.Auxiliary tau s wit rnd :=
  ⟨Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow
      (Spec.BLCCommit.randomTable p salt full randomCount enough)), plain, witnessCorrection⟩

/-- With honest corrections, every execution's slope is the common accumulator. -/
theorem slope_honest [NeZero tau] (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (plain : Fin s → ZMod 2) (witnessCorrection : Fin wit → ZMod 2)
    (e : Fin tau) (c : Fin (s + (wit + rnd))) :
    Spec.BLCSeedFold.slope p salt full randomCount enough (honestAux p salt full randomCount enough plain witnessCorrection) e c =
      Spec.BLC.commonAcc Spec.GrayCode.grayFieldRow (Spec.BLCCommit.randomTable p salt full randomCount enough) c := by
  simp only [Spec.BLCSeedFold.slope, folded, correctionTerm, honestAux, Spec.BLCCommit.positiveCorrections]
  split_ifs with he
  · have hidx : Spec.BLCCommit.positiveIndex (correctionIndex e he) = e := by
      apply Fin.ext
      simp only [Spec.BLCCommit.positiveIndex, correctionIndex]
      omega
    rw [hidx]
    simp only [Spec.BLC.correction, Pi.sub_apply, Spec.BLC.foldExecutions]
    ring
  · have hzero : e = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    subst hzero
    simp only [Spec.BLC.commonAcc, Spec.BLC.foldExecutions, add_zero]

/-- The honest masked slope is the plain consistency check. -/
theorem maskedSlope_honest [NeZero tau] (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (plain : Fin s → ZMod 2) (witnessCorrection : Fin wit → ZMod 2)
    (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (e : Fin tau) (a : Fin s) :
    maskedSlope p salt full randomCount enough (honestAux p salt full randomCount enough plain witnessCorrection) M e a =
      Spec.BLC.consistencyCheck M
        (Spec.BLC.commonAcc Spec.GrayCode.grayFieldRow (Spec.BLCCommit.randomTable p salt full randomCount enough)) a := by
  simp only [maskedSlope, slope_honest, Spec.BLC.consistencyCheck, Matrix.mulVec, dotProduct]

/-- The intercept matrix is Algorithm 10's base row matrix. -/
theorem interceptMatrix_honest (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) :
    interceptMatrix p salt full randomCount enough =
      Spec.BLC.baseRow Spec.GrayCode.grayFieldRow (Spec.BLCCommit.randomTable p salt full randomCount enough) := by
  funext c e j
  rfl

/-- The candidate base of the honest shares at any hidden indices is the
honest base check, for any mask. -/
theorem candidateBase_honest {F : Type*} [CommRing F] [Algebra (ZMod 2) F] [NeZero tau] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2))
    (witness : Fin wit → ZMod 2) (hidden : Fin tau → Fin (2 ^ kappa)) :
    candidateBase M
      (Spec.BLC.commitArithmetic xi Spec.GrayCode.grayFieldRow
        (Spec.BLCCommit.randomTable p salt full randomCount enough) M witness).plainCheck hidden
      (shareMatrix p salt full randomCount enough
        (honestAux p salt full randomCount enough
          (Spec.BLC.commitArithmetic xi Spec.GrayCode.grayFieldRow
            (Spec.BLCCommit.randomTable p salt full randomCount enough) M witness).plainCheck
          (Spec.BLC.commitArithmetic xi Spec.GrayCode.grayFieldRow
            (Spec.BLCCommit.randomTable p salt full randomCount enough) M witness).witnessCorrection) hidden) =
      (Spec.BLC.commitArithmetic xi Spec.GrayCode.grayFieldRow
        (Spec.BLCCommit.randomTable p salt full randomCount enough) M witness).baseCheck := by
  funext a e j
  set arithmetic := Spec.BLC.commitArithmetic xi Spec.GrayCode.grayFieldRow
    (Spec.BLCCommit.randomTable p salt full randomCount enough) M witness with harith
  set aux := honestAux p salt full randomCount enough arithmetic.plainCheck arithmetic.witnessCorrection with haux
  show candidateBase M aux.plain hidden (shareMatrix p salt full randomCount enough aux hidden) a e j = _
  rw [CandidateVerifier.candidateBase_affine, haux, maskedSlope_honest, interceptMatrix_honest]
  simp only [harith, Spec.BLC.commitArithmetic, honestAux, sub_self, zero_mul, zero_add]

end SDitH.Proofs.HonestCandidate
