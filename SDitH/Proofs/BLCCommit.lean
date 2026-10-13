import SDitH.Spec.BLCCommit
import SDitH.Proofs.BLCArithmetic
import SDitH.Proofs.ByteSampling
import Mathlib.Algebra.Polynomial.Degree.Operations

namespace SDitH.Proofs.BLCCommit

open Spec.BLCCommit Spec.DomainSeparation Spec.BLC Polynomial

theorem positiveIndex_value {tau : Nat} [NeZero tau] (j : Fin (tau - 1)) :
    (positiveIndex j).val = j.val + 1 := rfl

/-- All and only execution indices 1,...,tau-1 enter Hashaux and aux'. -/
theorem positiveIndex_range {tau : Nat} [NeZero tau] (e : Fin tau) :
    (∃ j : Fin (tau - 1), positiveIndex j = e) ↔ e ≠ 0 := by
  constructor
  · rintro ⟨j, rfl⟩ h
    have hv := congrArg Fin.val h
    simp [positiveIndex] at hv
  · intro he
    have he' : e.val ≠ 0 := fun h => he (Fin.ext h)
    refine ⟨⟨e.val - 1, by have hb := e.isLt; omega⟩, ?_⟩
    apply Fin.ext
    simp only [positiveIndex]
    omega

theorem randomTable_coordinate {lambda tau kappa s wit rnd : Nat}
    (p : Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (seeds : Fin tau → Fin (2 ^ kappa) → Bits lambda)
    (count : Nat) (enough : s + (wit + rnd) ≤ 8 * count)
    (e : Fin tau) (i : Fin (2 ^ kappa)) (j : Fin (s + (wit + rnd))) :
    randomTable p salt seeds count enough e i j =
      bitField ((p.prg (seeds e i) salt e.val (j.val / 8)).val.testBit (j.val % 8)) := by
  simp [randomTable, Spec.ByteSampling.sampleBinary, Spec.ByteSampling.readBytes]

theorem buildLine_degree {K F : Type*} [CommRing K] [Field F] [Algebra K F]
    (constant : K) (slope : F) : (buildLine constant slope).natDegree ≤ 1 := by
  unfold buildLine
  apply natDegree_add_le_of_degree_le
  · simp
  · exact natDegree_mul_le_of_le (show (C slope).natDegree ≤ 0 by simp)
      (show (X : F[X]).natDegree ≤ 1 by simp)

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]
variable {lambda tau kappa B wit rnd : Nat} [NeZero tau]
variable (xi : F) (p : Primitives lambda tau kappa (lambda + B) wit rnd)
variable (salt root : Bits lambda) (witness : Fin wit → ZMod 2)
variable (randomCount consistencyCount : Nat)
variable (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
variable (hconsistency : wit + rnd ≤ 8 * consistencyCount)

/-- Algorithm 10's line constants and degrees follow from its actual composed
computation, independently of any cryptographic properties of the primitives. -/
theorem line_properties :
    let result := commit xi p salt root witness randomCount consistencyCount hrandom hconsistency
    (∀ j, (result.witness j).eval 0 = algebraMap (ZMod 2) F (witness j)) ∧
    (∀ j, (result.witness j).natDegree ≤ 1) ∧
    (∀ j, (result.randomness j).natDegree ≤ 1) := by
  dsimp only [commit, commitArithmetic]
  exact ⟨fun _ => BLC.buildLine_zero _ _, fun _ => buildLine_degree _ _, fun _ => buildLine_degree _ _⟩

end SDitH.Proofs.BLCCommit
