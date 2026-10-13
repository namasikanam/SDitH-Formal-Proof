import SDitH.Proofs.MuxSelect
import SDitH.Proofs.ExtractionSplit
import SDitH.Proofs.KeyGeneration

/-! The extracted solution as a syndrome-decoding solution of the public
instance: a witness with zero mux syndrome residual and unitary selectors
selects one leaf per chunk, the vector with a one at each chunk's selected
leaf is a solution of the systematic instance `[I | H']·x = y` of weight
`w` (one per chunk), which is the key generation's solution notion. -/

namespace SDitH.Proofs.SolutionRegular

open Spec.PIOPArithmetic Spec.UnitaryPolynomial Spec.PIOPComposition Spec.Batching
open Spec.PIOPArithmetic (selectorCount)
open MuxSelect ExtractionSplit
open scoped BigOperators Classical

noncomputable section

theorem leafCount_pos : ∀ widths : List Nat, 0 < leafCount widths
  | [] => by simp [leafCount]
  | r :: rest => by
    simp only [leafCount]
    exact Nat.mul_pos (Nat.succ_pos r) (leafCount_pos rest)

/-- The chunk-and-leaf addressing of the flattened witness. -/
def chunkEquiv (a w : Nat) (ha : 0 < a) : Fin w × Fin a ≃ Fin (a * w) where
  toFun p := blockIndex p.1 p.2
  invFun idx := (⟨idx.val / a, Nat.div_lt_of_lt_mul idx.isLt⟩, ⟨idx.val % a, Nat.mod_lt _ ha⟩)
  left_inv p := by
    ext
    · simp only [blockIndex]
      rw [Nat.mul_add_div ha, Nat.div_eq_of_lt p.2.isLt, Nat.add_zero]
    · simp only [blockIndex]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt p.2.isLt]
  right_inv idx := by
    ext
    simp only [blockIndex]
    exact Nat.div_add_mod idx.val a

theorem chunkEquiv_apply (a w : Nat) (ha : 0 < a) (p : Fin w × Fin a) : chunkEquiv a w ha p = blockIndex p.1 p.2 := rfl

variable {r k w : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k)

/-- The flattened-index equivalence of the public instance. -/
def flatEquiv : Fin w × Fin (leafCount widths) ≃ Fin (r + k) :=
  (chunkEquiv (leafCount widths) w (leafCount_pos widths)).trans (finCongr hsize)

theorem flatEquiv_apply (p : Fin w × Fin (leafCount widths)) :
    flatEquiv widths hsize p = Fin.cast hsize (blockIndex p.1 p.2) := rfl

/-- The vector with a one at each chunk's selected leaf. -/
def solutionVector (bits : Fin (selectorCount widths * w) → ZMod 2) : Fin (r + k) → ZMod 2 :=
  fun idx =>
    let p := (flatEquiv widths hsize).symm idx
    Spec.elementary (selectAddress widths (formatWitness widths bits p.1)) p.2

theorem solutionVector_apply (bits : Fin (selectorCount widths * w) → ZMod 2) (i : Fin w) (j : Fin (leafCount widths)) :
    solutionVector widths hsize bits (Fin.cast hsize (blockIndex i j)) =
      Spec.elementary (selectAddress widths (formatWitness widths bits i)) j := by
  show Spec.elementary (selectAddress widths (formatWitness widths bits
      ((flatEquiv widths hsize).symm (Fin.cast hsize (blockIndex i j))).1))
    ((flatEquiv widths hsize).symm (Fin.cast hsize (blockIndex i j))).2 = _
  rw [← flatEquiv_apply widths hsize (i, j), Equiv.symm_apply_apply]

/-- The systematic instance applied to the solution vector is the chunk sum
of the selected columns. -/
theorem mulVec_solutionVector (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (bits : Fin (selectorCount widths * w) → ZMod 2)
    (row : Fin r) :
    (systematicLeft H').mulVec (solutionVector widths hsize bits) row =
      ∑ i, systematicLeft H' row (Fin.cast hsize (blockIndex i (selectAddress widths (formatWitness widths bits i)))) := by
  show ∑ idx, systematicLeft H' row idx * solutionVector widths hsize bits idx = _
  rw [← (flatEquiv widths hsize).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [flatEquiv_apply, solutionVector_apply, Spec.elementary]
  rw [Finset.sum_eq_single (selectAddress widths (formatWitness widths bits i))]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A witness with zero residual and unitary selectors gives a solution of
the systematic instance. -/
theorem mulVec_eq_of_residual (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (bits : Fin (selectorCount widths * w) → ZMod 2)
    (hres : muxSyndromeResidual widths hsize H' y bits = 0)
    (hsel : ∀ i (j : Fin widths.length), AtMostOne (selectorAt widths (formatWitness widths bits i) j)) :
    (systematicLeft H').mulVec (solutionVector widths hsize bits) = y := by
  funext row
  rw [mulVec_solutionVector]
  have h := congrFun hres row
  simp only [muxSyndromeResidual, Pi.zero_apply] at h
  have hmux : ∀ i, muxTree widths (formatWitness widths bits i) (chunkColumns widths hsize (systematicLeft H' row) i) =
      systematicLeft H' row (Fin.cast hsize (blockIndex i (selectAddress widths (formatWitness widths bits i)))) := by
    intro i
    rw [muxTree_select widths _ (allAtMostOne_of_selectorAt widths _ (hsel i))]
    rfl
  simp only [hmux] at h
  exact (neg_add_eq_zero.mp h).symm

/-- The solution vector has weight `w`: one nonzero entry per chunk. -/
theorem hammingWeight_solutionVector (bits : Fin (selectorCount widths * w) → ZMod 2) :
    Spec.hammingWeight (solutionVector widths hsize bits) = w := by
  unfold Spec.hammingWeight
  have himage : ∀ inst : DecidablePred fun idx => solutionVector widths hsize bits idx ≠ 0,
      (@Finset.filter _ _ inst Finset.univ) =
      Finset.univ.image fun i : Fin w =>
        flatEquiv widths hsize (i, selectAddress widths (formatWitness widths bits i)) := by
    intro inst
    ext idx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨((flatEquiv widths hsize).symm idx).1, ?_⟩
      unfold solutionVector at h
      simp only [Spec.elementary] at h
      by_cases hp : ((flatEquiv widths hsize).symm idx).2 =
          selectAddress widths (formatWitness widths bits ((flatEquiv widths hsize).symm idx).1)
      · rw [← hp, Prod.mk.eta, Equiv.apply_symm_apply]
      · exact absurd (by simp [hp]) h
    · rintro ⟨i, rfl⟩
      unfold solutionVector
      simp [Spec.elementary]
  rw [himage, Finset.card_image_of_injective _ (fun i i' h => ?_), Finset.card_univ, Fintype.card_fin]
  have := congrArg Prod.fst ((flatEquiv widths hsize).injective h)
  exact this

section Setting

open Spec.SharedSigning

variable {lambda tau kappa s higherCount wpow : Nat} {F : Type} [Field F] [Algebra (ZMod 2) F]

omit [Field F] [Algebra (ZMod 2) F] in
/-- An extracted solution is a weight-`w` solution of the public instance. -/
theorem isSolution_sd (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (bits : Fin (selectorCount widths * w) → ZMod 2) (h : IsSolution S bits) :
    Spec.SDSolution (Spec.KeyGeneration.instanceOf S.H' S.y) w (solutionVector widths S.hsize bits) :=
  (KeyGeneration.instanceOf_solution_iff S.H' S.y _).mpr
    ⟨mulVec_eq_of_residual widths S.hsize S.H' S.y bits h.1 h.2, hammingWeight_solutionVector widths S.hsize bits⟩

end Setting

end
end SDitH.Proofs.SolutionRegular
