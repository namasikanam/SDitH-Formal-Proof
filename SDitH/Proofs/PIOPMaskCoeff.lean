import SDitH.Proofs.PIOPMaskSplit

/-! The coefficients of the formatted mask. Each layer's packed randomness
polynomial is multiplied by a power of X decreasing in the layer index, so
the k-th coefficient of the mask is the k-shifted coefficient of the layer
whose power is at most k. For randomness lines (degree at most one), the
k-th coefficient is the packed constant of layer d-2-k plus the packed
slope of layer d-1-k, and the hashed coefficients of the prover polynomial
are the zero-randomness coefficients padded by them. -/

namespace SDitH.Proofs.PIOPMaskCoeff

open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Polynomial
open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The packed polynomial of one layer. -/
def packed {lambda : Nat} (xi : R) (layer : Fin lambda → R[X]) : R[X] :=
  ∑ j, (C xi) ^ j.val * layer j

theorem formatMask_eq_sum {d lambda : Nat} (xi : R) (r : Fin (d - 1) → Fin lambda → R[X]) :
    formatMask (C xi) X r = ∑ i, packed xi (r i) * X ^ (d - 2 - i.val) := rfl

/-- The generic coefficient formula. -/
theorem formatMask_coeff {d lambda : Nat} (xi : R) (r : Fin (d - 1) → Fin lambda → R[X]) (k : Nat) :
    (formatMask (C xi) X r).coeff k =
      ∑ i, if d - 2 - i.val ≤ k then (packed xi (r i)).coeff (k - (d - 2 - i.val)) else 0 := by
  rw [formatMask_eq_sum, finset_sum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact coeff_mul_X_pow' _ _ _

/-- The constant and linear coefficients of a packed line, and its vanishing
higher coefficients. -/
theorem packed_line_coeff_zero {lambda : Nat} (xi : R) (a b : Fin lambda → R) :
    (packed xi (fun j => C (a j) + C (b j) * X)).coeff 0 = ∑ j, xi ^ j.val * a j := by
  unfold packed
  rw [finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← C_pow, coeff_C_mul, coeff_add, coeff_C_mul_X, coeff_C]
  simp

theorem packed_line_coeff_one {lambda : Nat} (xi : R) (a b : Fin lambda → R) :
    (packed xi (fun j => C (a j) + C (b j) * X)).coeff 1 = ∑ j, xi ^ j.val * b j := by
  unfold packed
  rw [finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← C_pow, coeff_C_mul, coeff_add, coeff_C_mul_X, coeff_C]
  simp

theorem packed_line_coeff_higher {lambda : Nat} (xi : R) (a b : Fin lambda → R) (m : Nat) :
    (packed xi (fun j => C (a j) + C (b j) * X)).coeff (m + 2) = 0 := by
  unfold packed
  rw [finset_sum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← C_pow, coeff_C_mul, coeff_add, coeff_C_mul_X, coeff_C]
  simp

/-- For randomness lines, the k-th mask coefficient is the packed constant of
layer d-2-k plus the packed slope of layer d-1-k (when those layers exist). -/
theorem formatMask_coeff_lines {d lambda : Nat} (xi : R) (a b : Fin (d - 1) → Fin lambda → R) (k : Nat) :
    (formatMask (C xi) X (fun i j => C (a i j) + C (b i j) * X)).coeff k =
      (∑ i : Fin (d - 1), if i.val = d - 2 - k ∧ k + 2 ≤ d then ∑ j, xi ^ j.val * a i j else 0) +
      (∑ i : Fin (d - 1), if i.val = d - 1 - k ∧ 1 ≤ k ∧ k + 1 ≤ d then ∑ j, xi ^ j.val * b i j else 0) := by
  rw [formatMask_coeff, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  by_cases hle : d - 2 - i.val ≤ k
  · rw [if_pos hle]
    obtain ⟨m, hm⟩ : ∃ m, k = d - 2 - i.val + m := ⟨k - (d - 2 - i.val), by omega⟩
    subst hm
    rw [Nat.add_sub_cancel_left]
    rcases m with _ | _ | m
    · rw [packed_line_coeff_zero, if_pos (by omega), if_neg (by omega), add_zero]
    · rw [packed_line_coeff_one, if_neg (by omega), if_pos (by omega), zero_add]
    · rw [packed_line_coeff_higher, if_neg (by omega), if_neg (by omega), add_zero]
  · rw [if_neg hle, if_neg (by omega), if_neg (by omega), add_zero]

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

/-- The hashed coefficients of the prover polynomial are the zero-randomness
coefficients padded by the mask coefficients. -/
theorem proverRun_coeff_succ {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F) (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F[X]) (randomness : Fin (lambda * (widths.length - 1)) → F[X]) (n : Nat) :
    (proverRun widths hsize xi gamma gammaPrime H' y witness randomness).coeff (n + 1) =
      (proverRun widths hsize xi gamma gammaPrime H' y witness 0).coeff (n + 1) +
        (formatMask (C xi) X (formatRandomness randomness)).coeff n := by
  rw [PIOPMaskSplit.proverRun_split, coeff_add, coeff_mul_X]

end
end SDitH.Proofs.PIOPMaskCoeff
