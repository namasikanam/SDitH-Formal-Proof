import SDitH.Spec.PIOPComposition

/-! The prover polynomial split into its mask part and its witness part. The
arithmetic body adds the masking polynomial times the evaluation point to a
sum depending only on the witness lines, so the prover polynomial is the
prover polynomial with zero randomness plus the formatted mask times X; the
mask is additive in the randomness. These identities are the algebraic
input of the honest-verifier zero-knowledge argument (the mask constants
pad the hashed coefficients). -/

namespace SDitH.Proofs.PIOPMaskSplit

open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Polynomial
open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem formatMask_add {d lambda : Nat} (xi z : R) (r r' : Fin (d - 1) → Fin lambda → R) :
    formatMask xi z (r + r') = formatMask xi z r + formatMask xi z r' := by
  unfold formatMask
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_mul]

theorem formatMask_zero {d lambda : Nat} (xi z : R) :
    formatMask xi z (0 : Fin (d - 1) → Fin lambda → R) = 0 := by
  simp [formatMask]

theorem formatRandomness_add {d lambda : Nat} (r r' : Fin (lambda * (d - 1)) → R) :
    formatRandomness r + formatRandomness r' = formatRandomness (r + r') := by
  funext i j
  simp [formatRandomness]

theorem formatRandomness_zero {d lambda : Nat} :
    formatRandomness (0 : Fin (lambda * (d - 1)) → R) = 0 := by
  funext i j
  simp [formatRandomness]

/-- The arithmetic body is the mask times the point plus a mask-free part. -/
theorem runArithmetic_mask {w : Nat} (widths : List Nat) (xi z mask syndrome : R) (gamma : Fin w → R)
    (selectors : Fin w → Selectors R widths) (columns : Fin w → Fin (leafCount widths) → R) :
    runArithmetic widths xi z mask syndrome gamma selectors columns =
      mask * z + runArithmetic widths xi z 0 syndrome gamma selectors columns := by
  unfold runArithmetic
  ring

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

/-- The prover polynomial is its zero-randomness value plus the formatted mask
of the randomness lines times X. -/
theorem proverRun_split {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F) (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F[X]) (randomness : Fin (lambda * (widths.length - 1)) → F[X]) :
    proverRun widths hsize xi gamma gammaPrime H' y witness randomness =
      proverRun widths hsize xi gamma gammaPrime H' y witness 0 +
        formatMask (C xi) X (formatRandomness randomness) * X := by
  unfold proverRun proverArithmeticFlat proverArithmetic
  rw [runArithmetic_mask, runArithmetic_mask _ _ _ (formatMask (C xi) X (formatRandomness 0))]
  rw [formatRandomness_zero, formatMask_zero, zero_mul, zero_add]
  ring

/-- Adding randomness lines adds their formatted mask times X. -/
theorem proverRun_add_randomness {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F) (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F[X]) (randomness randomness' : Fin (lambda * (widths.length - 1)) → F[X]) :
    proverRun widths hsize xi gamma gammaPrime H' y witness (randomness + randomness') =
      proverRun widths hsize xi gamma gammaPrime H' y witness randomness +
        formatMask (C xi) X (formatRandomness randomness') * X := by
  rw [proverRun_split, proverRun_split _ _ _ _ _ _ _ _ randomness, ← formatRandomness_add, formatMask_add]
  ring

/-- The difference of two prover polynomials with the same randomness is
mask-free: it is the difference of the zero-randomness polynomials. -/
theorem proverRun_sub_same_randomness {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (xi : F) (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F) (H' : Matrix (Fin r) (Fin k) K)
    (y : Fin r → K) (witness witness' : Fin (selectorCount widths * w) → F[X])
    (randomness : Fin (lambda * (widths.length - 1)) → F[X]) :
    proverRun widths hsize xi gamma gammaPrime H' y witness randomness -
        proverRun widths hsize xi gamma gammaPrime H' y witness' randomness =
      proverRun widths hsize xi gamma gammaPrime H' y witness 0 -
        proverRun widths hsize xi gamma gammaPrime H' y witness' 0 := by
  rw [proverRun_split, proverRun_split _ _ _ _ _ _ _ witness']
  ring

end
end SDitH.Proofs.PIOPMaskSplit
