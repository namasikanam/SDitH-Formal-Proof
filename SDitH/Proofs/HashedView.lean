import SDitH.Proofs.HashedPads
import SDitH.Proofs.CorrectionTranslation

/-! The hashed coefficients below the top as the view's packed layer
constants plus witness-free terms. For randomness lines whose constants
are the algebra images of the accumulator's randomness coordinates, the
k-th hashed coefficient (k at most d-2) is the zero-randomness coefficient
plus the packed constant of layer d-2-k of the accumulator plus a slope
term; the packed constant is additive, so splitting the accumulator into
the hidden vector and the others exhibits the hidden vector's packed layer
as the pad. -/

namespace SDitH.Proofs.HashedView

open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Spec.CoefficientCompression Spec.BLC
open Polynomial HashedPads
open scoped BigOperators Classical

noncomputable section

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

theorem packedConst_add {lambda : Nat} (xi : F) (bits bits' : Fin lambda → K) :
    packedConst xi (bits + bits') = packedConst xi bits + packedConst xi bits' := by
  unfold packedConst
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/-- The mask coefficient below the top for bit-constant lines: the packed
constant of layer d-2-k plus the slope term of layer d-1-k. -/
theorem formatMask_coeff_below {d lambda : Nat} (xi : F) (bits : Fin (d - 1) → Fin lambda → K)
    (b : Fin (d - 1) → Fin lambda → F) (k : Nat) (hk : k + 2 ≤ d) :
    (formatMask (C xi) X (fun i j => C (algebraMap K F (bits i j)) + C (b i j) * X)).coeff k =
      packedConst xi (bits ⟨d - 2 - k, by omega⟩) +
        (if h1 : 1 ≤ k then ∑ j, xi ^ j.val * b ⟨d - 1 - k, by omega⟩ j else 0) := by
  rw [formatMask_coeff_bits]
  congr 1
  · rw [Finset.sum_eq_single ⟨d - 2 - k, by omega⟩]
    · rw [if_pos ⟨rfl, hk⟩]
    · intro i _ hi
      rw [if_neg]
      intro h
      exact hi (Fin.ext h.1)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · by_cases h1 : 1 ≤ k
    · rw [dif_pos h1, Finset.sum_eq_single ⟨d - 1 - k, by omega⟩]
      · rw [if_pos ⟨rfl, h1, by omega⟩]
      · intro i _ hi
        rw [if_neg]
        intro h
        exact hi (Fin.ext h.1)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [dif_neg h1]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      exact h1 h.2.1

/-- A layer of the accumulator's randomness coordinates. -/
def layerBits {tau N kappa s wit lambda d : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + lambda * (d - 1))) → K) (i : Fin (d - 1)) : Fin lambda → K :=
  fun j => commonAcc phi random (randomnessIndex (blockIndex i j))

/-- A layer of one party's randomness coordinates. -/
def layerBitsOf {s wit lambda d : Nat} (r : Fin (s + (wit + lambda * (d - 1))) → K) (i : Fin (d - 1)) : Fin lambda → K :=
  fun j => r (randomnessIndex (blockIndex i j))

/-- The accumulator's layer splits into the hidden party's layer and the others'. -/
theorem layerBits_translate {tau N kappa s wit lambda d : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + lambda * (d - 1))) → K) (h : Fin N) (i : Fin (d - 1)) :
    layerBits phi random i = layerBitsOf (random 0 h) i + layerBitsOf (HiddenShareTranslation.others random h) i := by
  funext j
  simp only [layerBits, layerBitsOf, Pi.add_apply]
  exact HiddenShareTranslation.commonAcc_translate phi random h _

/-- The formatted randomness of the honest lines has the bit-constant shape. -/
theorem formatRandomness_lines {tau N kappa s wit lambda d : Nat} [NeZero tau] (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + lambda * (d - 1))) → K)
    (M : Matrix (Fin s) (Fin (wit + lambda * (d - 1))) K) (witness : Fin wit → K) :
    formatRandomness (commitArithmetic xi phi random M witness).randomnessLines =
      fun i j => C (algebraMap K F (layerBits phi random i j)) +
        C (psi xi (baseRow phi random (randomnessIndex (blockIndex i j)))) * X := by
  funext i j
  simp [formatRandomness, commitArithmetic, buildLine, layerBits]

end
end SDitH.Proofs.HashedView
