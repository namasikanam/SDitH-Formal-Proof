import SDitH.Spec.Batching
import Mathlib.Tactic

namespace SDitH.Proofs.Batching

open Spec.Batching
open scoped BigOperators

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

/-- The linear-map implementation equals the literal zero-padded block formula. -/
theorem packBlock_formula {r lambda : Nat} (ξ : F)
    (block : Fin (blockCount r lambda)) (v : Fin r → K) :
    packBlockLinear ξ block v =
      ∑ j : Fin lambda, ξ ^ j.val *
        (if h : block.val * lambda + j.val < r then
          algebraMap K F (v ⟨block.val * lambda + j.val, h⟩) else 0) := by
  unfold packBlockLinear
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [LinearMap.smulRight_apply, Algebra.smul_def, mul_comm]

/-- The implementation is the dot product with the block vector Φ(v). -/
theorem batch_formula {r lambda : Nat} (ξ : F)
    (gamma : Fin (blockCount r lambda) → F) (v : Fin r → K) :
    batchLinearMap ξ gamma v = ∑ block, gamma block * packVector ξ v block := by
  simp [batchLinearMap, packVector, LinearMap.sum_apply]

/-- Equation (8) for an arbitrary expanded syndrome matrix.
No assumption that x is a solution is needed: this computes the residual. -/
theorem batch_residual {r n lambda : Nat} (ξ : F)
    (gamma : Fin (blockCount r lambda) → F)
    (H : Matrix (Fin r) (Fin n) K) (x : Fin n → K) (y : Fin r → K) :
    batchLinearMap ξ gamma (H.mulVec x - y) =
      (∑ j, algebraMap K F (x j) * batchLinearMap ξ gamma (fun i => H i j)) -
        batchLinearMap ξ gamma y := by
  have hm : H.mulVec x = ∑ j, x j • (fun i => H i j) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hm, map_sub, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.map_smul, Algebra.smul_def]

/-- In particular, satisfying the actual linear SD relation makes the batched
residual zero. The converse needs injectivity/probability arguments not assumed here. -/
theorem solution_has_zero_batch {r n lambda : Nat} (ξ : F)
    (gamma : Fin (blockCount r lambda) → F)
    (H : Matrix (Fin r) (Fin n) K) (x : Fin n → K) (y : Fin r → K)
    (h : H.mulVec x = y) :
    (∑ j, algebraMap K F (x j) * batchLinearMap ξ gamma (fun i => H i j)) -
      batchLinearMap ξ gamma y = 0 := by
  rw [← batch_residual, h, sub_self, map_zero]

end SDitH.Proofs.Batching
