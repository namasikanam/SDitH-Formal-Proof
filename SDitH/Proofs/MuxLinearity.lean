import SDitH.Spec.PIOPComposition
import Mathlib.Tactic

namespace SDitH.Proofs.MuxLinearity

open Spec.PIOPArithmetic Spec.PIOPComposition Spec.Batching
open scoped BigOperators

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

/-- With selectors fixed, mux is linear in its leaves. Hence batching may be
performed before or after the literal mux, without interpreting its selectors. -/
theorem map_mux {r s : Nat} (L : (Fin r → K) →ₗ[K] F)
    (bits : Fin s → K) (leaves : Fin (s + 1) → Fin r → K) :
    L (fun row => mux bits (fun col => leaves col row)) =
      mux (fun j => algebraMap K F (bits j)) (fun col => L (leaves col)) := by
  have he : (fun row => mux bits (fun col => leaves col row)) =
      leaves 0 + ∑ j, bits j • (leaves j.succ - leaves 0) := by
    funext row
    simp [mux, Finset.sum_apply]
  rw [he, map_add, map_sum]
  simp only [mux, LinearMap.map_smul, map_sub]
  simp only [Algebra.smul_def]

theorem map_muxTree {r : Nat} (L : (Fin r → K) →ₗ[K] F)
    (widths : List Nat) (selectors : Selectors K widths)
    (leaves : Fin (leafCount widths) → Fin r → K) :
    L (fun row => muxTree widths selectors (fun col => leaves col row)) =
      muxTree widths (mapSelectors (algebraMap K F) widths selectors)
        (fun col => L (leaves col)) := by
  induction widths with
  | nil => rfl
  | cons s rest ih =>
    simp only [muxTree, mapSelectors]
    rw [ih]
    congr 1
    funext row
    exact map_mux L selectors.1 (fun col => leaves (blockIndex row col))

/-- Algorithm 21 followed by the literal mux computes the linear batch of
the actual base-field residual defined in the specification. -/
theorem batch_mux_residual {r k w lambda : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r lambda) → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (bits : Fin (selectorCount widths * w) → K) :
    batchLinearMap xi gamma (muxSyndromeResidual widths hsize H' y bits) =
      -(batchLinearEquations xi gamma H' y).2 + ∑ i,
        muxTree widths (mapSelectors (algebraMap K F) widths (formatWitness widths bits i))
          (chunkColumns widths hsize (batchLinearEquations xi gamma H' y).1 i) := by
  have he : muxSyndromeResidual widths hsize H' y bits =
      -y + ∑ i, (fun row => muxTree widths (formatWitness widths bits i)
        (chunkColumns widths hsize (systematicLeft H' row) i)) := by
    funext row
    simp [muxSyndromeResidual, Finset.sum_apply]
  rw [he, map_add, map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact map_muxTree (batchLinearMap xi gamma) widths (formatWitness widths bits i)
    (fun col row => chunkColumns widths hsize (systematicLeft H' row) i col)

end SDitH.Proofs.MuxLinearity
