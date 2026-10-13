import SDitH.Proofs.ScaledWitness

/-! A concrete degree-four scaled mux with the [4,4,4] arities of Table 7.
All selector and amplitude inputs are lines; the amplitude constant is one.
This checks the extra degree used by Table 8 without claiming a full F256
PIOP implementation or resolving the source's mux/witness indexing conflict.
-/

namespace SDitH.Proofs.ScaledMuxDegree

open Polynomial Spec.ScaledWitness Spec.PIOPArithmetic

variable {F : Type*} [Field F]

noncomputable def selectorLine : Fin 3 → F[X] := fun j => if j.val = 0 then X else 0

noncomputable def selectors : Selectors F[X] [3,3,3] :=
  (selectorLine, selectorLine, selectorLine, PUnit.unit)

def leaves : Fin (leafCount [3,3,3]) → F := fun j => if j.val = 21 then 1 else 0

theorem selectors_linear : LinearSelectors [3,3,3] (selectors (F := F)) := by
  have h : ∀ j : Fin 3, (selectorLine (F := F) j).natDegree ≤ 1 := by
    intro j
    unfold selectorLine
    split_ifs <;> simp
  exact ⟨h, h, h, trivial⟩

theorem amplitude_nonzero_constant : (X + 1 : F[X]).eval 0 ≠ 0 := by simp

theorem output_polynomial :
    scaledMux (X + 1) [3,3,3] selectors (fun j => C (leaves j)) =
      (X ^ 4 + X ^ 3 : F[X]) := by
  norm_num [scaledMux, selectors, selectorLine, leaves, muxTree, mux, blockIndex,
    Fin.sum_univ_succ]
  ring

/-- The additional degree can actually occur; three tensor layers do not
give a general degree-three bound once the amplitude line is included. -/
theorem output_degree :
    (scaledMux (X + 1 : F[X]) [3,3,3] selectors (fun j => C (leaves j))).natDegree = 4 := by
  rw [output_polynomial]
  compute_degree <;> norm_num

end SDitH.Proofs.ScaledMuxDegree
