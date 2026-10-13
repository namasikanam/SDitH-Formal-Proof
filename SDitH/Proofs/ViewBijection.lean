import SDitH.Proofs.RevealedBijection
import SDitH.Proofs.HashedPads

/-! The revealed view as an affine bijection of execution zero's hidden
vector, over the binary field with the submitted quotient ring. The view
is the witness correction, the per-layer packed constants (which pad the
hashed coefficients below the top) and the plain check; the randomness
coordinates are re-indexed into layers by the block index, each layer is
packed by the coefficient-encoding bijection and translated by the other
parties' packed constants. Hence a uniform hidden vector yields a uniform
view whatever the constants, in particular whatever the witness. -/

namespace SDitH.Proofs.ViewBijection

open Spec.BLC Spec.PIOPArithmetic Spec.FieldRepresentation RevealedBijection HashedPads PackingUniform
open scoped BigOperators Classical

noncomputable section

section Layers

variable {K : Type*} {a m : Nat}

/-- The block index as the product equivalence followed by the commutativity cast. -/
theorem blockIndex_eq (row : Fin m) (col : Fin a) :
    blockIndex row col = finCongr (Nat.mul_comm m a) (finProdFinEquiv (row, col)) := by
  ext
  simp [blockIndex, finProdFinEquiv_apply_val]
  ring

/-- Re-indexing a flat array into layers by the block index. -/
def layersEquiv : (Fin (a * m) → K) ≃ (Fin m → Fin a → K) :=
  (Equiv.arrowCongr ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m a))).symm) (Equiv.refl K)).trans
    (Equiv.curry (Fin m) (Fin a) K)

theorem layersEquiv_apply (f : Fin (a * m) → K) (row : Fin m) (col : Fin a) :
    layersEquiv f row col = f (blockIndex row col) := by
  rw [blockIndex_eq]
  rfl

end Layers

variable (category : Category) {s wit d : Nat}

/-- The view map: witness correction, packed layer constants translated by the
other parties' packed constants, and plain check. -/
def viewMap (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2)
    (r : Fin (s + (wit + width category * (d - 1))) → ZMod 2) :
    (Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2) :=
  (fun j => A j - r (witnessIndex j),
    fun i => B i + packedConst (generator category) (fun j => r (randomnessIndex (blockIndex i j))),
    fun a => consistencyCheck M r a + Cc a)

/-- The middle component's equivalence: layers, packing, translation. -/
def middleEquiv (B : Fin (d - 1) → QuotientRing category) :
    (Fin (width category * (d - 1)) → ZMod 2) ≃ (Fin (d - 1) → QuotientRing category) :=
  (layersEquiv.trans (Equiv.piCongrRight fun _ => packEquiv category)).trans (Equiv.addLeft B)

/-- The view as an equivalence. -/
def viewEquiv (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2) :
    (Fin (s + (wit + width category * (d - 1))) → ZMod 2) ≃
      (Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2) :=
  (revealedEquiv M A 0 Cc).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (middleEquiv category B) (Equiv.refl _)))

theorem viewEquiv_apply (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2)
    (r : Fin (s + (wit + width category * (d - 1))) → ZMod 2) :
    viewEquiv category M A B Cc r = viewMap category M A B Cc r := by
  unfold viewEquiv viewMap middleEquiv
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext i
  show B i + (Equiv.piCongrRight fun _ => packEquiv category) (layersEquiv ((revealedEquiv M A 0 Cc) r).2.1) i = _
  congr 1
  show encodeCoefficients category (layersEquiv ((revealedEquiv M A 0 Cc) r).2.1 i) = _
  rw [← packedConst_eq_encode]
  congr 1
  funext j
  rw [layersEquiv_apply]
  show (revealedMap M A 0 Cc r).2.1 (blockIndex i j) = _
  simp [revealedMap]

/-- A uniform hidden vector gives a uniform view, whatever the constants. -/
theorem view_uniform (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2) :
    (PMF.uniformOfFintype (Fin (s + (wit + width category * (d - 1))) → ZMod 2)).map (viewMap category M A B Cc) =
      PMF.uniformOfFintype ((Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2)) := by
  have h : viewMap category M A B Cc = viewEquiv category M A B Cc := by
    funext r
    exact (viewEquiv_apply category M A B Cc r).symm
  rw [h]
  exact IntegerSamplingProbability.map_uniform_equiv (viewEquiv category M A B Cc)

theorem view_independent (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2))
    (A A' : Fin wit → ZMod 2) (B B' : Fin (d - 1) → QuotientRing category) (Cc Cc' : Fin s → ZMod 2) :
    (PMF.uniformOfFintype (Fin (s + (wit + width category * (d - 1))) → ZMod 2)).map (viewMap category M A B Cc) =
      (PMF.uniformOfFintype (Fin (s + (wit + width category * (d - 1))) → ZMod 2)).map (viewMap category M A' B' Cc') := by
  rw [view_uniform, view_uniform]

end
end SDitH.Proofs.ViewBijection
