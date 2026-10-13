import SDitH.Proofs.ViewBijection

/-! The honest revealed data as a bijective image of the view, hence uniform
and witness-independent under a uniform hidden vector. The honest data
(witness correction, hashed coefficients below the top, plain check) is the
view with its middle component reversed in the layer index and translated
by the witness-dependent zero-randomness coefficients and the slope terms;
reversal and translation are bijections, so a uniform hidden vector gives
uniform honest data whatever the witness. The PRG hypothesis that supplies
the uniform hidden vector is the remaining input. -/

namespace SDitH.Proofs.HonestViewUniform

open Spec.FieldRepresentation ViewBijection
open scoped BigOperators Classical

noncomputable section

variable (category : Category) {s wit d : Nat}

/-- The layer index of the hashed coefficient j: layer d-2-j. -/
def layerRev (j : Fin (d - 1)) : Fin (d - 1) := ⟨d - 2 - j.val, by have := j.isLt; omega⟩

theorem layerRev_involutive : Function.Involutive (layerRev (d := d)) := by
  intro j
  apply Fin.ext
  have := j.isLt
  simp only [layerRev]
  omega

/-- The honest revealed data: witness correction, hashed coefficients below
the top (zero-randomness coefficient plus the view's reversed packed layer
plus the slope term), plain check. -/
def honestData (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2) (Qc st : Fin (d - 1) → QuotientRing category)
    (r : Fin (s + (wit + width category * (d - 1))) → ZMod 2) :
    (Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2) :=
  let v := viewMap category M A B Cc r
  (v.1, fun j => (Qc j + st j) + v.2.1 (layerRev j), v.2.2)

/-- The post-processing of the view: reversal and translation of the middle
component, as an equivalence. -/
def postEquiv (Qc st : Fin (d - 1) → QuotientRing category) :
    ((Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2)) ≃
      ((Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2)) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr
    ((Equiv.arrowCongr (Function.Involutive.toPerm layerRev layerRev_involutive) (Equiv.refl _)).trans
      (Equiv.addLeft (Qc + st)))
    (Equiv.refl _))

theorem honestData_eq (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2) (Qc st : Fin (d - 1) → QuotientRing category)
    (r : Fin (s + (wit + width category * (d - 1))) → ZMod 2) :
    honestData category M A B Cc Qc st r = postEquiv category Qc st (viewMap category M A B Cc r) := by
  unfold honestData postEquiv
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  show (Qc j + st j) + (viewMap category M A B Cc r).2.1 (layerRev j) =
    (Qc + st) j + (viewMap category M A B Cc r).2.1 ((Function.Involutive.toPerm layerRev layerRev_involutive).symm j)
  rfl

/-- Under a uniform hidden vector the honest data is uniform, whatever the
witness-dependent constants. -/
theorem honestData_uniform (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2) (Qc st : Fin (d - 1) → QuotientRing category) :
    (PMF.uniformOfFintype (Fin (s + (wit + width category * (d - 1))) → ZMod 2)).map
        (honestData category M A B Cc Qc st) =
      PMF.uniformOfFintype ((Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2)) := by
  have h : honestData category M A B Cc Qc st = postEquiv category Qc st ∘ viewMap category M A B Cc := by
    funext r
    exact honestData_eq category M A B Cc Qc st r
  rw [h, ← PMF.map_comp, view_uniform]
  exact IntegerSamplingProbability.map_uniform_equiv (postEquiv category Qc st)

/-- The honest data's distribution does not depend on the witness-dependent
constants. -/
theorem honestData_independent (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2))
    (A A' : Fin wit → ZMod 2) (B B' : Fin (d - 1) → QuotientRing category) (Cc Cc' : Fin s → ZMod 2)
    (Qc Qc' st st' : Fin (d - 1) → QuotientRing category) :
    (PMF.uniformOfFintype (Fin (s + (wit + width category * (d - 1))) → ZMod 2)).map
        (honestData category M A B Cc Qc st) =
      (PMF.uniformOfFintype (Fin (s + (wit + width category * (d - 1))) → ZMod 2)).map
        (honestData category M A' B' Cc' Qc' st') := by
  rw [honestData_uniform, honestData_uniform]

end
end SDitH.Proofs.HonestViewUniform
