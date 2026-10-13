import SDitH.Proofs.CorrectionTranslation
import SDitH.Proofs.PackingUniform

/-! The positive executions' corrections are one-time pads. Each execution's
correction is a value depending on the common accumulator and that
execution's other parties minus the execution's hidden vector, so the map
from the hidden vector to the correction is a bijection (negation then
translation), and a uniform hidden vector gives a uniform correction
whatever the constants. Together with execution zero's revealed data, every
transmitted auxiliary row is padded by its own execution's hidden vector. -/

namespace SDitH.Proofs.CorrectionUniform

open Spec.BLC CorrectionTranslation
open scoped BigOperators Classical

noncomputable section

section Generic

variable {G : Type*} [AddCommGroup G] [Fintype G] [Nonempty G]

/-- Subtracting a uniform pad from a fixed value is uniform. -/
theorem sub_pad_uniform (c : G) :
    (PMF.uniformOfFintype G).map (fun g => c - g) = PMF.uniformOfFintype G := by
  have h : (fun g : G => c - g) = (Equiv.neg G).trans (Equiv.addLeft c) := by
    funext g
    simp [sub_eq_add_neg]
  rw [h]
  exact IntegerSamplingProbability.map_uniform_equiv _

end Generic

variable {K : Type*} [CommRing K] [Fintype K] [Nonempty K]

/-- An execution's correction as a function of its hidden vector. -/
def correctionOf {tau N ell kappa : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (e : Fin tau) (h : Fin N) (v : Fin ell → K) : Fin ell → K :=
  fun c => (commonAcc phi random c - othersAt random e h c) - v c

omit [Fintype K] [Nonempty K] in
theorem correction_eq_correctionOf {tau N ell kappa : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (e : Fin tau) (h : Fin N) :
    correction phi random e = correctionOf phi random e h (random e h) := by
  funext c
  exact correction_translate phi random e h c

/-- A uniform hidden vector gives a uniform correction, whatever the constants. -/
theorem correctionOf_uniform {tau N ell kappa : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (e : Fin tau) (h : Fin N) :
    (PMF.uniformOfFintype (Fin ell → K)).map (correctionOf phi random e h) = PMF.uniformOfFintype (Fin ell → K) := by
  have hc : correctionOf phi random e h = fun v => (fun c => commonAcc phi random c - othersAt random e h c) - v := by
    funext v c
    rfl
  rw [hc]
  exact sub_pad_uniform _

end
end SDitH.Proofs.CorrectionUniform
