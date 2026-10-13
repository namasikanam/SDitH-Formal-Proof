import SDitH.Proofs.HonestViewUniform
import SDitH.Proofs.CorrectionUniform

/-! The joint pad over all executions. Execution zero's hidden vector
determines the revealed data through a bijection, and each positive
execution's correction is a constant (depending on execution zero's vector)
minus that execution's hidden vector; the joint map from all hidden vectors
to the revealed data and corrections is therefore a triangular bijection
(a shear), so independent uniform hidden vectors give a uniform joint
transcript whatever the constants, in particular whatever the witness. -/

namespace SDitH.Proofs.JointPads

open scoped BigOperators Classical

noncomputable section

section Generic

variable {X Y : Type*} {G : Type*} [AddCommGroup G] {m ell : Nat}

/-- The joint map: a bijection of the first vector, and for each positive
execution a constant depending on the first vector minus that execution's
vector. -/
def jointMap (f : X ≃ Y) (K0 : X → Fin m → Fin ell → G) (p : X × (Fin m → Fin ell → G)) :
    Y × (Fin m → Fin ell → G) :=
  (f p.1, fun e => K0 p.1 e - p.2 e)

/-- The joint map as a shear equivalence. -/
def jointEquiv (f : X ≃ Y) (K0 : X → Fin m → Fin ell → G) : X × (Fin m → Fin ell → G) ≃ Y × (Fin m → Fin ell → G) :=
  Equiv.prodShear f fun x => Equiv.piCongrRight fun e => (Equiv.neg (Fin ell → G)).trans (Equiv.addLeft (K0 x e))

theorem jointEquiv_apply (f : X ≃ Y) (K0 : X → Fin m → Fin ell → G) (p : X × (Fin m → Fin ell → G)) :
    jointEquiv f K0 p = jointMap f K0 p := by
  unfold jointEquiv jointMap
  refine Prod.ext rfl ?_
  funext e c
  show K0 p.1 e c + -p.2 e c = K0 p.1 e c - p.2 e c
  rw [sub_eq_add_neg]

/-- Independent uniform hidden vectors give a uniform joint transcript. -/
theorem jointMap_uniform [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] [Fintype G] [Nonempty G]
    (f : X ≃ Y) (K0 : X → Fin m → Fin ell → G) :
    (PMF.uniformOfFintype (X × (Fin m → Fin ell → G))).map (jointMap f K0) =
      PMF.uniformOfFintype (Y × (Fin m → Fin ell → G)) := by
  have h : jointMap f K0 = jointEquiv f K0 := by
    funext p
    exact (jointEquiv_apply f K0 p).symm
  rw [h]
  exact IntegerSamplingProbability.map_uniform_equiv (jointEquiv f K0)

/-- The joint transcript's distribution does not depend on the bijection or
the constants. -/
theorem jointMap_independent [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] [Fintype G] [Nonempty G]
    (f f' : X ≃ Y) (K0 K0' : X → Fin m → Fin ell → G) :
    (PMF.uniformOfFintype (X × (Fin m → Fin ell → G))).map (jointMap f K0) =
      (PMF.uniformOfFintype (X × (Fin m → Fin ell → G))).map (jointMap f' K0') := by
  rw [jointMap_uniform, jointMap_uniform]

end Generic

open Spec.FieldRepresentation HonestViewUniform ViewBijection

variable (category : Category) {s wit d : Nat}

/-- The honest data map as an equivalence (the view followed by the
post-processing). -/
def honestDataEquiv (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2) (Qc st : Fin (d - 1) → QuotientRing category) :
    (Fin (s + (wit + width category * (d - 1))) → ZMod 2) ≃
      ((Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2)) :=
  (viewEquiv category M A B Cc).trans (postEquiv category Qc st)

theorem honestDataEquiv_apply (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2)) (A : Fin wit → ZMod 2)
    (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2) (Qc st : Fin (d - 1) → QuotientRing category)
    (r : Fin (s + (wit + width category * (d - 1))) → ZMod 2) :
    honestDataEquiv category M A B Cc Qc st r = honestData category M A B Cc Qc st r := by
  unfold honestDataEquiv
  rw [Equiv.trans_apply, viewEquiv_apply, honestData_eq]

/-- The joint transcript of execution zero's data and the positive executions'
corrections is uniform under independent uniform hidden vectors, whatever
the witness-dependent constants and the correction constants. -/
theorem joint_transcript_uniform {m : Nat} (M : Matrix (Fin s) (Fin (wit + width category * (d - 1))) (ZMod 2))
    (A : Fin wit → ZMod 2) (B : Fin (d - 1) → QuotientRing category) (Cc : Fin s → ZMod 2)
    (Qc st : Fin (d - 1) → QuotientRing category)
    (K0 : (Fin (s + (wit + width category * (d - 1))) → ZMod 2) → Fin m → Fin (s + (wit + width category * (d - 1))) → ZMod 2) :
    (PMF.uniformOfFintype ((Fin (s + (wit + width category * (d - 1))) → ZMod 2) ×
        (Fin m → Fin (s + (wit + width category * (d - 1))) → ZMod 2))).map
        (jointMap (honestDataEquiv category M A B Cc Qc st) K0) =
      PMF.uniformOfFintype (((Fin wit → ZMod 2) × (Fin (d - 1) → QuotientRing category) × (Fin s → ZMod 2)) ×
        (Fin m → Fin (s + (wit + width category * (d - 1))) → ZMod 2)) :=
  jointMap_uniform _ _

end
end SDitH.Proofs.JointPads
