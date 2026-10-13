import SDitH.Proofs.FieldRepresentation

/-! The full polynomial-basis linear isomorphism phi on printed p. 34.
Only monicity is needed for this representation result; the field structure
from irreducibility is a separate established theorem. -/

namespace SDitH.Proofs.FieldIsomorphism

open Spec.FieldRepresentation FieldRepresentation
open scoped BigOperators

noncomputable def submittedBasis (category : Category) :
    Module.Basis (Fin (width category)) (ZMod 2) (QuotientRing category) :=
  (AdjoinRoot.powerBasis' (modulus_monic category)).basis.reindex
    (finCongr (modulus_degree category))

theorem submittedBasis_apply (category : Category) (i : Fin (width category)) :
    submittedBasis category i = generator category ^ i.val := by
  rw [submittedBasis, Module.Basis.reindex_apply]
  change (AdjoinRoot.powerBasis' (modulus_monic category)).basis
    ((finCongr (modulus_degree category)).symm i) = _
  rw [PowerBasis.coe_basis]
  rfl

noncomputable def coefficientEquiv (category : Category) :
    (Fin (width category) → ZMod 2) ≃ₗ[ZMod 2] QuotientRing category :=
  (submittedBasis category).equivFun.symm

theorem coefficientEquiv_apply (category : Category) (v : Fin (width category) → ZMod 2) :
    coefficientEquiv category v = encodeCoefficients category v := by
  simp only [coefficientEquiv, Module.Basis.equivFun_symm_apply, submittedBasis_apply,
    Algebra.smul_def, encodeCoefficients]

/-- Every submitted field element has exactly one full coefficient vector.
This proves both directions of the representation, beyond injectivity alone. -/
theorem encodeCoefficients_bijective (category : Category) :
    Function.Bijective (encodeCoefficients category (n := width category)) := by
  have he : encodeCoefficients category (n := width category) = coefficientEquiv category := by
    funext v
    exact (coefficientEquiv_apply category v).symm
  rw [he]
  exact (coefficientEquiv category).bijective

theorem encode_decode_coefficients (category : Category) (x : QuotientRing category) :
    encodeCoefficients category ((coefficientEquiv category).symm x) = x := by
  rw [← coefficientEquiv_apply, LinearEquiv.apply_symm_apply]

theorem decode_encode_coefficients (category : Category) (v : Fin (width category) → ZMod 2) :
    (coefficientEquiv category).symm (encodeCoefficients category v) = v := by
  rw [← coefficientEquiv_apply, LinearEquiv.symm_apply_apply]

end SDitH.Proofs.FieldIsomorphism
