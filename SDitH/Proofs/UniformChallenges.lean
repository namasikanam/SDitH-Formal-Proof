import SDitH.Spec.UniformChallenges
import SDitH.Proofs.PolynomialBounds
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

namespace SDitH.Proofs.UniformChallenges

open Spec.UniformChallenges
open scoped BigOperators ENNReal Classical

theorem probability_card {A : Type*} [Fintype A] [Nonempty A] (event : A → Prop) :
    probability event = (Fintype.card {a // event a} : ℝ≥0∞) / Fintype.card A := by
  classical
  exact PMF.toOuterMeasure_uniformOfFintype_apply {a | event a}

theorem subset_probability_card {A : Type*} (sample : Finset A) (hne : sample.Nonempty)
    (event : A → Prop) :
    subsetProbability sample hne event =
      ((sample.filter event).card : ℝ≥0∞) / sample.card := by
  classical
  exact PMF.toOuterMeasure_uniformOfFinset_apply hne {a | event a}

theorem subset_probability_mono {A : Type*} (sample : Finset A) (hne : sample.Nonempty)
    (event event' : A → Prop) (h : ∀ a, event a → event' a) :
    subsetProbability sample hne event ≤ subsetProbability sample hne event' := by
  rw [subset_probability_card, subset_probability_card]
  apply ENNReal.div_le_div_right _ _
  exact_mod_cast Finset.card_le_card (show sample.filter event ⊆ sample.filter event' from by
    intro a ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, h a (Finset.mem_filter.mp ha).2⟩)

/-- A nonzero polynomial fixed before a uniform sample from S has root
probability at most degree/|S|. The nonzero premise is explicit. -/
theorem polynomial_root_probability {F : Type*} [Field F]
    (p : Polynomial F) (hp : p ≠ 0) (sample : Finset F) (hne : sample.Nonempty)
    (d : Nat) (hdegree : p.natDegree ≤ d) :
    subsetProbability sample hne (fun x => p.eval x = 0) ≤
      (d : ℝ≥0∞) / sample.card := by
  classical
  rw [subset_probability_card]
  exact ENNReal.div_le_div_right (by exact_mod_cast residual_root_count p hp sample d hdegree) _

/-- A surjective linear form has exactly a 1/|F| fraction of its domain in
its kernel. This is a statement about the defined uniform sampler. -/
theorem linear_kernel_probability {F M : Type*} [Field F] [Fintype F]
    [AddCommGroup M] [Module F M] [Fintype M]
    (L : M →ₗ[F] F) (hsurj : Function.Surjective L) :
    probability (fun x => L x = 0) = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  classical
  rw [probability_card]
  change (Fintype.card L.ker : ℝ≥0∞) / Fintype.card M = _
  have hc := L.ker.card_eq_card_quotient_mul_card
  rw [Nat.card_congr (L.quotKerEquivOfSurjective hsurj).toEquiv] at hc
  simp only [Nat.card_eq_fintype_card] at hc
  have hce : (Fintype.card M : ℝ≥0∞) =
      (Fintype.card L.ker : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞) := by exact_mod_cast hc
  have hk0 : (Fintype.card L.ker : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hkt : (Fintype.card L.ker : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [hce, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hk0) (Or.inl hkt), ← mul_assoc,
    ENNReal.mul_inv_cancel hk0 hkt, one_mul]

noncomputable def batchLinearForm {I F : Type*} [Fintype I] [Field F]
    (values : I → F) : (I → F) →ₗ[F] F where
  toFun := linearBatch values
  map_add' a b := by simp [linearBatch, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [linearBatch, Finset.mul_sum, mul_assoc]

theorem batchLinearForm_surjective {I F : Type*} [Fintype I] [Field F]
    (values : I → F) (j : I) (hj : values j ≠ 0) :
    Function.Surjective (batchLinearForm values) := by
  classical
  intro y
  refine ⟨Pi.single j (y / values j), ?_⟩
  simp [batchLinearForm, linearBatch, Pi.single_apply, hj]

/-- Independent uniform coefficients (the uniform law on the full function
space) cancel a fixed nonzero vector with probability exactly 1/|F|. -/
theorem linear_batch_probability {I F : Type*} [Fintype I] [DecidableEq I] [Field F] [Fintype F]
    (values : I → F) (hvalues : values ≠ 0) :
    probability (fun gamma => linearBatch values gamma = 0) =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hj : ∃ j, values j ≠ 0 := by
    by_contra h
    apply hvalues
    funext j
    exact not_not.mp (not_exists.mp h j)
  obtain ⟨j, hj⟩ := hj
  exact linear_kernel_probability (batchLinearForm values)
    (batchLinearForm_surjective values j hj)

/-- Every fiber of a surjective linear form has the same uniform probability.
The target is fixed before sampling the input. -/
theorem linear_fiber_probability {F M : Type*} [Field F] [Fintype F]
    [AddCommGroup M] [Module F M] [Fintype M]
    (L : M →ₗ[F] F) (hsurj : Function.Surjective L) (target : F) :
    probability (fun x => L x = target) = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  obtain ⟨x0, hx0⟩ := hsurj target
  let e : {x // L x = 0} ≃ {x // L x = target} :=
    { toFun := fun x => ⟨x.val + x0, by simp [map_add, x.property, hx0]⟩
      invFun := fun x => ⟨x.val - x0, by simp [map_sub, x.property, hx0]⟩
      left_inv := fun x => Subtype.ext (add_sub_cancel_right x.val x0)
      right_inv := fun x => Subtype.ext (sub_add_cancel x.val x0) }
  rw [← linear_kernel_probability L hsurj, probability_card, probability_card,
    Fintype.card_congr e]

/-- A fixed additive offset does not change the exact cancellation probability
of a nonzero linear batch. This also applies after fixing an independent earlier
challenge and its resulting offset. -/
theorem affine_batch_probability {I F : Type*} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] (values : I → F) (hvalues : values ≠ 0) (offset : F) :
    probability (fun gamma => offset + linearBatch values gamma = 0) =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  obtain ⟨j, hj⟩ : ∃ j, values j ≠ 0 := by
    by_contra h
    exact hvalues (funext fun j => not_not.mp (not_exists.mp h j))
  have h := linear_fiber_probability (batchLinearForm values)
    (batchLinearForm_surjective values j hj) (-offset)
  simpa only [batchLinearForm, LinearMap.coe_mk, AddHom.coe_mk,
    add_eq_zero_iff_eq_neg'] using h

end SDitH.Proofs.UniformChallenges
