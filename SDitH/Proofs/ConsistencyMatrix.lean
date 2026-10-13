import SDitH.Spec.ConsistencyMatrix
import SDitH.Proofs.UniformChallenges
import SDitH.Proofs.BLCSeedLines

/-! A fixed nonzero vector is annihilated by [I | M], for uniform M, with
probability at most |K|^(-s): exactly that value when its payload part is
nonzero, and never when only its top part is nonzero. Consequently two
distinct fixed slopes have equal masked images with probability at most
|K|^(-s). These are statements about the defined uniform matrix sampler. -/

namespace SDitH.Proofs.ConsistencyMatrix

open Spec.ConsistencyMatrix Spec.UniformChallenges
open scoped BigOperators ENNReal Classical

variable {K : Type*} [CommRing K] {s payload : Nat}

theorem masked_split (M : Matrix (Fin s) (Fin payload) K) (d : Fin (s + payload) → K) (a : Fin s) :
    masked M d a = top d a + ∑ b, M a b * bottom d b := by
  simp only [masked, top, bottom, Fin.sum_univ_add, Spec.Batching.systematicLeft, Fin.addCases_left,
    Fin.addCases_right]
  simp [ite_mul, Finset.sum_ite_eq]

theorem masked_sub (M : Matrix (Fin s) (Fin payload) K) (x y : Fin (s + payload) → K) (a : Fin s) :
    masked M (x - y) a = masked M x a - masked M y a := by
  simp only [masked, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem vector_ext {d : Fin (s + payload) → K} (htop : top d = 0) (hbottom : bottom d = 0) : d = 0 := by
  funext c
  refine Fin.addCases (fun a => ?_) (fun b => ?_) c
  · exact congrFun htop a
  · exact congrFun hbottom b

theorem probability_mono {A : Type*} [Fintype A] [Nonempty A] (event event' : A → Prop)
    (h : ∀ a, event a → event' a) : probability event ≤ probability event' := by
  rw [UniformChallenges.probability_card, UniformChallenges.probability_card]
  exact ENNReal.div_le_div_right (by exact_mod_cast Fintype.card_subtype_mono event event' h) _

theorem probability_of_empty {A : Type*} [Fintype A] [Nonempty A] (event : A → Prop)
    (h : ∀ a, ¬ event a) : probability event = 0 := by
  rw [UniformChallenges.probability_card]
  have hc : Fintype.card {a // event a} = 0 := Fintype.card_eq_zero_iff.mpr ⟨fun x => h x.val x.property⟩
  simp [hc]

/-- Every fiber of a surjective linear map into a finite module has the
same uniform probability 1/|V|. -/
theorem linear_map_fiber_probability {F M V : Type*} [Field F] [Fintype F]
    [AddCommGroup M] [Module F M] [Fintype M] [AddCommGroup V] [Module F V] [Fintype V]
    (L : M →ₗ[F] V) (hsurj : Function.Surjective L) (target : V) :
    probability (fun x => L x = target) = (Fintype.card V : ℝ≥0∞)⁻¹ := by
  obtain ⟨x0, hx0⟩ := hsurj target
  let e : {x // L x = 0} ≃ {x // L x = target} :=
    { toFun := fun x => ⟨x.val + x0, by simp [map_add, x.property, hx0]⟩
      invFun := fun x => ⟨x.val - x0, by simp [map_sub, x.property, hx0]⟩
      left_inv := fun x => Subtype.ext (add_sub_cancel_right x.val x0)
      right_inv := fun x => Subtype.ext (sub_add_cancel x.val x0) }
  rw [UniformChallenges.probability_card, Fintype.card_congr e.symm]
  change (Fintype.card L.ker : ℝ≥0∞) / Fintype.card M = _
  have hc := L.ker.card_eq_card_quotient_mul_card
  rw [Nat.card_congr (L.quotKerEquivOfSurjective hsurj).toEquiv] at hc
  simp only [Nat.card_eq_fintype_card] at hc
  have hce : (Fintype.card M : ℝ≥0∞) =
      (Fintype.card L.ker : ℝ≥0∞) * (Fintype.card V : ℝ≥0∞) := by exact_mod_cast hc
  have hk0 : (Fintype.card L.ker : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hkt : (Fintype.card L.ker : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [hce, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hk0) (Or.inl hkt), ← mul_assoc,
    ENNReal.mul_inv_cancel hk0 hkt, one_mul]

section Field

variable {F : Type*} [Field F]

/-- M ↦ M·v as a linear map in M. -/
def mulVecMap (v : Fin payload → F) : Matrix (Fin s) (Fin payload) F →ₗ[F] (Fin s → F) where
  toFun M := M.mulVec v
  map_add' M N := Matrix.add_mulVec M N v
  map_smul' c M := by
    funext a
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem mulVecMap_surjective (v : Fin payload → F) (hv : v ≠ 0) : Function.Surjective (mulVecMap (s := s) v) := by
  obtain ⟨b, hb⟩ : ∃ b, v b ≠ 0 := by
    by_contra h
    exact hv (funext fun b => not_not.mp (not_exists.mp h b))
  intro target
  refine ⟨fun a b' => if b' = b then target a / v b else 0, ?_⟩
  funext a
  simp [mulVecMap, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_eq', div_mul_cancel₀ _ hb]

variable [Fintype F]

theorem kernel_probability_bottom (d : Fin (s + payload) → F) (hbottom : bottom d ≠ 0) :
    kernelProbability d = (Fintype.card F : ℝ≥0∞)⁻¹ ^ s := by
  have hev : (fun M : Matrix (Fin s) (Fin payload) F => ∀ a, masked M d a = 0) =
      fun M => mulVecMap (bottom d) M = -top d := by
    funext M
    have hmul : ∀ a, mulVecMap (bottom d) M a = ∑ b, M a b * bottom d b := by
      intro a
      rfl
    apply propext
    constructor
    · intro h
      funext a
      rw [hmul, Pi.neg_apply]
      have := h a
      rw [masked_split] at this
      linear_combination this
    · intro h a
      have := congrFun h a
      rw [hmul, Pi.neg_apply] at this
      rw [masked_split]
      linear_combination this
  rw [kernelProbability, hev, linear_map_fiber_probability _ (mulVecMap_surjective _ hbottom)]
  simp [Fintype.card_fin, ENNReal.inv_pow]

theorem kernel_probability_top (d : Fin (s + payload) → F) (hbottom : bottom d = 0) (htop : top d ≠ 0) :
    kernelProbability d = 0 := by
  apply probability_of_empty
  intro M h
  apply htop
  funext a
  have := h a
  rw [masked_split, hbottom] at this
  simpa using this

/-- A fixed nonzero vector lies in the kernel of [I | M] with probability at
most |F|^(-s) over a uniform mask. -/
theorem kernel_probability_le (d : Fin (s + payload) → F) (hd : d ≠ 0) :
    kernelProbability d ≤ (Fintype.card F : ℝ≥0∞)⁻¹ ^ s := by
  by_cases hbottom : bottom d = 0
  · have htop : top d ≠ 0 := fun h => hd (vector_ext h hbottom)
    rw [kernel_probability_top d hbottom htop]
    exact zero_le _
  · exact le_of_eq (kernel_probability_bottom d hbottom)

/-- Two distinct fixed vectors have equal masked images with probability at
most |F|^(-s). This is the uniform-mask step for two executions' slopes. -/
theorem equal_mask_probability_le (x y : Fin (s + payload) → F) (hne : x ≠ y) :
    equalMaskProbability x y ≤ (Fintype.card F : ℝ≥0∞)⁻¹ ^ s := by
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  refine le_trans ?_ (kernel_probability_le (x - y) hd)
  apply probability_mono
  intro M h a
  rw [masked_sub, h a, sub_self]

end Field

/-- Instantiation for the binary masks of the source: s = lambda + B. -/
theorem binary_equal_mask_probability_le {lambda B payload : Nat}
    (x y : Fin ((lambda + B) + payload) → ZMod 2) (hne : x ≠ y) :
    equalMaskProbability x y ≤ (2 : ℝ≥0∞)⁻¹ ^ (lambda + B) := by
  have h := equal_mask_probability_le x y hne
  simpa [ZMod.card] using h

/-- The masked slope of `BLCSeedLines` is this mask applied to the slope vector. -/
theorem maskedSlope_eq {lambda tau kappa s wit rnd : Nat}
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Spec.DomainSeparation.Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Spec.DomainSeparation.Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (e : Fin tau) (a : Fin s) :
    Spec.BLCSeedLines.maskedSlope p salt full randomCount enough aux M e a =
      masked M (Spec.BLCSeedFold.slope p salt full randomCount enough aux e) a := rfl

end SDitH.Proofs.ConsistencyMatrix
