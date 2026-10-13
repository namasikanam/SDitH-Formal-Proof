import SDitH.Proofs.IntegerSamplingProbability

/-! Exact finite conditioning identities used to compare once-sampled ideal
cipher families with posterior sampling. These are counting proofs, not
conditional-independence assumptions about an adaptive adversary. -/

namespace SDitH.Proofs.FinitePosterior

open scoped Classical ENNReal
noncomputable section

variable {A B R : Type*} [Fintype A]

abbrev Fiber (f : A → B) (a : A) := {x : A // f x = f a}

instance fiber_nonempty (f : A → B) (a : A) : Nonempty (Fiber f a) := ⟨⟨a, rfl⟩⟩

def resample (f : A → B) (a : A) : PMF A :=
  (PMF.uniformOfFintype (Fiber f a)).map Subtype.val

theorem resample_apply (f : A → B) (a b : A) :
    resample f a b = if f b = f a then (Fintype.card (Fiber f a) : ℝ≥0∞)⁻¹ else 0 := by
  simp only [resample, PMF.map_apply, PMF.uniformOfFintype_apply]
  by_cases h : f b = f a
  · rw [if_pos h, tsum_eq_single (⟨b, h⟩ : Fiber f a)]
    · simp
    · intro x hx
      have hne : b ≠ x.val := by
        intro he
        exact hx (Subtype.ext he.symm)
      simp [hne]
  · rw [if_neg h]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    have hne : b ≠ x.val := by
      intro he
      exact h (he ▸ x.property)
    simp [hne]

theorem resample_zero (f : A → B) (a b : A) (h : f b ≠ f a) : resample f a b = 0 := by
  simp [resample_apply, h]

/-- Averaging the conditional uniform laws restores the initial uniform law. -/
theorem resample_average (f : A → B) (b : A) :
    ∑ a : A, (Fintype.card A : ℝ≥0∞)⁻¹ * resample f a b = (Fintype.card A : ℝ≥0∞)⁻¹ := by
  have hpoint (a : A) : resample f a b =
      if f a = f b then (Fintype.card (Fiber f b) : ℝ≥0∞)⁻¹ else 0 := by
    rw [resample_apply]
    by_cases he : f a = f b
    · have hf : Fiber f a = Fiber f b := by simp only [Fiber, he]
      simp [he, hf]
    · simp [he, Ne.symm he]
  simp only [hpoint, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun a => f a = f b)).card = Fintype.card (Fiber f b) :=
    (Fintype.card_subtype _).symm
  rw [hcard]
  have hn : (Fintype.card (Fiber f b) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (Fintype.card A : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Fiber f b) : ℝ≥0∞) * (Fintype.card (Fiber f b) : ℝ≥0∞)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hn (ENNReal.natCast_ne_top _), mul_one]

variable [Nonempty A]

/-- Retain the observed answer while resampling its compatible hidden value.
The next computation may depend on both that answer and the sampled value. -/
theorem resample_bind (f : A → B) (next : B → A → PMF R) :
    (PMF.uniformOfFintype A).bind (fun a => (resample f a).bind (next (f a))) =
      (PMF.uniformOfFintype A).bind (fun a => next (f a) a) := by
  ext r
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ∑ a : A, ((Fintype.card A : ℝ≥0∞)⁻¹ * resample f a b) * next (f b) b r := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases he : f b = f a
      · rw [← he]
        exact (mul_assoc _ _ _).symm
      · simp [resample_zero f a b he]
    _ = _ := by rw [← Finset.sum_mul, resample_average]

theorem fiber_bind (f : A → B) (next : B → A → PMF R) :
    (PMF.uniformOfFintype A).bind (fun a =>
      (PMF.uniformOfFintype (Fiber f a)).bind (fun b => next (f a) b.val)) =
      (PMF.uniformOfFintype A).bind (fun a => next (f a) a) := by
  simpa only [resample, PMF.bind_map, Function.comp_def] using resample_bind f next

end
end SDitH.Proofs.FinitePosterior
