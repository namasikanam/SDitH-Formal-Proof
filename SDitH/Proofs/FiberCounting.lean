import SDitH.Proofs.ChargeExpect
import SDitH.Proofs.PosteriorPrune

/-! Fiber counting under a measure-preserving bijection. For a distribution
invariant under a bijection that fixes a weight and carries one label value
to another, the weighted mass of the two label values coincide; summing
over a set of label values bounds the weighted mass of one value by the
total weight over the set's size. This is the counting behind the hidden
path's independence from the pruned view: the exchange fixes the view's
law and moves the node's value. -/

namespace SDitH.Proofs.FiberCounting

open Spec.RandomOracleTrap (indicator)
open ChargeExpect
open scoped Classical ENNReal

noncomputable section

variable {α γ : Type*}

/-- Under a distribution invariant under a bijection fixing the weight and
carrying one label value to another, the weighted masses of the two values
coincide. -/
theorem mean_label_eq (p : PMF α) (e : α ≃ α) (hp : p.map e = p) (φ : α → ℝ≥0∞) (hφ : ∀ a, φ (e a) = φ a)
    (ℓ : α → γ) (v v' : γ) (hℓ : ∀ a, ℓ a = v ↔ ℓ (e a) = v') :
    mean p (fun a => φ a * indicator (decide (ℓ a = v))) = mean p (fun a => φ a * indicator (decide (ℓ a = v'))) := by
  conv_rhs => rw [← hp, mean_map]
  refine congrArg _ (funext fun a => ?_)
  rw [hφ]
  congr 2
  exact decide_eq_decide.mpr (hℓ a)

/-- The same with the bijection an involution that exchanges the two label
values and fixes the weight on the first value's fiber only. -/
theorem mean_label_eq_of_involutive (p : PMF α) (e : α → α) (he : Function.Involutive e) (hp : p.map e = p)
    (φ : α → ℝ≥0∞) (ℓ : α → γ) (v v' : γ) (hφ : ∀ a, ℓ a = v → φ (e a) = φ a)
    (hℓ : ∀ a, ℓ a = v → ℓ (e a) = v') (hℓ' : ∀ a, ℓ a = v' → ℓ (e a) = v) :
    mean p (fun a => φ a * indicator (decide (ℓ a = v'))) = mean p (fun a => φ a * indicator (decide (ℓ a = v))) := by
  conv_lhs => rw [← hp, mean_map]
  refine congrArg _ (funext fun a => ?_)
  by_cases hv : ℓ a = v
  · rw [hφ a hv, hv, hℓ a hv]
    simp
  · have hne : ℓ (e a) ≠ v' := fun h => hv (by simpa [he a] using hℓ' (e a) h)
    simp [hv, hne, RandomOracleTrap.indicator_false]

/-- The indicators of a label's values over a finite set sum to at most one. -/
theorem sum_indicator_le_one (ℓ : α → γ) (a : α) (T : Finset γ) :
    ∑ v ∈ T, indicator (decide (ℓ a = v)) ≤ 1 := by
  have h : ∀ v, indicator (decide (ℓ a = v)) = if ℓ a = v then (1 : ℝ≥0∞) else 0 := by
    intro v
    by_cases hv : ℓ a = v <;> simp [indicator, hv]
  simp only [h, Finset.sum_ite_eq]
  split <;> simp

/-- A finite sum of weighted label masses is the weighted mass of the
summed indicators. -/
theorem sum_mean_label (p : PMF α) (φ : α → ℝ≥0∞) (ℓ : α → γ) (T : Finset γ) :
    ∑ v ∈ T, mean p (fun a => φ a * indicator (decide (ℓ a = v))) =
      mean p (fun a => φ a * ∑ v ∈ T, indicator (decide (ℓ a = v))) := by
  induction T using Finset.induction_on with
  | empty => simp [mean_const]
  | insert v T hv ih =>
    rw [Finset.sum_insert hv, ih]
    simp only [Finset.sum_insert hv, mul_add]
    rw [mean_add]

/-- A finite sum of weighted label masses is at most the total weight. -/
theorem sum_label_le (p : PMF α) (φ : α → ℝ≥0∞) (ℓ : α → γ) (T : Finset γ) :
    ∑ v ∈ T, mean p (fun a => φ a * indicator (decide (ℓ a = v))) ≤ mean p φ := by
  rw [sum_mean_label]
  refine mean_le_mean _ _ _ fun a _ => ?_
  calc φ a * ∑ v ∈ T, indicator (decide (ℓ a = v)) ≤ φ a * 1 :=
        mul_le_mul' le_rfl (sum_indicator_le_one ℓ a T)
    _ = φ a := mul_one _

/-- When every label value in a set has the weighted mass of a given value,
that mass is at most the total weight over the set's size. -/
theorem label_mass_le (p : PMF α) (φ : α → ℝ≥0∞) (ℓ : α → γ) (v : γ) (T : Finset γ)
    (h : ∀ v' ∈ T, mean p (fun a => φ a * indicator (decide (ℓ a = v'))) =
      mean p (fun a => φ a * indicator (decide (ℓ a = v)))) :
    (T.card : ℝ≥0∞) * mean p (fun a => φ a * indicator (decide (ℓ a = v))) ≤ mean p φ := by
  have hsum := sum_label_le p φ ℓ T
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul] at hsum
  exact hsum

end
end SDitH.Proofs.FiberCounting
