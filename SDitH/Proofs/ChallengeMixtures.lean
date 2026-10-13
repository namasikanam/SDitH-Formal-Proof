import SDitH.Spec.UniformChallenges
import Mathlib.Tactic

namespace SDitH.Proofs.ChallengeMixtures

open Spec.UniformChallenges
open scoped BigOperators ENNReal Classical

theorem eventOutcome_true {A : Type*} (p : PMF A) (event : A → Prop) :
    eventOutcome p event true = p.toOuterMeasure {a | event a} := by
  unfold eventOutcome
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  congr 1
  ext a
  simp

theorem bind_true_le {A : Type*} (p : PMF A) (next : A → PMF Bool) (epsilon : ℝ≥0∞)
    (h : ∀ a ∈ p.support, next a true ≤ epsilon) : (p.bind next) true ≤ epsilon := by
  rw [PMF.bind_apply]
  calc
    (∑' a, p a * next a true) ≤ ∑' a, p a * epsilon := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : a ∈ p.support
      · exact mul_le_mul_right (h a ha) _
      · simp only [PMF.mem_support_iff, not_not] at ha
        simp [ha]
    _ = epsilon := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem bind_true_eq {A : Type*} (p : PMF A) (next : A → PMF Bool) (epsilon : ℝ≥0∞)
    (h : ∀ a ∈ p.support, next a true = epsilon) : (p.bind next) true = epsilon := by
  rw [PMF.bind_apply]
  calc
    (∑' a, p a * next a true) = ∑' a, p a * epsilon := by
      apply tsum_congr
      intro a
      by_cases ha : a ∈ p.support
      · rw [h a ha]
      · simp only [PMF.mem_support_iff, not_not] at ha
        simp [ha]
    _ = epsilon := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem complement_mass {A : Type*} [Fintype A] (p : PMF A) (event : A → Prop) :
    p.toOuterMeasure {a | ¬ event a} = 1 - p.toOuterMeasure {a | event a} := by
  apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
  simp only [PMF.toOuterMeasure_apply_fintype, Set.indicator_apply, Set.mem_setOf_eq]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ a, ((if ¬ event a then p a else 0) + (if event a then p a else 0))) = ∑ a, p a := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : event a <;> simp [ha]
    _ = 1 := by simpa only [tsum_fintype] using p.tsum_coe

/-- Average a conditional bound over an arbitrary finite first-stage law.
The second-stage experiment may depend on the first sampled value. -/
theorem bind_true_bound {A : Type*} [Fintype A] (p : PMF A) (next : A → PMF Bool)
    (bad : A → Prop) (epsilon : ℝ≥0∞)
    (hgood : ∀ a, ¬ bad a → next a true ≤ epsilon) :
    (p.bind next) true ≤ p.toOuterMeasure {a | bad a} +
      (1 - p.toOuterMeasure {a | bad a}) * epsilon := by
  rw [PMF.bind_apply, tsum_fintype]
  calc
    (∑ a, p a * next a true) ≤ ∑ a, p a * (if bad a then 1 else epsilon) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_right
      by_cases ha : bad a
      · simpa only [if_pos ha] using (next a).coe_le_one true
      · simpa only [if_neg ha] using hgood a ha
    _ = p.toOuterMeasure {a | bad a} + p.toOuterMeasure {a | ¬ bad a} * epsilon := by
      simp only [PMF.toOuterMeasure_apply_fintype, Set.indicator_apply, Set.mem_setOf_eq]
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : bad a <;> simp [ha]
    _ = _ := by rw [complement_mass]

theorem boolean_union_bound {A I : Type*} [Fintype I]
    (p : PMF A) (win : A → Bool) (events : I → A → Bool)
    (hcover : ∀ a ∈ p.support, win a = true → ∃ i, events i a = true) :
    (p.map win) true ≤ ∑ i, (p.map (events i)) true := by
  simp only [PMF.map_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ p.support
  · by_cases hw : true = win a
    · obtain ⟨i, hi⟩ := hcover a ha hw.symm
      simp only [if_pos hw]
      calc
        p a = (if true = events i a then p a else 0) := by simp [hi]
        _ ≤ ∑ j, if true = events j a then p a else 0 :=
          Finset.single_le_sum (f := fun j : I => if true = events j a then p a else 0)
            (fun _ _ => bot_le) (Finset.mem_univ i)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : true = events j a <;> simp [h]
    · simp [hw]
  · have hp : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hp]

end SDitH.Proofs.ChallengeMixtures
