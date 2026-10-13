import SDitH.Proofs.FiberCounting
import SDitH.Proofs.ChargeCutExpect

/-! Fiber counting with bad exchange targets. When a label value's weighted
mass is exchanged with every other value except a bounded number of bad
targets per point, the value's mass is at most the total weight over the
number of values less the bound. -/

namespace SDitH.Proofs.FiberCountingBad

open Spec.RandomOracleTrap (indicator)
open ChargeExpect ChargeCutExpect FiberCounting
open scoped Classical ENNReal

noncomputable section

variable {α γ : Type*} [Fintype γ]

omit [Fintype γ] in
theorem indicator_not_add (b : Bool) : indicator (!b) + indicator b = 1 := by
  cases b <;> simp [indicator]

omit [Fintype γ] in
/-- A weighted mass splits along a predicate. -/
theorem mean_split (p : PMF α) (ψ : α → ℝ≥0∞) (Bad : α → Prop) :
    mean p ψ = mean p (fun a => ψ a * indicator (decide (¬ Bad a))) + mean p (fun a => ψ a * indicator (decide (Bad a))) := by
  rw [← mean_add]
  refine congrArg _ (funext fun a => ?_)
  rw [← mul_add]
  by_cases h : Bad a <;> simp [h, indicator]

/-- The sum over the targets of the bad-target masses is the mass weighted
by the number of bad targets. -/
theorem sum_bad_mass (p : PMF α) (ψ : α → ℝ≥0∞) (Bad : γ → α → Prop) :
    ∑ v' : γ, mean p (fun a => ψ a * indicator (decide (Bad v' a))) =
      mean p (fun a => ψ a * ((Finset.univ.filter fun v' => Bad v' a).card : ℝ≥0∞)) := by
  have hcount : ∀ a, ((Finset.univ.filter fun v' => Bad v' a).card : ℝ≥0∞) =
      ∑ v' : γ, indicator (decide (Bad v' a)) := by
    intro a
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun v' _ => ?_
    by_cases h : Bad v' a <;> simp [h, indicator]
  simp only [hcount]
  induction (Finset.univ : Finset γ) using Finset.induction_on with
  | empty => simp [mean_const]
  | insert v T hv ih =>
    rw [Finset.sum_insert hv, ih]
    simp only [Finset.sum_insert hv, mul_add]
    rw [mean_add]

/-- A label value's mass when exchanged with all but a bounded number of
bad targets. -/
theorem label_mass_le_of_bad [Nonempty γ] (p : PMF α) (φ : α → ℝ≥0∞) (hφ : ∀ a, φ a ≤ 1) (ℓ : α → γ) (v : γ)
    (Bad : γ → α → Prop) (M : ℕ) (hM : ∀ a, (Finset.univ.filter fun v' => Bad v' a).card ≤ M)
    (h : ∀ v', mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (¬ Bad v' a))) ≤
      mean p (fun a => φ a * indicator (decide (ℓ a = v')))) :
    ((Fintype.card γ - M : ℕ) : ℝ≥0∞) * mean p (fun a => φ a * indicator (decide (ℓ a = v))) ≤ mean p φ := by
  set m := mean p (fun a => φ a * indicator (decide (ℓ a = v))) with hm
  have hmle : m ≤ 1 := mean_le_const _ _ 1 fun a _ => by
    calc φ a * indicator (decide (ℓ a = v)) ≤ 1 * 1 :=
          mul_le_mul' (hφ a) (by by_cases h : ℓ a = v <;> simp [h, indicator])
      _ = 1 := mul_one _
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hmle
  -- the total: card γ · m = Σ_{v'} m ≤ Σ_{v'} (good part + bad part)
  have hsplit : (Fintype.card γ : ℝ≥0∞) * m ≤ mean p φ + (M : ℝ≥0∞) * m := by
    have hsum : (Fintype.card γ : ℝ≥0∞) * m = ∑ v' : γ, m := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hsum]
    calc ∑ v' : γ, m
        = ∑ v' : γ, (mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (¬ Bad v' a))) +
            mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (Bad v' a)))) :=
          Finset.sum_congr rfl fun v' _ => mean_split p _ (Bad v')
      _ = ∑ v' : γ, mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (¬ Bad v' a))) +
            ∑ v' : γ, mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (Bad v' a))) :=
          Finset.sum_add_distrib
      _ ≤ ∑ v' : γ, mean p (fun a => φ a * indicator (decide (ℓ a = v'))) +
            mean p (fun a => φ a * indicator (decide (ℓ a = v)) * ((Finset.univ.filter fun v' => Bad v' a).card : ℝ≥0∞)) :=
          add_le_add (Finset.sum_le_sum fun v' _ => h v') (le_of_eq (sum_bad_mass p _ Bad))
      _ ≤ mean p φ + mean p (fun a => φ a * indicator (decide (ℓ a = v)) * (M : ℝ≥0∞)) :=
          add_le_add (sum_label_le p φ ℓ Finset.univ) (mean_le_mean _ _ _ fun a _ =>
            mul_le_mul' le_rfl (Nat.cast_le.mpr (hM a)))
      _ = mean p φ + (M : ℝ≥0∞) * m := by
          rw [show (fun a => φ a * indicator (decide (ℓ a = v)) * (M : ℝ≥0∞)) =
            fun a => (M : ℝ≥0∞) * (φ a * indicator (decide (ℓ a = v))) from funext fun a => mul_comm _ _, mean_mul_left]
  calc ((Fintype.card γ - M : ℕ) : ℝ≥0∞) * m ≤ (Fintype.card γ : ℝ≥0∞) * m - (M : ℝ≥0∞) * m := by
        rw [ENNReal.natCast_sub, ENNReal.sub_mul fun _ _ => hmtop]
    _ ≤ mean p φ := tsub_le_iff_right.mpr hsplit

end
end SDitH.Proofs.FiberCountingBad
