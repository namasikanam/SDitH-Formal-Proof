import SDitH.Proofs.FiberCountingBad
import SDitH.Proofs.HiddenEntries

/-! One-sided fiber exchange, and pruning at an unused key. The one-sided
form of the fiber exchange needs no inverse: under an invariant
distribution, the mass of a label value restricted to the good points is at
most the mass of a target value whenever the map carries good points of the
value to the target without lowering the weight. Pruning a history at a
key none of its entries uses prunes it at the remaining keys. -/

namespace SDitH.Proofs.FiberCountingSided

open Spec.RandomOracleTrap (indicator)
open ChargeExpect FiberCounting HiddenEntries
open scoped Classical ENNReal

noncomputable section

variable {α γ : Type*}

/-- The one-sided fiber exchange. -/
theorem mean_label_le_of_map (p : PMF α) (e : α → α) (hp : p.map e = p) (φ : α → ℝ≥0∞) (ℓ : α → γ) (v v' : γ)
    (Bad : α → Prop) (hφ : ∀ a, ℓ a = v → ¬ Bad a → φ a ≤ φ (e a)) (hℓ : ∀ a, ℓ a = v → ¬ Bad a → ℓ (e a) = v') :
    mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (¬ Bad a))) ≤
      mean p (fun a => φ a * indicator (decide (ℓ a = v'))) := by
  conv_rhs => rw [← hp, mean_map]
  refine mean_le_mean _ _ _ fun a _ => ?_
  by_cases hv : ℓ a = v
  · by_cases hb : Bad a
    · simp [hb, indicator]
    · rw [hℓ a hv hb]
      simp only [hv, hb, decide_true, not_false_eq_true, RandomOracleTrap.indicator_true, mul_one]
      exact hφ a hv hb
  · simp [hv, indicator]

variable {Key Block : Type*}

/-- Pruning at a key none of the history's entries uses is pruning at the
remaining keys. -/
theorem pruneAt_cons_of_no_entry (K : List Key) (κ : Key) (history : List (Spec.IdealCipher.Entry Key Block))
    (h : ∀ e ∈ history, e.key ≠ κ) : pruneAt (κ :: K) history = pruneAt K history := by
  unfold pruneAt
  refine List.filter_congr fun e he => ?_
  have := h e he
  simp [this]

end
end SDitH.Proofs.FiberCountingSided
