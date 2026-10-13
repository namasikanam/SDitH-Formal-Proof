import SDitH.Proofs.PathUnion

/-! The hidden keys of all executions. A signature hides one leaf per
execution; its hidden keys are the union over the executions of the hidden
keys of the execution's leaf, and touching them is at most the sum over
the executions of touching the execution's hidden keys. -/

namespace SDitH.Proofs.HiddenTuple

open Spec.SeedTree Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa : Nat} (layout : Layout lambda (Bits lambda) (Bits lambda)) (g : Family (Bits lambda) (Bits lambda))
  (variant : Grinding) (salt root : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa))

/-- The hidden keys of all executions. -/
def hiddenKeysAll : List (Bits lambda) :=
  (List.finRange tau).flatMap fun e => hiddenKeys layout g variant salt root (leafAddress e (hidden e))

theorem mem_hiddenKeysAll (κ : Bits lambda) :
    κ ∈ hiddenKeysAll layout g variant salt root hidden ↔
      ∃ e : Fin tau, κ ∈ hiddenKeys layout g variant salt root (leafAddress e (hidden e)) := by
  unfold hiddenKeysAll
  simp [List.mem_flatMap, List.mem_finRange]

/-- Touching the hidden keys of all executions is at most the sum over the
executions of touching the execution's hidden keys. -/
theorem touchAll_le_sum (new : List (Entry (Bits lambda) (Bits lambda))) :
    indicator (decide (∃ e ∈ new, e.key ∈ hiddenKeysAll layout g variant salt root hidden)) ≤
      ∑ ex : Fin tau, indicator (decide (∃ e ∈ new, e.key ∈ hiddenKeys layout g variant salt root (leafAddress ex (hidden ex)))) := by
  by_cases h : ∃ e ∈ new, e.key ∈ hiddenKeysAll layout g variant salt root hidden
  · obtain ⟨e, he, hκ⟩ := h
    obtain ⟨ex, hex⟩ := (mem_hiddenKeysAll layout g variant salt root hidden e.key).mp hκ
    have hterm : indicator (decide (∃ e ∈ new, e.key ∈ hiddenKeys layout g variant salt root (leafAddress ex (hidden ex)))) = 1 := by
      have : ∃ e ∈ new, e.key ∈ hiddenKeys layout g variant salt root (leafAddress ex (hidden ex)) := ⟨e, he, hex⟩
      simp [this, indicator]
    have hex' : ∃ e ∈ new, e.key ∈ hiddenKeysAll layout g variant salt root hidden := ⟨e, he, hκ⟩
    calc indicator (decide (∃ e ∈ new, e.key ∈ hiddenKeysAll layout g variant salt root hidden)) = 1 := by
          simp [indicator, hex']
      _ = indicator (decide (∃ e ∈ new, e.key ∈ hiddenKeys layout g variant salt root (leafAddress ex (hidden ex)))) :=
          hterm.symm
      _ ≤ _ := Finset.single_le_sum
          (f := fun ex => indicator (decide (∃ e ∈ new, e.key ∈ hiddenKeys layout g variant salt root (leafAddress ex (hidden ex)))))
          (fun _ _ => zero_le _) (Finset.mem_univ ex)
  · simp [h, indicator]

end
end SDitH.Proofs.HiddenTuple
