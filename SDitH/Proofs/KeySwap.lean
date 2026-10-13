import SDitH.Proofs.PosteriorPrune

/-! The swap of two keys. Precomposing a family with the transposition of
two keys swaps the permutations at them; it is an involution fixing every
other key, so it preserves matching of a history in which the two keys are
fresh, and leaves the posterior of such a history invariant. -/

namespace SDitH.Proofs.KeySwap

open Spec.IdealCipher (Family Entry Matches Candidates World)
open CipherResample
open scoped Classical

noncomputable section

variable {Key Block : Type*} (κ κ' : Key) (f : Family Key Block)

/-- The family with the permutations at two keys swapped. -/
def swapKeys : Family Key Block := f ∘ Equiv.swap κ κ'

theorem swapKeys_apply_left : swapKeys κ κ' f κ = f κ' := by simp [swapKeys]

theorem swapKeys_apply_right : swapKeys κ κ' f κ' = f κ := by simp [swapKeys]

theorem swapKeys_apply_of_ne (k : Key) (hk : k ≠ κ) (hk' : k ≠ κ') : swapKeys κ κ' f k = f k := by
  simp [swapKeys, Equiv.swap_apply_of_ne_of_ne hk hk']

theorem swapKeys_involutive : Function.Involutive (swapKeys κ κ' (Block := Block)) := fun g => by
  funext k
  simp [swapKeys, Equiv.swap_apply_self]

/-- The swap preserves matching of a history in which both keys are fresh. -/
theorem matches_swapKeys (history : List (Entry Key Block)) (hfκ : ∀ e ∈ history, e.key ≠ κ)
    (hfκ' : ∀ e ∈ history, e.key ≠ κ') : Matches (swapKeys κ κ' f) history ↔ Matches f history := by
  constructor
  · intro h e he
    have := h e he
    rwa [swapKeys_apply_of_ne κ κ' f e.key (hfκ e he) (hfκ' e he)] at this
  · intro h e he
    rw [swapKeys_apply_of_ne κ κ' f e.key (hfκ e he) (hfκ' e he)]
    exact h e he

variable [Fintype Key] [Fintype Block]

/-- The swap on the candidates of a world in which both keys are fresh. -/
def swapCandidates (world : World Key Block) (hfκ : ∀ e ∈ world.history, e.key ≠ κ)
    (hfκ' : ∀ e ∈ world.history, e.key ≠ κ') : Candidates world ≃ Candidates world where
  toFun c := ⟨swapKeys κ κ' c.val, (matches_swapKeys κ κ' c.val world.history hfκ hfκ').mpr c.property⟩
  invFun c := ⟨swapKeys κ κ' c.val, (matches_swapKeys κ κ' c.val world.history hfκ hfκ').mpr c.property⟩
  left_inv c := Subtype.ext (swapKeys_involutive κ κ' c.val)
  right_inv c := Subtype.ext (swapKeys_involutive κ κ' c.val)

/-- The posterior of a history in which both keys are fresh is invariant
under the swap. -/
theorem posterior_swapKeys (history : List (Entry Key Block)) (hpos : ∃ g : Family Key Block, Matches g history)
    (hfκ : ∀ e ∈ history, e.key ≠ κ) (hfκ' : ∀ e ∈ history, e.key ≠ κ') :
    (posterior history).map (swapKeys κ κ') = posterior history := by
  rw [posterior_world ⟨history, hpos⟩, PMF.map_comp]
  have h : swapKeys κ κ' ∘ (Subtype.val : Candidates (⟨history, hpos⟩ : World Key Block) → Family Key Block) =
      Subtype.val ∘ swapCandidates κ κ' ⟨history, hpos⟩ hfκ hfκ' := rfl
  rw [h, ← PMF.map_comp, IntegerSamplingProbability.map_uniform_equiv]

end
end SDitH.Proofs.KeySwap
