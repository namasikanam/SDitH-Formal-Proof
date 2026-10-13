import SDitH.Proofs.PosteriorPrune

/-! The exchange of a node's value. Given a parent key, two block values and
two keys (meant as the keys of the two values), the exchange post-composes
the permutation at the parent key with the transposition of the two values
and swaps the permutations at the two keys. It is an involution, it fixes
every key other than the three, so it preserves matching of a history in
which the three keys are fresh, and hence it preserves the posterior family
of such a history. This is the measure-preserving map behind the hidden
path's independence from the pruned data. -/

namespace SDitH.Proofs.NodeExchange

open Spec.IdealCipher (Family Entry Matches Candidates World)
open CipherResample
open scoped Classical

noncomputable section

variable {Key Block : Type*}

/-- The exchange of a node's value. -/
def swapNode (p : Key) (v v' : Block) (κ κ' : Key) (f : Family Key Block) : Family Key Block :=
  Function.update (f ∘ Equiv.swap κ κ') p ((f p).trans (Equiv.swap v v'))

variable (p : Key) (v v' : Block) (κ κ' : Key) (f : Family Key Block)

theorem swapNode_apply_parent : swapNode p v v' κ κ' f p = (f p).trans (Equiv.swap v v') := by
  simp [swapNode]

theorem swapNode_apply_of_ne (k : Key) (hk : k ≠ p) (hκ : k ≠ κ) (hκ' : k ≠ κ') :
    swapNode p v v' κ κ' f k = f k := by
  simp [swapNode, Function.update_of_ne hk, Equiv.swap_apply_of_ne_of_ne hκ hκ']

theorem swapNode_apply_left (hκp : κ ≠ p) : swapNode p v v' κ κ' f κ = f κ' := by
  simp [swapNode, Function.update_of_ne hκp]

theorem swapNode_apply_right (hκ'p : κ' ≠ p) : swapNode p v v' κ κ' f κ' = f κ := by
  simp [swapNode, Function.update_of_ne hκ'p]

/-- The exchange is an involution when the parent key differs from the two keys. -/
theorem swapNode_involutive (hp : p ≠ κ) (hp' : p ≠ κ') : Function.Involutive (swapNode p v v' κ κ') := by
  intro f
  funext k
  by_cases hk : k = p
  · subst hk
    simp only [swapNode, Function.update_self, Equiv.trans_assoc, Equiv.swap_swap, Equiv.trans_refl]
  · have hswap : Equiv.swap κ κ' k ≠ p := fun h => hk (by
      rw [← Equiv.swap_apply_self κ κ' k, h, Equiv.swap_apply_of_ne_of_ne hp hp'])
    simp only [swapNode, Function.update_of_ne hk, Function.comp_apply, Function.update_of_ne hswap,
      Equiv.swap_apply_self]

/-- The exchange as a permutation of families. -/
def swapNodeEquiv (hp : p ≠ κ) (hp' : p ≠ κ') : Family Key Block ≃ Family Key Block :=
  (swapNode_involutive p v v' κ κ' hp hp').toPerm

theorem swapNodeEquiv_apply (hp : p ≠ κ) (hp' : p ≠ κ') : swapNodeEquiv p v v' κ κ' hp hp' f = swapNode p v v' κ κ' f :=
  rfl

/-- The exchange preserves matching of a history in which the three keys are
fresh. -/
theorem matches_swapNode (history : List (Entry Key Block)) (hfp : ∀ e ∈ history, e.key ≠ p)
    (hfκ : ∀ e ∈ history, e.key ≠ κ) (hfκ' : ∀ e ∈ history, e.key ≠ κ') :
    Matches (swapNode p v v' κ κ' f) history ↔ Matches f history := by
  constructor
  · intro h e he
    have := h e he
    rwa [swapNode_apply_of_ne p v v' κ κ' f e.key (hfp e he) (hfκ e he) (hfκ' e he)] at this
  · intro h e he
    rw [swapNode_apply_of_ne p v v' κ κ' f e.key (hfp e he) (hfκ e he) (hfκ' e he)]
    exact h e he

variable [Fintype Key] [Fintype Block]

/-- The exchange on the candidates of a world in which the three keys are
fresh. -/
def swapCandidates (world : World Key Block) (hp : p ≠ κ) (hp' : p ≠ κ') (hfp : ∀ e ∈ world.history, e.key ≠ p)
    (hfκ : ∀ e ∈ world.history, e.key ≠ κ) (hfκ' : ∀ e ∈ world.history, e.key ≠ κ') :
    Candidates world ≃ Candidates world where
  toFun c := ⟨swapNode p v v' κ κ' c.val, (matches_swapNode p v v' κ κ' c.val world.history hfp hfκ hfκ').mpr c.property⟩
  invFun c := ⟨swapNode p v v' κ κ' c.val, (matches_swapNode p v v' κ κ' c.val world.history hfp hfκ hfκ').mpr c.property⟩
  left_inv c := Subtype.ext (swapNode_involutive p v v' κ κ' hp hp' c.val)
  right_inv c := Subtype.ext (swapNode_involutive p v v' κ κ' hp hp' c.val)

/-- The posterior of a history in which the three keys are fresh is
invariant under the exchange. -/
theorem posterior_swapNode (history : List (Entry Key Block)) (hpos : ∃ g : Family Key Block, Matches g history)
    (hp : p ≠ κ) (hp' : p ≠ κ') (hfp : ∀ e ∈ history, e.key ≠ p) (hfκ : ∀ e ∈ history, e.key ≠ κ)
    (hfκ' : ∀ e ∈ history, e.key ≠ κ') :
    (posterior history).map (swapNode p v v' κ κ') = posterior history := by
  rw [posterior_world ⟨history, hpos⟩, PMF.map_comp]
  have h : swapNode p v v' κ κ' ∘ (Subtype.val : Candidates (⟨history, hpos⟩ : World Key Block) → Family Key Block) =
      Subtype.val ∘ swapCandidates p v v' κ κ' ⟨history, hpos⟩ hp hp' hfp hfκ hfκ' := rfl
  rw [h, ← PMF.map_comp, IntegerSamplingProbability.map_uniform_equiv]

end
end SDitH.Proofs.NodeExchange
