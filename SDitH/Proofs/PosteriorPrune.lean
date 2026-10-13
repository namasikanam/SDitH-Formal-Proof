import SDitH.Proofs.HiddenEntries
import SDitH.Proofs.PosteriorFresh

/-! The posterior factorises over keys. A family matches a history key by
key, so a candidate's coordinate at a key can be replaced by any permutation
matching the entries at that key; exchanging the coordinates of a candidate
of a history and a candidate of its pruned history (at a key outside the
pruned ones) is a bijection between the fibers, hence the law of the
coordinate at such a key is the same under the posterior of the history and
of its pruned history, and so is the law of the answer to any request at
such a key. -/

namespace SDitH.Proofs.PosteriorPrune

open Spec.IdealCipher (Family Entry Matches Candidates World answer)
open HiddenEntries CipherResample
open scoped Classical ENNReal

noncomputable section

/-- The law of a uniform draw's image at a value is the fiber's size over the
type's size. -/
theorem uniform_map_apply {α β : Type*} [Fintype α] [Nonempty α] (g : α → β) (b : β) :
    ((PMF.uniformOfFintype α).map g) b = (Fintype.card {a // g a = b} : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : g a = b
  · simp [h]
  · simp [h, Ne.symm h]

variable {Key Block : Type*} [Fintype Key] [Fintype Block]

omit [Fintype Key] [Fintype Block] in
/-- Replacing a family's coordinate at a key by a permutation matching the
entries at that key keeps it matching. -/
theorem matches_update (f : Family Key Block) (history : List (Entry Key Block)) (hf : Matches f history) (κ : Key)
    (π : Equiv.Perm Block) (hπ : ∀ e ∈ history, e.key = κ → π e.input = e.output) :
    Matches (Function.update f κ π) history := by
  intro e he
  by_cases hk : e.key = κ
  · rw [hk, Function.update_self]
    exact hπ e he hk
  · rw [Function.update_of_ne hk]
    exact hf e he

omit [Fintype Key] [Fintype Block] in
/-- The entries at a key outside the pruned keys are the same in the history
and in its pruned history. -/
theorem mem_pruneAt_of_key (K : List Key) (history : List (Entry Key Block)) (κ : Key) (hκ : κ ∉ K)
    (e : Entry Key Block) (he : e.key = κ) : e ∈ pruneAt K history ↔ e ∈ history := by
  rw [mem_pruneAt, he]
  exact ⟨fun h => h.1, fun h => ⟨h, hκ⟩⟩

/-- The candidates whose coordinate at a key is a given permutation. -/
abbrev Fiber (world : World Key Block) (κ : Key) (π : Equiv.Perm Block) := {f : Candidates world // f.val κ = π}

/-- Exchanging the coordinates at a key outside the pruned keys between a
candidate of a world and a candidate of its pruned world in a fiber. -/
def exchange (K : List Key) (world : World Key Block) (κ : Key) (hκ : κ ∉ K) (π : Equiv.Perm Block) :
    Candidates world × Fiber (pruneWorld K world) κ π ≃ Candidates (pruneWorld K world) × Fiber world κ π where
  toFun p :=
    (⟨Function.update p.2.val.val κ (p.1.val κ), matches_update _ _ p.2.val.property κ _ fun e he hk => by
        subst hk
        exact p.1.property e ((mem_pruneAt_of_key K world.history _ hκ e rfl).mp he)⟩,
      ⟨⟨Function.update p.1.val κ π, matches_update _ _ p.1.property κ π fun e he hk => by
        rw [← p.2.property]
        subst hk
        exact p.2.val.property e ((mem_pruneAt_of_key K world.history _ hκ e rfl).mpr he)⟩, by simp⟩)
  invFun p :=
    (⟨Function.update p.2.val.val κ (p.1.val κ), matches_update _ _ p.2.val.property κ _ fun e he hk => by
        subst hk
        exact p.1.property e ((mem_pruneAt_of_key K world.history _ hκ e rfl).mpr he)⟩,
      ⟨⟨Function.update p.1.val κ π, matches_update _ _ p.1.property κ π fun e he hk => by
        rw [← p.2.property]
        subst hk
        exact p.2.val.property e ((mem_pruneAt_of_key K world.history _ hκ e rfl).mp he)⟩, by simp⟩)
  left_inv p := by
    rcases p with ⟨⟨f, hf⟩, ⟨⟨f', hf'⟩, hπ⟩⟩
    simp only [Function.update_self, Function.update_idem]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext (Subtype.ext ?_))
    · exact Function.update_eq_self κ f
    · simp only
      rw [← hπ]
      exact Function.update_eq_self κ f'
  right_inv p := by
    rcases p with ⟨⟨f, hf⟩, ⟨⟨f', hf'⟩, hπ⟩⟩
    simp only [Function.update_self, Function.update_idem]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext (Subtype.ext ?_))
    · exact Function.update_eq_self κ f
    · simp only
      rw [← hπ]
      exact Function.update_eq_self κ f'

/-- The fibers' sizes are proportional to the candidates' numbers. -/
theorem card_fiber_mul (K : List Key) (world : World Key Block) (κ : Key) (hκ : κ ∉ K) (π : Equiv.Perm Block)
    (i₁ : Fintype (Fiber (pruneWorld K world) κ π)) (i₂ : Fintype (Fiber world κ π)) :
    Fintype.card (Candidates world) * @Fintype.card _ i₁ =
      Fintype.card (Candidates (pruneWorld K world)) * @Fintype.card _ i₂ := by
  rw [← Fintype.card_prod, ← Fintype.card_prod]
  exact Fintype.card_congr (exchange K world κ hκ π)

/-- The coordinate at a key outside the pruned keys has the same law under the
posterior of a world and of its pruned world. -/
theorem posterior_coord_eq (K : List Key) (world : World Key Block) (κ : Key) (hκ : κ ∉ K) :
    (posterior world.history).map (fun f => f κ) = (posterior (pruneWorld K world).history).map (fun f => f κ) := by
  rw [posterior_world, posterior_world, PMF.map_comp, PMF.map_comp]
  ext π
  rw [uniform_map_apply, uniform_map_apply, ← div_eq_mul_inv, ← div_eq_mul_inv]
  rw [ENNReal.div_eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  exact congrArg _ (card_fiber_mul K world κ hκ π _ _).symm

/-- The key of a request. -/
def keyOf : Spec.IdealCipher.Query Key Block → Key
  | .encrypt key _ => key
  | .decrypt key _ => key

/-- The answer to a request at a key outside the pruned keys has the same law
under the posterior of a world and of its pruned world. -/
theorem posterior_answer_eq_prune (K : List Key) (world : World Key Block) (request : Spec.IdealCipher.Query Key Block)
    (hκ : keyOf request ∉ K) :
    (posterior world.history).map (fun f => answer f request) =
      (posterior (pruneWorld K world).history).map (fun f => answer f request) := by
  cases request with
  | encrypt key input =>
    have h := congrArg (PMF.map fun π : Equiv.Perm Block => π input) (posterior_coord_eq K world key hκ)
    rw [PMF.map_comp, PMF.map_comp] at h
    exact h
  | decrypt key output =>
    have h := congrArg (PMF.map fun π : Equiv.Perm Block => π.symm output) (posterior_coord_eq K world key hκ)
    rw [PMF.map_comp, PMF.map_comp] at h
    exact h

end
end SDitH.Proofs.PosteriorPrune
