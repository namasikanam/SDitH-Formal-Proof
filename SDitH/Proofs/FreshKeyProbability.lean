import SDitH.Proofs.FreshKeyUniform
import SDitH.Proofs.IntegerSamplingProbability
import SDitH.Spec.BAVCCipherProgram

/-! The fresh-parent-key event's probability. For a uniform parent seed and
an injective key layout, the parent's key is used in a history only when
the parent is one of at most as many seeds as the history has entries, so
the probability that the key is not fresh is at most the history's length
over the number of seeds. -/

namespace SDitH.Proofs.FreshKeyProbability

open Spec.IdealCipher Spec.BAVCCipherProgram Spec.DomainSeparation Spec.UniformChallenges FreshKeyUniform
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat} {Key Block : Type*} [Fintype Key]

/-- The seeds whose key is used in the history inject into the history's
entries. -/
theorem card_not_fresh_le (layout : Layout lambda Key Block) (hkey : Function.Injective layout.key)
    (world : World Key Block) :
    Nat.card {parent : Bits lambda // ¬ FreshKey world (layout.key parent)} ≤ world.history.length := by
  classical
  have hinj : Function.Injective (fun parent : {parent : Bits lambda // ¬ FreshKey world (layout.key parent)} =>
      (⟨layout.key parent.val, by
        obtain ⟨e, he, hk⟩ := by
          have := parent.property
          unfold FreshKey at this
          push_neg at this
          exact this
        exact List.mem_map.mpr ⟨e, he, hk⟩⟩ : {k : Key // k ∈ world.history.map Entry.key})) := by
    intro a b h
    apply Subtype.ext
    exact hkey (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Nat.card_eq_fintype_card]
  refine hcard.trans ?_
  rw [Fintype.card_subtype]
  calc (Finset.univ.filter fun k : Key => k ∈ world.history.map Entry.key).card
      = (world.history.map Entry.key).toFinset.card := by
        congr 1
        ext k
        simp
    _ ≤ (world.history.map Entry.key).length := List.toFinset_card_le _
    _ = world.history.length := by simp

/-- A uniform parent's key is not fresh with probability at most the
history's length over the number of seeds. -/
theorem not_fresh_probability (layout : Layout lambda Key Block) (hkey : Function.Injective layout.key)
    (world : World Key Block) :
    probability (fun parent : Bits lambda => ¬ FreshKey world (layout.key parent)) ≤
      (world.history.length : ℝ≥0∞) / (2 ^ lambda : ℕ) := by
  rw [IntegerSamplingProbability.probability_nat_card]
  have hcard : (Nat.card (Bits lambda) : ℝ≥0∞) = ((2 ^ lambda : ℕ) : ℝ≥0∞) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hcard]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_not_fresh_le layout hkey world) _

end
end SDitH.Proofs.FreshKeyProbability
