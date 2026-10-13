import SDitH.Proofs.IdealCipherPairCollision

/-! The probability charged to a newly matching observation pair. The first
half is obtained through a fresh forward or inverse query. Conditional on that
answer, an unobserved companion comparison contributes a second factor. -/

namespace SDitH.Proofs.IdealCipherPairProbability

open Spec.IdealCipher Spec.IdealCipherPairCollision IdealCipherFresh
open scoped Classical ENNReal
noncomputable section

theorem event_mass_mono {A : Type*} (p : PMF A) (left right : A → Prop)
    (h : ∀ a, left a → right a) :
    (p.map (fun a => decide (left a))) true ≤ (p.map (fun a => decide (right a))) true := by
  simp only [PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : left a
  · simp [ha, h a ha]
  · simp [ha]

theorem event_mass_zero {A : Type*} (p : PMF A) (event : A → Prop) (h : ∀ a, ¬ event a) :
    (p.map (fun a => decide (event a))) true = 0 := by
  have he : (fun a => decide (event a)) = fun _ => false := by
    funext a
    simp [h a]
  rw [he]
  have hc : p.map (fun _ => false) = PMF.pure false := PMF.map_const _ _
  rw [hc]
  simp

theorem bind_gate_bound {A : Type*} (p : PMF A) (next : A → PMF Bool) (gate : A → Prop)
    (epsilon : ℝ≥0∞) (h : ∀ a, next a true ≤ if gate a then epsilon else 0) :
    (p.bind next) true ≤ (p.map (fun a => decide (gate a))) true * epsilon := by
  rw [PMF.bind_apply, PMF.map_apply, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro a
  have ha := mul_le_mul_right (h a) (p a)
  by_cases hg : gate a <;> simpa [hg] using ha

variable {Key Block Tag : Type*}

theorem unseen_decrypt_fresh (world : World Key Block) (family : Candidates world)
    (key : Key) (output : Block)
    (h : Unseen world.history key ((family.val key).symm output)) : FreshOutput world key output := by
  intro e he hk ho
  apply h e he hk
  apply (family.val key).injective
  rw [Equiv.apply_symm_apply, ← ho]
  simpa only [hk] using family.property e he

variable [Fintype Key] [Fintype Block]

theorem firstHalf_bound (world : World Key Block) (request : Query Key Block) (old : Entry Key Block)
    (q : Nat) (hlen : world.history.length ≤ q) (project : Block → Tag) (capacity : Nat)
    (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((PMF.uniformOfFintype (Candidates world)).map (fun family =>
      decide (FirstHalf project world.history (entry request (answer family.val request)) old))) true ≤
      (capacity : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞) := by
  cases request with
  | encrypt key input =>
    by_cases hf : FreshInput world key input
    · apply (event_mass_mono _ _ (fun family => project (family.val key input) = project old.output)
        (fun _ h => h.2.2.2)).trans
      exact IdealCipherComparison.family_target_bound world key input hf q hlen project _ capacity (hcapacity _)
    · rw [event_mass_zero _ _ (fun _ h => hf h.1)]
      exact zero_le _
  | decrypt key output =>
    by_cases hf : FreshOutput world key output
    · apply (event_mass_mono _ _ (fun family => (family.val key).symm output = old.input)
        (fun _ h => h.2.2.1)).trans
      have ht := IdealCipherCapacity.fresh_decrypt_target_budget_bound world key output old.input hf q hlen
      simp only [query, PMF.map_comp, Function.comp_def, answer] at ht
      apply ht.trans
      letI : Nonempty {block : Block // project block = project old.output} := ⟨⟨old.output, rfl⟩⟩
      have hc : 1 ≤ capacity := (Fintype.card_pos (α := {block : Block // project block = project old.output})).trans_le (hcapacity _)
      rw [← one_div]
      exact ENNReal.div_le_div_right (by exact_mod_cast hc) _
    · rw [event_mass_zero _ _ (fun family h => hf (unseen_decrypt_fresh world family key output h.1))]
      exact zero_le _

theorem firstPair_conditional_bound (world : World Key Block) (request : Query Key Block)
    (value : Block) (hpossible : ∃ family : Family Key Block, Matches family world.history ∧ answer family request = value)
    (old : Entry Key Block) (q : Nat) (hlen : world.history.length ≤ q)
    (project : Block → Tag) (companion : Block → Block) (capacity : Nat)
    (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((PMF.uniformOfFintype (Candidates (observe world request value hpossible))).map (fun family =>
      decide (FirstPair project companion family.val world.history (entry request value) old))) true ≤
      if FirstHalf project world.history (entry request value) old then
        (capacity : ℝ≥0∞) / ((Fintype.card Block - (q + 2) : Nat) : ℝ≥0∞) else 0 := by
  by_cases hh : FirstHalf project world.history (entry request value) old
  · rw [if_pos hh]
    by_cases hf : Unseen ((entry request value) :: world.history) (entry request value).key (companion (entry request value).input) ∨
        Unseen ((entry request value) :: world.history) old.key (companion (entry request value).input)
    · apply (event_mass_mono _ _ (fun family =>
        project (family.val (entry request value).key (companion (entry request value).input)) =
          project (family.val old.key (companion (entry request value).input))) (fun _ h => h.2.1.2.2.2)).trans
      exact IdealCipherComparison.either_fresh_comparison_bound (observe world request value hpossible)
        (entry request value).key old.key hh.2.1 (companion (entry request value).input)
        hf (q + 1) (Nat.succ_le_succ hlen) project capacity hcapacity
    · rw [event_mass_zero _ _ (fun _ h => hf h.2.2)]
      exact zero_le _
  · rw [if_neg hh, event_mass_zero _ _ (fun _ h => hh ⟨h.1, h.2.1.1, h.2.1.2.1, h.2.1.2.2.1⟩)]

/-- Per earlier observation, a newly matching half with an unobserved matching
companion has two probability factors. Freshness is an event tested against
the actual history, not a premise about the adversary's chosen request. -/
theorem firstPair_bound (world : World Key Block) (request : Query Key Block) (old : Entry Key Block)
    (q : Nat) (hlen : world.history.length ≤ q) (project : Block → Tag)
    (companion : Block → Block) (capacity : Nat)
    (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((PMF.uniformOfFintype (Candidates world)).map (fun family =>
      decide (FirstPair project companion family.val world.history (entry request (answer family.val request)) old))) true ≤
      ((capacity : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞)) *
        ((capacity : ℝ≥0∞) / ((Fintype.card Block - (q + 2) : Nat) : ℝ≥0∞)) := by
  let test : Block → List (Entry Key Block) → Family Key Block → PMF Bool :=
    fun value _ family => PMF.pure (decide (FirstPair project companion family world.history (entry request value) old))
  have he := IdealCipher.posterior_step world request test
  change ((PMF.uniformOfFintype (Candidates world)).bind (fun family =>
    test (answer family.val request) (entry request (answer family.val request) :: world.history) family.val)) true ≤ _
  rw [← he]
  apply (bind_gate_bound _ _ (fun sample => FirstHalf project world.history (entry request (answer sample.val request)) old)
    ((capacity : ℝ≥0∞) / ((Fintype.card Block - (q + 2) : Nat) : ℝ≥0∞)) ?_).trans
  · exact mul_le_mul_left (firstHalf_bound world request old q hlen project capacity hcapacity) _
  · intro sample
    exact firstPair_conditional_bound world request (answer sample.val request) ⟨sample.val, sample.property, rfl⟩
      old q hlen project companion capacity hcapacity

end
end SDitH.Proofs.IdealCipherPairProbability
