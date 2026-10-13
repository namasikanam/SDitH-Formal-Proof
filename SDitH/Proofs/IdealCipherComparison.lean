import SDitH.Proofs.IdealCipherCapacity
import SDitH.Proofs.IdealCipherJoint
import SDitH.Proofs.ChallengeMixtures

/-! Conditional equality of projected cipher outputs at different keys.
The other key's answer may be unqueried: an auxiliary exposure derives the
bound from compatible permutations instead of assuming independence. -/

namespace SDitH.Proofs.IdealCipherComparison

open Spec.IdealCipher IdealCipherFresh
open scoped Classical ENNReal
noncomputable section

variable {Key Block Tag : Type*}

theorem fresh_observe (world : World Key Block) (request : Query Key Block) (value : Block)
    (hpossible : ∃ family : Family Key Block, Matches family world.history ∧ answer family request = value)
    (key : Key) (input : Block) (hfresh : FreshInput world key input)
    (hnew : (entry request value).key ≠ key ∨ (entry request value).input ≠ input) :
    FreshInput (observe world request value hpossible) key input := by
  intro e he hk hi
  rcases List.mem_cons.mp he with rfl | he
  · rcases hnew with hnew | hnew
    · exact hnew hk
    · exact hnew hi
  · exact hfresh e he hk hi

variable [Fintype Key] [Fintype Block]

theorem family_target_bound (world : World Key Block) (key : Key) (input : Block)
    (hfresh : FreshInput world key input) (q : Nat) (hlen : world.history.length ≤ q)
    (project : Block → Tag) (target : Tag) (capacity : Nat)
    (hcapacity : Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((PMF.uniformOfFintype (Candidates world)).map
      (fun family => decide (project (family.val key input) = target))) true ≤
      (capacity : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞) := by
  have h := IdealCipherCapacity.fresh_encrypt_event_budget_bound world key input hfresh q hlen
    (fun output => project output = target)
  simp only [query, PMF.map_comp, Function.comp_def, answer] at h
  exact h.trans (ENNReal.div_le_div_right (by exact_mod_cast hcapacity) _)

/-- One fresh side suffices, even if neither side has yet been observed.
The auxiliary other-key query costs at most one additional graph entry. -/
theorem fresh_comparison_bound (world : World Key Block) (left right : Key)
    (hkeys : left ≠ right) (input : Block) (hfresh : FreshInput world left input)
    (q : Nat) (hlen : world.history.length ≤ q) (project : Block → Tag) (capacity : Nat)
    (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((PMF.uniformOfFintype (Candidates world)).map
      (fun family => decide (project (family.val left input) = project (family.val right input)))) true ≤
      (capacity : ℝ≥0∞) / ((Fintype.card Block - (q + 1) : Nat) : ℝ≥0∞) := by
  let test : Block → List (Entry Key Block) → Family Key Block → PMF Bool :=
    fun _ _ family => PMF.pure (decide (project (family left input) = project (family right input)))
  have he := IdealCipher.posterior_step world (.encrypt right input) test
  change ((PMF.uniformOfFintype (Candidates world)).bind (fun family =>
    test (answer family.val (.encrypt right input))
      (entry (.encrypt right input) (answer family.val (.encrypt right input)) :: world.history) family.val)) true ≤ _
  rw [← he]
  apply ChallengeMixtures.bind_true_le
  intro sample _
  let observed := observe world (.encrypt right input) (answer sample.val (.encrypt right input))
    ⟨sample.val, sample.property, rfl⟩
  have hf : FreshInput observed left input := fresh_observe world _ _ _ left input hfresh (Or.inl (Ne.symm hkeys))
  have hl : observed.history.length ≤ q + 1 := Nat.succ_le_succ hlen
  have ht (family : Candidates observed) : family.val right input = sample.val right input :=
    family.property _ List.mem_cons_self
  have htest : (fun family : Candidates observed => test (answer sample.val (.encrypt right input))
      (entry (.encrypt right input) (answer sample.val (.encrypt right input)) :: world.history) family.val) =
      (fun family => PMF.pure (decide (project (family.val left input) = project (sample.val right input)))) := by
    funext family
    simp only [test, ht family]
  rw [htest]
  exact family_target_bound observed left input hf (q + 1) hl project _ capacity (hcapacity _)

theorem either_fresh_comparison_bound (world : World Key Block) (left right : Key)
    (hkeys : left ≠ right) (input : Block)
    (hfresh : FreshInput world left input ∨ FreshInput world right input)
    (q : Nat) (hlen : world.history.length ≤ q) (project : Block → Tag) (capacity : Nat)
    (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((PMF.uniformOfFintype (Candidates world)).map
      (fun family => decide (project (family.val left input) = project (family.val right input)))) true ≤
      (capacity : ℝ≥0∞) / ((Fintype.card Block - (q + 1) : Nat) : ℝ≥0∞) := by
  rcases hfresh with hf | hf
  · exact fresh_comparison_bound world left right hkeys input hf q hlen project capacity hcapacity
  · simpa only [eq_comm] using fresh_comparison_bound world right left (Ne.symm hkeys) input hf q hlen project capacity hcapacity

end
end SDitH.Proofs.IdealCipherComparison
