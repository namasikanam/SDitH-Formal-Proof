import SDitH.Proofs.HashCipherPair
import SDitH.Proofs.CipherResample
import SDitH.Proofs.HashCipher
import SDitH.Proofs.HashCipherTrace
import SDitH.Proofs.MeanHybrid
import SDitH.Proofs.HiddenSlice
import SDitH.Proofs.ForkRestoreEq

/-! The posterior mass of the witnessed pair event at a cipher history: the
probability, under the posterior family of the history, that two recorded
entries with distinct keys and a common input have equal projected outputs
and equal projected companion outputs. A shared program run from a
resampled world raises this mass by at most the adaptive pair cost of its
budget, which is the single-run paired-cipher bound read through the
resampling law. -/

namespace SDitH.Proofs.PairMass

open Spec.IdealCipher Spec.IdealCipherPairCollision
open Spec.RandomOracleTrap (indicator)
open CipherResample ChargeExpect IdealCipherPairAdaptive ForkRestoreEq MeanHybrid HiddenSlice
open scoped Classical ENNReal

noncomputable section

theorem indicator_le_one' (b : Bool) : indicator b ≤ 1 := by
  cases b <;> simp [indicator]

theorem pure_true (b : Bool) : (PMF.pure b) true = indicator b := by
  cases b <;> simp [PMF.pure_apply, indicator]

section Cipher

variable {Key Block Tag : Type*} [Fintype Key] [Fintype Block]

/-- The posterior mass of the witnessed pair event at a history. -/
def pairMass (project : Block → Tag) (companion : Block → Block) (history : List (Entry Key Block)) : ℝ≥0∞ :=
  mean (posterior history) fun g => indicator (decide (Witnessed project companion g history))

theorem pairMass_le_one (project : Block → Tag) (companion : Block → Block) (history : List (Entry Key Block)) :
    pairMass project companion history ≤ 1 :=
  mean_le_const _ _ _ fun _ _ => indicator_le_one' _

theorem pairMass_nil (project : Block → Tag) (companion : Block → Block) :
    pairMass project companion ([] : List (Entry Key Block)) = 0 := by
  unfold pairMass
  refine le_antisymm (mean_le_const _ _ _ fun g _ => ?_) (zero_le _)
  have h : ¬ Witnessed project companion g [] := by
    rintro ⟨left, hleft, _⟩
    simp at hleft
  simp [h, indicator]

/-- A history every matching family witnesses has mass one. -/
theorem pairMass_eq_one (project : Block → Tag) (companion : Block → Block) (history : List (Entry Key Block))
    (hpos : ∃ g : Family Key Block, Matches g history)
    (h : ∀ g : Family Key Block, Matches g history → Witnessed project companion g history) :
    pairMass project companion history = 1 := by
  unfold pairMass
  rw [posterior_world ⟨history, hpos⟩, mean_map]
  refine (mean_congr_support _ _ (fun _ => 1) fun f _ => ?_).trans (mean_const _ 1)
  simp [h f.val f.property, indicator]

/-- The history law of a world is the pair mass of its history. -/
theorem historyLaw_eq (project : Block → Tag) (companion : Block → Block) (world : World Key Block) :
    (historyLaw project companion world) true = pairMass project companion world.history := by
  unfold historyLaw pairMass
  rw [map_true, posterior_world world, mean_map]

/-- The pair cost grows with the total. -/
theorem pairCost_mono (capacity : Nat) {q q' : Nat} (h : q ≤ q') :
    pairCost Block capacity q ≤ pairCost Block capacity q' := by
  unfold pairCost
  refine mul_le_mul' (ENNReal.div_le_div_left ?_ _) (ENNReal.div_le_div_left ?_ _)
  · exact Nat.cast_le.mpr (Nat.sub_le_sub_left h _)
  · exact Nat.cast_le.mpr (Nat.sub_le_sub_left (by omega) _)

end Cipher

section Shared

open Spec.DomainSeparation (Bits)

variable {lambda s wit rnd : Nat}

/-- A shared program run from a resampled world raises the pair mass by at
most the adaptive pair cost of its budget. -/
theorem runProgram_pair_bound {A : Type*} (budget : Nat)
    (program : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g world.cipherHistory)
    (total : Nat) (hlen : world.cipherHistory.length + budget ≤ total)
    (project : Bits lambda → Bits lambda) (companion : Bits lambda → Bits lambda)
    (hinv : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcap : ∀ target, Fintype.card {output : Bits lambda // project output = target} ≤ capacity) :
    mean (resample world) (fun w => mean (Spec.SharedScheme.runProgram budget program w) fun r =>
        pairMass project companion r.2.cipherHistory) ≤
      pairMass project companion world.cipherHistory +
        ((budget * world.cipherHistory.length + budget.choose 2 : Nat) : ℝ≥0∞) * pairCost (Bits lambda) capacity total := by
  set W : World (Bits lambda) (Bits lambda) := ⟨world.cipherHistory, hpos⟩ with hW
  have hres := runFixed_resample Spec.HashCipherProgram.procedure budget program world.hashTable world.hashHistory W
    world.trace (fun out g => PMF.pure (decide (Witnessed project companion g out.cipherHistory)))
  have hres' := congrArg (fun p : PMF Bool => p true) hres
  simp only [mean_bind_apply, pure_true] at hres'
  calc mean (resample world) (fun w => mean (Spec.SharedScheme.runProgram budget program w) fun r =>
        pairMass project companion r.2.cipherHistory)
      = mean (posterior W.history) fun g =>
          mean (Spec.HashCipherTrace.runFixed Spec.HashCipherProgram.procedure g budget program world.hashTable
            world.hashHistory W.history world.trace) fun out =>
            mean (posterior out.cipherHistory) fun g' =>
              indicator (decide (Witnessed project companion g' out.cipherHistory)) := by
        simp only [resample, Spec.SharedScheme.runProgram, mean_map, pairMass]
        rfl
    _ = mean (posterior W.history) fun g =>
          mean (Spec.HashCipherTrace.runFixed Spec.HashCipherProgram.procedure g budget program world.hashTable
            world.hashHistory W.history world.trace) fun out =>
            indicator (decide (Witnessed project companion g out.cipherHistory)) := hres'.symm
    _ = ((Spec.HashCipher.runPosterior Spec.HashCipherProgram.procedure budget program world.hashTable world.hashHistory W).map
          (Spec.HashCipher.cipherEvent project companion)) true := by
        rw [HashCipher.runPosterior_eq, PMF.map_bind, mean_bind_apply, posterior_world W, mean_map]
        refine congrArg _ (funext fun f => ?_)
        rw [← HashCipherTrace.runFixed_forget _ _ _ _ _ _ _ world.trace, PMF.map_comp, PMF.map_comp, map_true]
        rfl
    _ ≤ (historyLaw project companion W) true +
          ((budget * W.history.length + budget.choose 2 : Nat) : ℝ≥0∞) * pairCost (Bits lambda) capacity total :=
        HashCipherPair.run_pair_bound Spec.HashCipherProgram.procedure budget program world.hashTable world.hashHistory W
          total hlen project companion hinv hnofix capacity (fun target => by convert hcap target)
    _ = _ := by rw [historyLaw_eq]

end Shared

end
end SDitH.Proofs.PairMass
