import SDitH.Proofs.PrunedRunReverse

/-! The pruned-run agreement for the shared scheme's program runs. The
shared world pruned at a list of keys keeps its family and the other fields;
a program run from the resampled world and from the resampled pruned world
agree, in both directions, up to the touching term, for functions of the
result that do not read the family (as every continuation that resamples
before reading does not). -/

namespace SDitH.Proofs.SharedPrune

open Spec.IdealCipher (Family Entry Matches)
open Spec.HashCipherTrace (Result runFixed)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open CipherResample HiddenEntries PrunedRun PrunedRunReverse ChargeExpect
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The shared world pruned at a list of keys. -/
def pruneShared (K : List (Bits lambda)) (world : Spec.SharedScheme.World lambda s wit rnd) :
    Spec.SharedScheme.World lambda s wit rnd :=
  { world with cipherHistory := pruneAt K world.cipherHistory }

/-- The shared world's cipher history has an entry at the keys. -/
def touchesW (K : List (Bits lambda)) (world : Spec.SharedScheme.World lambda s wit rnd) : Bool :=
  decide (∃ e ∈ world.cipherHistory, e.key ∈ K)

/-- A function of a program result that does not read the family. -/
def FamilyFree {A : Type*}
    (ψ : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A × Spec.SharedScheme.World lambda s wit rnd → ℝ≥0∞) : Prop :=
  ∀ (a : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A) (world : Spec.SharedScheme.World lambda s wit rnd) (family : Family (Bits lambda) (Bits lambda)),
    ψ (a, { world with family := family }) = ψ (a, world)

/-- The program run from the resampled world is below the run from the
resampled pruned world plus the touching term. -/
theorem runProgram_le_prune {A : Type*} (K : List (Bits lambda)) (budget : Nat)
    (program : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd)
    (hpos : ∃ f : Family (Bits lambda) (Bits lambda), Matches f world.cipherHistory)
    (ψ : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A × Spec.SharedScheme.World lambda s wit rnd → ℝ≥0∞)
    (hψ : FamilyFree ψ) (hle : ∀ r, ψ r ≤ 1) :
    mean (resample world) (fun w => mean (Spec.SharedScheme.runProgram budget program w) fun r =>
      ψ (r.1, pruneShared K r.2)) ≤
    mean (resample (pruneShared K world)) (fun w => mean (Spec.SharedScheme.runProgram budget program w) fun r =>
      ψ r + indicator (touchesW K r.2)) := by
  have h := run_le_prune K Spec.HashCipherProgram.procedure budget program world.hashTable world.hashHistory
    world.cipherHistory hpos world.trace
    (fun out => ψ (out.state, ⟨world.family, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩))
    (fun out => hle _)
  unfold resample
  simp only [mean_map, Spec.SharedScheme.runProgram, pruneShared]
  refine le_of_eq_of_le ?_ (h.trans (le_of_eq ?_))
  · refine congrArg _ (funext fun f => congrArg _ (funext fun out => ?_))
    simp only [pruneResult]
    rw [hψ out.state ⟨world.family, out.hashTable, out.hashHistory, pruneAt K out.cipherHistory, out.trace⟩ f]
  · refine congrArg _ (funext fun f => congrArg _ (funext fun out => ?_))
    simp only [touchesW, touches]
    rw [hψ out.state ⟨world.family, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩ f]
    congr

/-- The program run from the resampled pruned world is below the run from the
resampled world plus the touching term. -/
theorem prune_le_runProgram {A : Type*} (K : List (Bits lambda)) (budget : Nat)
    (program : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd)
    (hpos : ∃ f : Family (Bits lambda) (Bits lambda), Matches f world.cipherHistory)
    (ψ : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A × Spec.SharedScheme.World lambda s wit rnd → ℝ≥0∞)
    (hψ : FamilyFree ψ) (hle : ∀ r, ψ r ≤ 1) :
    mean (resample (pruneShared K world)) (fun w => mean (Spec.SharedScheme.runProgram budget program w) ψ) ≤
    mean (resample world) (fun w => mean (Spec.SharedScheme.runProgram budget program w) fun r =>
      ψ (r.1, pruneShared K r.2)) +
    mean (resample (pruneShared K world)) (fun w => mean (Spec.SharedScheme.runProgram budget program w) fun r =>
      indicator (touchesW K r.2)) := by
  have h := prune_le_run K Spec.HashCipherProgram.procedure budget program world.hashTable world.hashHistory
    world.cipherHistory hpos world.trace
    (fun out => ψ (out.state, ⟨world.family, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩))
    (fun out => hle _)
  unfold resample
  simp only [mean_map, Spec.SharedScheme.runProgram, pruneShared]
  refine le_of_eq_of_le ?_ (h.trans (le_of_eq ?_))
  · refine congrArg _ (funext fun f => congrArg _ (funext fun out => ?_))
    rw [hψ out.state ⟨world.family, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩ f]
  · refine congrArg₂ (· + ·) (congrArg _ (funext fun f => congrArg _ (funext fun out => ?_)))
      (congrArg _ (funext fun f => congrArg _ (funext fun out => by simp only [touchesW, touches]; congr)))
    simp only [pruneResult]
    rw [hψ out.state ⟨world.family, out.hashTable, out.hashHistory, pruneAt K out.cipherHistory, out.trace⟩ f]

end
end SDitH.Proofs.SharedPrune
