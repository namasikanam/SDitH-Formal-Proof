import SDitH.Proofs.HashCipher
import SDitH.Proofs.IdealCipherPairAdaptive

namespace SDitH.Proofs.HashCipherPair

open Spec.HashCipher Spec.IdealCipherPairCollision
open IdealCipherPairAdaptive
open scoped Classical ENNReal
noncomputable section

variable {Input Digest Key Block State Tag : Type*}
variable [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]

/-- The paired-cipher event remains bounded while hash answers can determine
future cipher inputs, keys and directions. The hash branch preserves the hidden
family's conditional law by the checked joint interpreter equivalence. -/
theorem run_pair_bound (procedure : Procedure Input Digest Key Block State)
    (budget : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (world : Spec.IdealCipher.World Key Block) (total : Nat) (hlen : world.history.length + budget ≤ total)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((runPosterior procedure budget state table hashes world).map (cipherEvent project companion)) true ≤
      historyLaw project companion world true +
        ((budget * world.history.length + budget.choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total := by
  induction budget generalizing state table hashes world with
  | zero =>
    simp only [runPosterior, finish, PMF.map_comp, Function.comp_def, cipherEvent,
      Nat.choose_zero_succ, Nat.cast_zero, zero_mul, add_zero, historyLaw, le_refl]
  | succ budget ih =>
    simp only [runPosterior, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      simp only [finish, PMF.map_comp, Function.comp_def, cipherEvent]
      exact le_add_right le_rfl
    | hash input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, cipherEvent, markJoint, markHash]
      have hrest := ChallengeMixtures.bind_true_le (Spec.RandomOracle.query table input)
        (fun result => (runPosterior procedure budget (next result.1) result.2 ((input, result.1) :: hashes) world).map
          (cipherEvent project companion))
        (historyLaw project companion world true +
          ((budget * world.history.length + budget.choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total)
        (fun result _ => ih (next result.1) result.2 ((input, result.1) :: hashes) world (by omega))
      apply hrest.trans
      apply add_le_add le_rfl
      apply mul_le_mul_left
      exact_mod_cast Nat.add_le_add (Nat.mul_le_mul_right world.history.length (Nat.le_succ budget))
        (Nat.choose_le_choose 2 (Nat.le_succ budget))
    | cipher request next =>
      simp only [Spec.IdealCipher.query, PMF.bind_map, PMF.map_bind, Function.comp_def]
      let after (sample : Spec.IdealCipher.Candidates world) :=
        Spec.IdealCipher.observe world request (Spec.IdealCipher.answer sample.val request) ⟨sample.val, sample.property, rfl⟩
      have hb (sample : Spec.IdealCipher.Candidates world) :=
        ih (next (Spec.IdealCipher.answer sample.val request)) table hashes (after sample) (by
          change world.history.length + 1 + budget ≤ total
          omega)
      have hadd := bind_add_bound (PMF.uniformOfFintype (Spec.IdealCipher.Candidates world))
        (fun sample => (runPosterior procedure budget (next (Spec.IdealCipher.answer sample.val request)) table hashes (after sample)).map
          (cipherEvent project companion))
        (fun sample => historyLaw project companion (after sample))
        (((budget * (world.history.length + 1) + budget.choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total) hb
      apply hadd.trans
      have he := IdealCipher.posterior_step world request
        (fun _ history family => PMF.pure (decide (Witnessed project companion family history)))
      change ((PMF.uniformOfFintype (Spec.IdealCipher.Candidates world)).bind (fun sample =>
        (PMF.uniformOfFintype (Spec.IdealCipher.Candidates (after sample))).bind (fun family =>
          PMF.pure (decide (Witnessed project companion family.val
            (Spec.IdealCipher.entry request (Spec.IdealCipher.answer sample.val request) :: world.history)))))) true + _ ≤ _
      rw [he]
      have hg := query_growth world request total (by omega) project companion hinvolution hnofix capacity hcapacity
      calc
        _ ≤ (historyLaw project companion world true + (world.history.length : ℝ≥0∞) * pairCost Block capacity total) +
            (((budget * (world.history.length + 1) + budget.choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total) :=
          add_le_add hg le_rfl
        _ = _ := by
          rw [add_assoc, ← add_mul, ← Nat.cast_add]
          congr 3
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          ring

theorem experiment_pair_bound (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((jointExperiment procedure budget initial).map (cipherEvent project companion)) true ≤
      (budget.choose 2 : ℝ≥0∞) * pairCost Block capacity budget := by
  have h := run_pair_bound procedure budget initial (fun _ => none) [] Spec.IdealCipher.empty budget (by simp [Spec.IdealCipher.empty])
    project companion hinvolution hnofix capacity hcapacity
  have hzero : historyLaw project companion (Spec.IdealCipher.empty : Spec.IdealCipher.World Key Block) true = 0 :=
    IdealCipherPairProbability.event_mass_zero _ _ (by simp [Witnessed, Spec.IdealCipher.empty])
  rw [hzero, HashCipher.experiments_eq] at h
  simpa only [Spec.IdealCipher.empty, List.length_nil, Nat.mul_zero, Nat.zero_add, zero_add] using h

end
end SDitH.Proofs.HashCipherPair
