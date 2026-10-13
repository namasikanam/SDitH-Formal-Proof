import SDitH.Proofs.HashCipherPipeline
import SDitH.Proofs.HashCipherPair
import SDitH.Proofs.IdealCipherPipeline

namespace SDitH.Proofs.HashCipherPipelineSecurity

open Spec.HashCipher Spec.IdealCipherPairCollision
open IdealCipherPairAdaptive
open scoped Classical ENNReal
noncomputable section

variable {Input Digest Key Block A B Tag : Type*}
variable [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]

/-- The second phase can depend on every answer revealed in the first phase.
Its paired-cipher cost includes comparisons with that earlier history. -/
theorem run_pair_bound (first : Procedure Input Digest Key Block A) (second : Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) (q : Nat) (state : A) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (world : Spec.IdealCipher.World Key Block)
    (total : Nat) (hlen : world.history.length + (q + k) ≤ total)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((Spec.HashCipherPipeline.runPosterior first second k next q state table hashes world).map (cipherEvent project companion)) true ≤
      historyLaw project companion world true +
        (((q + k) * world.history.length + (q + k).choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total := by
  induction q generalizing state table hashes world with
  | zero =>
    simpa only [Spec.HashCipherPipeline.runPosterior, Nat.zero_add] using
      HashCipherPair.run_pair_bound second k (next state) table hashes world total (by omega)
        project companion hinvolution hnofix capacity hcapacity
  | succ q ih =>
    simp only [Spec.HashCipherPipeline.runPosterior, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      apply (HashCipherPair.run_pair_bound second k (next state) table hashes world total (by omega)
        project companion hinvolution hnofix capacity hcapacity).trans
      apply add_le_add le_rfl
      apply mul_le_mul_left
      exact_mod_cast IdealCipherPipeline.charge_mono k (q + 1 + k) world.history.length (by omega)
    | hash input advance =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, cipherEvent, markJoint, markHash]
      have hrest := ChallengeMixtures.bind_true_le (Spec.RandomOracle.query table input)
        (fun result => (Spec.HashCipherPipeline.runPosterior first second k next q (advance result.1)
          result.2 ((input, result.1) :: hashes) world).map (cipherEvent project companion))
        (historyLaw project companion world true +
          (((q + k) * world.history.length + (q + k).choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total)
        (fun result _ => ih (advance result.1) result.2 ((input, result.1) :: hashes) world (by omega))
      apply hrest.trans
      apply add_le_add le_rfl
      apply mul_le_mul_left
      exact_mod_cast IdealCipherPipeline.charge_mono (q + k) (q + 1 + k) world.history.length (by omega)
    | cipher request advance =>
      simp only [Spec.IdealCipher.query, PMF.bind_map, PMF.map_bind, Function.comp_def]
      let after (sample : Spec.IdealCipher.Candidates world) :=
        Spec.IdealCipher.observe world request (Spec.IdealCipher.answer sample.val request) ⟨sample.val, sample.property, rfl⟩
      have hb (sample : Spec.IdealCipher.Candidates world) :=
        ih (advance (Spec.IdealCipher.answer sample.val request)) table hashes (after sample) (by
          change world.history.length + 1 + (q + k) ≤ total
          omega)
      have hadd := bind_add_bound (PMF.uniformOfFintype (Spec.IdealCipher.Candidates world))
        (fun sample => (Spec.HashCipherPipeline.runPosterior first second k next q
          (advance (Spec.IdealCipher.answer sample.val request)) table hashes (after sample)).map (cipherEvent project companion))
        (fun sample => historyLaw project companion (after sample))
        ((((q + k) * (world.history.length + 1) + (q + k).choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total) hb
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
            ((((q + k) * (world.history.length + 1) + (q + k).choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total) :=
          add_le_add hg le_rfl
        _ = _ := by
          rw [add_assoc, ← add_mul, ← Nat.cast_add]
          congr 3
          rw [Nat.add_right_comm q 1 k, Nat.choose_succ_succ, Nat.choose_one_right]
          ring

theorem pair_bound (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((Spec.HashCipherPipeline.jointExperiment first q initial second k next).map (cipherEvent project companion)) true ≤
      ((q + k).choose 2 : ℝ≥0∞) * pairCost Block capacity (q + k) := by
  have h := run_pair_bound first second k next q initial (fun _ => none) [] Spec.IdealCipher.empty (q + k)
    (by simp [Spec.IdealCipher.empty]) project companion hinvolution hnofix capacity hcapacity
  have hzero : historyLaw project companion (Spec.IdealCipher.empty : Spec.IdealCipher.World Key Block) true = 0 :=
    IdealCipherPairProbability.event_mass_zero _ _ (by simp [Witnessed, Spec.IdealCipher.empty])
  rw [hzero, HashCipherPipeline.experiments_eq] at h
  simpa only [Spec.IdealCipher.empty, List.length_nil, Nat.mul_zero, Nat.zero_add, zero_add] using h

theorem combined_bound (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((Spec.HashCipherPipeline.jointExperiment first q initial second k next).map (combinedEvent project companion)) true ≤
      ((q + k).choose 2 : ℝ≥0∞) *
        ((Fintype.card Digest : ℝ≥0∞)⁻¹ + pairCost Block capacity (q + k)) := by
  apply (RandomOracleCollision.boolean_or_mass (Spec.HashCipherPipeline.jointExperiment first q initial second k next)
    (fun joint => joint.2.hashCollided) (cipherEvent project companion)).trans
  calc
    _ ≤ ((q + k).choose 2 : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        ((q + k).choose 2 : ℝ≥0∞) * pairCost Block capacity (q + k) :=
      add_le_add (HashCipherPipeline.hash_bound first q initial second k next)
        (pair_bound first q initial second k next project companion hinvolution hnofix capacity hcapacity)
    _ = _ := (mul_add _ _ _).symm

/-- Monotonicity on the actual supported executions. This is used only after
the caller derives event coverage from its computation. -/
theorem event_mass_le {X : Type*} (law : PMF X) (left right : X → Bool)
    (h : ∀ x ∈ law.support, left x = true → right x = true) :
    (law.map left) true ≤ (law.map right) true := by
  simp only [PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hs : x ∈ law.support
  · by_cases hl : left x = true
    · simp [hl, h x hs hl]
    · simp [hl]
  · have hz : law x = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
    simp [hz]

theorem event_bound (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity)
    (bad : Result Input Digest Key Block B → Bool)
    (hcover : ∀ joint ∈ (Spec.HashCipherPipeline.jointExperiment first q initial second k next).support,
      bad joint.2 = true → (∃ pair, Spec.RandomOracleCollision.storedCollision pair (hashView joint.2) = true) ∨
        Witnessed project companion joint.1 joint.2.cipherHistory) :
    ((Spec.HashCipherPipeline.experiment first q initial second k next).map bad) true ≤
      ((q + k).choose 2 : ℝ≥0∞) *
        ((Fintype.card Digest : ℝ≥0∞)⁻¹ + pairCost Block capacity (q + k)) := by
  apply le_trans ?_ (combined_bound first q initial second k next project companion hinvolution hnofix capacity hcapacity)
  simp only [Spec.HashCipherPipeline.experiment, PMF.map_comp, Function.comp_def]
  apply event_mass_le
  intro joint hs hw
  rcases hcover joint hs hw with ⟨pair, hp⟩ | hc
  · simp only [combinedEvent, HashCipherPipeline.stored_collision_implies_flag first q initial second k next joint hs pair hp, Bool.true_or]
  · simp only [combinedEvent, cipherEvent, hc, decide_true, Bool.or_true]

end
end SDitH.Proofs.HashCipherPipelineSecurity
