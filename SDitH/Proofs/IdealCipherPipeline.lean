import SDitH.Spec.IdealCipherPipeline
import SDitH.Proofs.IdealCipherPairAdaptive
import SDitH.Proofs.IdealCipherTrace

namespace SDitH.Proofs.IdealCipherPipeline

open Spec.IdealCipher Spec.IdealCipherPairCollision Spec.IdealCipherPipeline
open IdealCipherPairAdaptive
open scoped Classical ENNReal
noncomputable section

variable {Key Block A B Tag : Type*} [Fintype Key] [Fintype Block]

theorem runPosterior_eq (first : Procedure Key Block A) (second : Procedure Key Block B)
    (k : Nat) (next : A → B) (q : Nat) (state : A) (world : World Key Block) :
    Spec.IdealCipherPipeline.runPosterior first second k next q state world =
      (PMF.uniformOfFintype (Candidates world)).bind (fun family =>
        (runFixed first family.val q state world.history).bind (fun start =>
          (runFixed second family.val k (next start.state) start.history).map fun out => (family.val, out))) := by
  induction q generalizing state world with
  | zero => simp only [Spec.IdealCipherPipeline.runPosterior, runFixed, PMF.pure_bind,
      IdealCipherJoint.runPosterior_eq]
  | succ q ih =>
    simp only [Spec.IdealCipherPipeline.runPosterior, runFixed, PMF.bind_bind]
    rw [PMF.bind_comm]
    congr 1
    funext action
    cases action with
    | stop => simp only [PMF.pure_bind, IdealCipherJoint.runPosterior_eq]
    | query request advance =>
      simp_rw [ih]
      exact IdealCipherJoint.query_resample world request (fun value history family =>
        (runFixed first family q (advance value) history).bind (fun start =>
          (runFixed second family k (next start.state) start.history).map fun out => (family, out)))

theorem experiments_eq (first : Procedure Key Block A) (q : Nat) (initial : A)
    (second : Procedure Key Block B) (k : Nat) (next : A → B) :
    Spec.IdealCipherPipeline.runPosterior first second k next q initial empty =
      jointExperiment first q initial second k next := by
  rw [runPosterior_eq, jointExperiment,
    ← IntegerSamplingProbability.map_uniform_equiv (IdealCipher.emptyEquiv (Key := Key) (Block := Block)), PMF.bind_map]
  rfl

theorem charge_mono (small large n : Nat) (h : small ≤ large) :
    small * n + small.choose 2 ≤ large * n + large.choose 2 := by
  exact Nat.add_le_add (Nat.mul_le_mul_right n h) (Nat.choose_le_choose 2 h)

/-- The paired-collision bound composes across an adaptively selected second
phase, counting its comparisons with the first phase's complete history. -/
theorem run_bound (first : Procedure Key Block A) (second : Procedure Key Block B)
    (k : Nat) (next : A → B) (q : Nat) (state : A) (world : World Key Block)
    (total : Nat) (hlen : world.history.length + (q + k) ≤ total)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((Spec.IdealCipherPipeline.runPosterior first second k next q state world).map (fun joint =>
      decide (Witnessed project companion joint.1 joint.2.history))) true ≤
      historyLaw project companion world true +
        (((q + k) * world.history.length + (q + k).choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total := by
  induction q generalizing state world with
  | zero =>
    simpa only [Spec.IdealCipherPipeline.runPosterior, Nat.zero_add] using
      IdealCipherPairAdaptive.run_bound second k (next state) world total (by omega)
      project companion hinvolution hnofix capacity hcapacity
  | succ q ih =>
    simp only [Spec.IdealCipherPipeline.runPosterior, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      apply (IdealCipherPairAdaptive.run_bound second k (next state) world total (by omega)
        project companion hinvolution hnofix capacity hcapacity).trans
      apply add_le_add le_rfl
      apply mul_le_mul_left
      exact_mod_cast charge_mono k (q + 1 + k) world.history.length (by omega)
    | query request advance =>
      simp only [query, PMF.bind_map, PMF.map_bind, Function.comp_def]
      let after (sample : Candidates world) := observe world request (answer sample.val request) ⟨sample.val, sample.property, rfl⟩
      have hb (sample : Candidates world) := ih (advance (answer sample.val request)) (after sample) (by
        change world.history.length + 1 + (q + k) ≤ total
        omega)
      have hadd := bind_add_bound (PMF.uniformOfFintype (Candidates world))
        (fun sample => (Spec.IdealCipherPipeline.runPosterior first second k next q (advance (answer sample.val request)) (after sample)).map
          (fun joint => decide (Witnessed project companion joint.1 joint.2.history)))
        (fun sample => historyLaw project companion (after sample))
        ((((q + k) * (world.history.length + 1) + (q + k).choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity total) hb
      apply hadd.trans
      have he := IdealCipher.posterior_step world request
        (fun _ history family => PMF.pure (decide (Witnessed project companion family history)))
      change ((PMF.uniformOfFintype (Candidates world)).bind (fun sample =>
        (PMF.uniformOfFintype (Candidates (after sample))).bind (fun family =>
          PMF.pure (decide (Witnessed project companion family.val (entry request (answer sample.val request) :: world.history)))))) true + _ ≤ _
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

theorem collision_bound (first : Procedure Key Block A) (q : Nat) (initial : A)
    (second : Procedure Key Block B) (k : Nat) (next : A → B)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((jointExperiment first q initial second k next).map (fun joint =>
      decide (Witnessed project companion joint.1 joint.2.history))) true ≤
      ((q + k).choose 2 : ℝ≥0∞) * pairCost Block capacity (q + k) := by
  have h := run_bound first second k next q initial empty (q + k) (by simp [empty])
    project companion hinvolution hnofix capacity hcapacity
  have hzero : historyLaw project companion (empty : World Key Block) true = 0 :=
    IdealCipherPairProbability.event_mass_zero _ _ (by simp [Witnessed, empty])
  rw [hzero, experiments_eq] at h
  simpa only [empty, List.length_nil, Nat.mul_zero, Nat.zero_add, zero_add] using h

theorem event_bound (first : Procedure Key Block A) (q : Nat) (initial : A)
    (second : Procedure Key Block B) (k : Nat) (next : A → B)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity)
    (bad : Result Key Block B → Bool)
    (hbad : ∀ joint ∈ (jointExperiment first q initial second k next).support,
      bad joint.2 = true → Witnessed project companion joint.1 joint.2.history) :
    ((experiment first q initial second k next).map bad) true ≤
      ((q + k).choose 2 : ℝ≥0∞) * pairCost Block capacity (q + k) := by
  apply le_trans ?_ (collision_bound first q initial second k next project companion hinvolution hnofix capacity hcapacity)
  simp only [experiment, PMF.map_comp, Function.comp_def, PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro joint
  by_cases hs : joint ∈ (jointExperiment first q initial second k next).support
  · by_cases hw : bad joint.2 = true
    · simp [hw, hbad joint hs hw]
    · simp [hw]
  · have hz : jointExperiment first q initial second k next joint = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hs
    simp [hz]

end
end SDitH.Proofs.IdealCipherPipeline
