import SDitH.Proofs.IdealCipherPairProbability
import SDitH.Proofs.RandomOracleCollision

/-! Adaptive composition of the two-call collision bound. Both query directions,
changing keys, repeated calls and randomized stopping are included. A matching
observed half is charged only when first witnessed, using the same hidden family
for its companion. This module does not supply signature extraction or simulation. -/

namespace SDitH.Proofs.IdealCipherPairAdaptive

open Spec.IdealCipher Spec.IdealCipherPairCollision IdealCipherPairProbability
open scoped Classical ENNReal
noncomputable section

theorem bind_add_bound {A : Type*} (p : PMF A) (next base : A → PMF Bool)
    (epsilon : ℝ≥0∞) (h : ∀ a, next a true ≤ base a true + epsilon) :
    (p.bind next) true ≤ (p.bind base) true + epsilon := by
  simp only [PMF.bind_apply]
  calc
    _ ≤ ∑' a, p a * (base a true + epsilon) :=
      ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (h a) _)
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

variable {Key Block Tag State : Type*} [Fintype Key] [Fintype Block]

def pairCost (Block : Type*) [Fintype Block] (capacity q : Nat) : ℝ≥0∞ :=
  ((capacity : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞)) *
    ((capacity : ℝ≥0∞) / ((Fintype.card Block - (q + 2) : Nat) : ℝ≥0∞))

def historyLaw (project : Block → Tag) (companion : Block → Block) (world : World Key Block) : PMF Bool :=
  (PMF.uniformOfFintype (Candidates world)).map fun family => decide (Witnessed project companion family.val world.history)

theorem query_growth (world : World Key Block) (request : Query Key Block)
    (q : Nat) (hlen : world.history.length ≤ q) (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((PMF.uniformOfFintype (Candidates world)).map (fun family => decide (Witnessed project companion family.val
      (entry request (answer family.val request) :: world.history)))) true ≤
      historyLaw project companion world true + (world.history.length : ℝ≥0∞) * pairCost Block capacity q := by
  let earlier : Candidates world → Prop := fun family => Witnessed project companion family.val world.history
  let first : Candidates world → Prop := fun family =>
    ∃ old ∈ world.history, FirstPair project companion family.val world.history (entry request (answer family.val request)) old
  have hsplit := event_mass_mono (PMF.uniformOfFintype (Candidates world))
    (fun family => Witnessed project companion family.val (entry request (answer family.val request) :: world.history))
    (fun family => earlier family ∨ first family) (by
      intro family hw
      exact IdealCipherPairCollision.witnessed_cons project companion hinvolution hnofix family.val world.history _
        ((IdealCipher.matches_cons _ _ _ _).mpr ⟨family.property, rfl⟩) hw)
  have hor := RandomOracleCollision.boolean_or_mass (PMF.uniformOfFintype (Candidates world))
    (fun family => decide (earlier family)) (fun family => decide (first family))
  have hdecide : (fun family : Candidates world => @decide (earlier family ∨ first family) (Classical.propDecidable _)) =
      (fun family => decide (earlier family) || decide (first family)) := by
    funext family
    by_cases he : earlier family <;> by_cases hf : first family <;> simp [he, hf]
  rw [hdecide] at hsplit
  apply (hsplit.trans hor).trans
  apply add_le_add le_rfl
  have hunion := ChallengeMixtures.boolean_union_bound (PMF.uniformOfFintype (Candidates world))
    (fun family => decide (first family))
    (fun i : Fin world.history.length => fun family => decide
      (FirstPair project companion family.val world.history (entry request (answer family.val request)) world.history[i])) (by
        intro family _ hh
        obtain ⟨old, hold, hp⟩ := of_decide_eq_true hh
        obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hold
        exact ⟨⟨i, hi⟩, by simpa only [Fin.getElem_fin, he, decide_eq_true_eq] using hp⟩)
  apply hunion.trans
  calc
    _ ≤ ∑ _i : Fin world.history.length, pairCost Block capacity q := by
      apply Finset.sum_le_sum
      intro i _
      exact firstPair_bound world request world.history[i] q hlen project companion capacity hcapacity
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem run_bound (procedure : Procedure Key Block State) (budget : Nat)
    (state : State) (world : World Key Block) (q : Nat) (hlen : world.history.length + budget ≤ q)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((Spec.IdealCipherJoint.runPosterior procedure budget state world).map (fun joint =>
      decide (Witnessed project companion joint.1 joint.2.history))) true ≤
      historyLaw project companion world true +
        ((budget * world.history.length + budget.choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity q := by
  induction budget generalizing state world with
  | zero =>
    simp only [Spec.IdealCipherJoint.runPosterior, Spec.IdealCipherJoint.finish, PMF.map_comp, Function.comp_def,
      Nat.choose_zero_succ, Nat.cast_zero, zero_mul, add_zero, historyLaw, le_refl]
  | succ budget ih =>
    simp only [Spec.IdealCipherJoint.runPosterior, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      simp only [Spec.IdealCipherJoint.finish, PMF.map_comp, Function.comp_def]
      exact le_add_right le_rfl
    | query request next =>
      simp only [query, PMF.bind_map, PMF.map_bind, Function.comp_def]
      let after (sample : Candidates world) := observe world request (answer sample.val request) ⟨sample.val, sample.property, rfl⟩
      have hb (sample : Candidates world) := ih (next (answer sample.val request)) (after sample) (by
        change world.history.length + 1 + budget ≤ q
        omega)
      have hadd := bind_add_bound (PMF.uniformOfFintype (Candidates world))
        (fun sample => (Spec.IdealCipherJoint.runPosterior procedure budget (next (answer sample.val request)) (after sample)).map
          (fun joint => decide (Witnessed project companion joint.1 joint.2.history)))
        (fun sample => historyLaw project companion (after sample))
        (((budget * (world.history.length + 1) + budget.choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity q)
        hb
      apply hadd.trans
      have he := IdealCipher.posterior_step world request
        (fun _ history family => PMF.pure (decide (Witnessed project companion family history)))
      change ((PMF.uniformOfFintype (Candidates world)).bind (fun sample =>
        (PMF.uniformOfFintype (Candidates (after sample))).bind (fun family =>
          PMF.pure (decide (Witnessed project companion family.val (entry request (answer sample.val request) :: world.history)))))) true + _ ≤ _
      rw [he]
      have hg := query_growth world request q (by omega) project companion hinvolution hnofix capacity hcapacity
      calc
        _ ≤ (historyLaw project companion world true + (world.history.length : ℝ≥0∞) * pairCost Block capacity q) +
            (((budget * (world.history.length + 1) + budget.choose 2 : Nat) : ℝ≥0∞) * pairCost Block capacity q) :=
          add_le_add hg le_rfl
        _ = _ := by
          rw [add_assoc, ← add_mul, ← Nat.cast_add]
          congr 3
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          ring

/-- Adaptive two-call collision bound in the ICM. The probability includes all
randomized query choices; a request need not be fresh. For a useful finite
estimate one takes q+2 < |Block|. Category-III projection has capacity 2^64. -/
theorem experiment_bound (procedure : Procedure Key Block State) (budget : Nat) (initial : State)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((Spec.IdealCipherJoint.experiment procedure budget initial).map (fun joint =>
      decide (Witnessed project companion joint.1 joint.2.history))) true ≤
      (budget.choose 2 : ℝ≥0∞) * pairCost Block capacity budget := by
  have h := run_bound procedure budget initial empty budget (by simp [empty]) project companion hinvolution hnofix capacity hcapacity
  have hzero : historyLaw project companion (empty : World Key Block) true = 0 := by
    exact event_mass_zero _ _ (by simp [Witnessed, empty])
  rw [hzero] at h
  simpa only [Spec.IdealCipherJoint.experiment, empty, List.length_nil, Nat.mul_zero, Nat.zero_add, zero_add] using h

/-- The same bound stated directly against the once-sampled hidden family,
without using the posterior interpreter in the experiment expression. -/
theorem fixed_experiment_bound (procedure : Procedure Key Block State) (budget : Nat) (initial : State)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((PMF.uniformOfFintype (Family Key Block)).bind (fun family =>
      (runFixed procedure family budget initial []).map (fun out =>
        decide (Witnessed project companion family out.history)))) true ≤
      (budget.choose 2 : ℝ≥0∞) * pairCost Block capacity budget := by
  have h := experiment_bound procedure budget initial project companion hinvolution hnofix capacity hcapacity
  rw [IdealCipherJoint.experiment_eq, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def] using h

end
end SDitH.Proofs.IdealCipherPairAdaptive
