import SDitH.Proofs.SignatureReplay

/-! Quantitative two-continuation replay at an actual saved fresh HashPiop
request. Success means both continuations win at that same input and their
answers differ. This proves a conditional replay bound at a fixed snapshot;
selecting a useful snapshot from forgery probability, witness-free signing
simulation and extraction from the two transcripts remain separate obligations. -/

namespace SDitH.Proofs.SignatureFork

open Spec.SignatureSecurity Spec.SignatureReplay
open scoped Classical ENNReal
noncomputable section

theorem boolean_mass_mono {A : Type*} (p : PMF A) (f g : A → Bool)
    (h : ∀ a, f a = true → g a = true) : (p.map f) true ≤ (p.map g) true := by
  simp only [PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  cases hf : f a with
  | false => simp
  | true => simp [h a hf]

theorem boolean_partition {A : Type*} (p : PMF A) (win split : A → Bool) :
    (p.map win) true = (p.map (fun a => win a && split a)) true +
      (p.map (fun a => win a && !split a)) true := by
  simp only [PMF.map_apply]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro a
  cases win a <;> cases split a <;> simp

theorem independent_both_success {A : Type*} (p : PMF A) (win : A → Bool) :
    (p.bind (fun left => p.map (fun right => win left && win right))) true =
      ((p.map win) true) ^ 2 := by
  calc
    _ = ∑' a, (if true = win a then p a else 0) * (p.map win) true := by
      rw [PMF.bind_apply]
      apply tsum_congr
      intro a
      cases win a <;> simp
    _ = (∑' a, if true = win a then p a else 0) * (p.map win) true :=
      ENNReal.tsum_mul_right
    _ = _ := by
      simp only [PMF.map_apply, pow_two]
      congr 1
      apply tsum_congr
      intro a
      by_cases h : true = win a <;> simp [h]

theorem uniform_label_guess {A D : Type*} [Fintype D] [Nonempty D]
    (p : PMF A) (label : A → D) (hlabel : p.map label = PMF.uniformOfFintype D) (d : D) :
    (p.map (fun a => decide (label a = d))) true = (Fintype.card D : ℝ≥0∞)⁻¹ := by
  rw [← PMF.uniformOfFintype_apply d, ← hlabel]
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  simp [eq_comm]

/-- A second successful copy can share the first copy's uniform answer with
probability at most 1/|D|. Uniformity is marginal, never conditioned on winning. -/
theorem successful_collision_bound {A D : Type*} [Fintype D] [Nonempty D]
    (p : PMF A) (win : A → Bool) (label : A → D)
    (hlabel : p.map label = PMF.uniformOfFintype D) :
    (p.bind (fun left => p.map (fun right =>
      win left && win right && decide (label left = label right)))) true ≤
        (p.map win) true * (Fintype.card D : ℝ≥0∞)⁻¹ := by
  have hnext (left : A) :
      (p.map (fun right => win left && win right && decide (label left = label right))) true ≤
        if win left then (Fintype.card D : ℝ≥0∞)⁻¹ else 0 := by
    cases hl : win left with
    | false => simp
    | true =>
      rw [← uniform_label_guess p label hlabel (label left)]
      apply boolean_mass_mono
      intro right h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact h.2.symm
  calc
    _ ≤ ∑' left, p left * (if win left then (Fintype.card D : ℝ≥0∞)⁻¹ else 0) := by
      rw [PMF.bind_apply]
      exact ENNReal.tsum_le_tsum (fun left => mul_le_mul_right (hnext left) _)
    _ = (∑' left, if true = win left then p left else 0) *
        (Fintype.card D : ℝ≥0∞)⁻¹ := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro left
      cases win left <;> simp
    _ = _ := by
      simp only [PMF.map_apply]
      congr 1
      apply tsum_congr
      intro a
      by_cases h : true = win a <;> simp [h]

theorem distinct_answer_replay_bound {A D : Type*} [Fintype D] [Nonempty D]
    (p : PMF A) (win : A → Bool) (label : A → D)
    (hlabel : p.map label = PMF.uniformOfFintype D) :
    ((p.map win) true) ^ 2 ≤
      (p.bind (fun left => p.map (fun right =>
        win left && win right && decide (label left ≠ label right)))) true +
        (p.map win) true * (Fintype.card D : ℝ≥0∞)⁻¹ := by
  let pairs := p.bind (fun left => p.map (fun right => (left, right)))
  have hpart := boolean_partition pairs
    (fun pair => win pair.1 && win pair.2)
    (fun pair => decide (label pair.1 ≠ label pair.2))
  simp only [pairs, PMF.map_bind, PMF.map_comp, Function.comp_def] at hpart
  rw [independent_both_success] at hpart
  rw [hpart]
  apply add_le_add le_rfl
  simpa only [← decide_not, not_not] using successful_collision_bound p win label hlabel

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- Squaring an average is bounded by averaging the squares. The state space
may be infinite; no finiteness premise is imposed on adversary states. -/
theorem square_mean_le_mean_square {A : Type*} (p : PMF A) (f : A → ℝ≥0∞)
    (hf : ∀ a, f a ≤ 1) : (∑' a, p a * f a) ^ 2 ≤ ∑' a, p a * (f a) ^ 2 := by
  have hpoint (a b : A) : 2 * f a * f b ≤ (f a) ^ 2 + (f b) ^ 2 := by
    have ha : f a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hf a)
    have hb : f b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hf b)
    generalize f a = x at ha ⊢
    generalize f b = y at hb ⊢
    lift x to NNReal using ha
    lift y to NNReal using hb
    exact_mod_cast two_mul_le_add_sq x y
  apply (ENNReal.mul_le_mul_iff_right (a := 2) (by norm_num) (by norm_num)).mp
  calc
    2 * (∑' a, p a * f a) ^ 2 = ∑' a, ∑' b, p a * p b * (2 * f a * f b) := by
      have he (a b : A) : p a * p b * (2 * f a * f b) =
          (2 * (p a * f a)) * (p b * f b) := by ring
      simp_rw [he, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_mul_left]
      ring
    _ ≤ ∑' a, ∑' b, p a * p b * ((f a) ^ 2 + (f b) ^ 2) := by
      exact ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun b =>
        mul_le_mul_right (hpoint a b) _
    _ = 2 * ∑' a, p a * (f a) ^ 2 := by
      have he (a b : A) : p a * p b * ((f a) ^ 2 + (f b) ^ 2) =
          (p a * (f a) ^ 2) * p b + p a * (p b * (f b) ^ 2) := by ring
      simp_rw [he, ENNReal.tsum_add, ENNReal.tsum_mul_left,
        ENNReal.tsum_mul_right, p.tsum_coe, mul_one, one_mul, two_mul]

/-- A proved bound for the defined replay algorithm. Let epsilon be the actual
target-winning probability after this snapshot. Then epsilon^2 is at most the
two-winning-distinct-answer probability plus epsilon/|Digest|. -/
theorem saved_fresh_query_fork_bound
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hfresh : snapshot.world.hashTable snapshot.input = none) :
    (((freshBranch scheme adversary snapshot).map (targetWin snapshot.input)) true) ^ 2 ≤
      ((forkAt scheme adversary snapshot).map (forkWins snapshot.input)) true +
      ((freshBranch scheme adversary snapshot).map (targetWin snapshot.input)) true *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have h := distinct_answer_replay_bound (freshBranch scheme adversary snapshot)
    (targetWin snapshot.input) Branch.answer
    (SignatureReplay.fresh_branch_answer_uniform scheme adversary snapshot)
  simpa only [forkAt, hfresh, PMF.map_bind, PMF.map_comp, Function.comp_def, forkWins] using h

theorem cut_fork_bound
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (saved : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State) :
    (singleAtCut scheme adversary saved true) ^ 2 ≤ forkAtCut scheme adversary saved true +
      singleAtCut scheme adversary saved true * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  cases saved with
  | ended terminal => simp [singleAtCut, forkAtCut]
  | saved snapshot =>
    cases he : snapshot.world.hashTable snapshot.input with
    | some answer => simp [singleAtCut, forkAtCut, forkAt, he, PMF.pure_map, forkWins]
    | none =>
      simpa only [singleAtCut, he, forkAtCut] using
        saved_fresh_query_fork_bound scheme adversary snapshot he

/-- Averaging over arbitrary random prefixes preserves the quantitative fork
bound. This includes terminated and nonfresh cuts, whose single success is zero. -/
theorem random_cut_fork_bound
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (cuts : PMF (Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State)) :
    ((cuts.bind (singleAtCut scheme adversary)) true) ^ 2 ≤
      (cuts.bind (forkAtCut scheme adversary)) true +
      (cuts.bind (singleAtCut scheme adversary)) true * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp only [PMF.bind_apply]
  calc
    _ ≤ ∑' saved, cuts saved * (singleAtCut scheme adversary saved true) ^ 2 :=
      square_mean_le_mean_square cuts _ (fun saved => (singleAtCut scheme adversary saved).coe_le_one true)
    _ ≤ ∑' saved, cuts saved * (forkAtCut scheme adversary saved true +
        singleAtCut scheme adversary saved true * (Fintype.card Digest : ℝ≥0∞)⁻¹) :=
      ENNReal.tsum_le_tsum fun saved => mul_le_mul_right (cut_fork_bound scheme adversary saved) _
    _ = _ := by simp_rw [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]

/-- The bound for the actual key-generation/adversary prefix experiment.
Relating its single-success probability to overall forgery probability still
requires the useful-query selection lemma; that premise is not assumed here. -/
theorem experiment_fork_bound
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (index fuel : Nat) :
    (singleExperiment scheme adversary index fuel true) ^ 2 ≤
      forkExperiment scheme adversary index fuel true +
      singleExperiment scheme adversary index fuel true * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
  random_cut_fork_bound scheme adversary (cutExperiment scheme adversary index fuel)

end
end SDitH.Proofs.SignatureFork
