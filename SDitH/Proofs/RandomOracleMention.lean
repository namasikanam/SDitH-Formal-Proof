import SDitH.Spec.RandomOracleMention
import SDitH.Proofs.RandomOracleTrace

/-! Prefix-dependent trap bound: with per-query bound epsilon(n) after n
fresh entries, the event is bounded by the sum of epsilon over the fresh
positions. The mention instance has epsilon(n) = n*m/|Output| for mention
sets of size at most m, giving choose(budget,2)*m/|Output| overall. -/

namespace SDitH.Proofs.RandomOracleMention

open Spec.RandomOracleTrace Spec.RandomOracleTrap Spec.RandomOracleMention
open scoped Classical ENNReal BigOperators
noncomputable section

variable {Input Output State : Type*} [Fintype Output] [Nonempty Output]

omit [Fintype Output] [Nonempty Output] in
theorem prefixBad_cons (bad : List (Entry Input Output) → Input → Output → Bool)
    (entry : Entry Input Output) (trace : List (Entry Input Output)) :
    prefixBad bad (entry :: trace) = (bad trace entry.input entry.answer || prefixBad bad trace) := rfl

theorem query_prefix_bound (bad : List (Entry Input Output) → Input → Output → Bool)
    (epsilon : Nat → ℝ≥0∞)
    (hbad : ∀ trace input, ((PMF.uniformOfFintype Output).map (bad trace input)) true ≤ epsilon trace.length)
    (table : Input → Option Output) (trace : List (Entry Input Output)) (input : Input) :
    ((Spec.RandomOracle.query table input).map
      (fun result => prefixBad bad (record table input result.1 trace))) true ≤
      indicator (prefixBad bad trace) + epsilon trace.length := by
  cases he : table input with
  | some old =>
    simp only [Spec.RandomOracle.query, record, he, PMF.pure_map, PMF.pure_apply]
    exact RandomOracleTrap.indicator_le_add _ _
  | none =>
    simp only [Spec.RandomOracle.query, record, he, PMF.map_comp, Function.comp_def, prefixBad_cons]
    have hu := RandomOracleCollision.boolean_or_mass (PMF.uniformOfFintype Output)
      (fun answer => bad trace input answer) (fun _ => prefixBad bad trace)
    refine hu.trans ?_
    rw [add_comm (indicator _) _]
    refine add_le_add (hbad trace input) ?_
    rw [RandomOracleTrap.map_const_true]

theorem sum_shift (f : Nat → ℝ≥0∞) (n fuel : Nat) :
    f n + ∑ i ∈ Finset.range fuel, f (n + 1 + i) = ∑ i ∈ Finset.range (fuel + 1), f (n + i) := by
  rw [Finset.sum_range_succ', Nat.add_zero, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

theorem run_prefix_bound (procedure : Spec.RandomOracleCollision.Procedure Input Output State)
    (bad : List (Entry Input Output) → Input → Output → Bool) (epsilon : Nat → ℝ≥0∞)
    (hbad : ∀ trace input, ((PMF.uniformOfFintype Output).map (bad trace input)) true ≤ epsilon trace.length)
    (fuel : Nat) (state : State) (table : Input → Option Output) (trace : List (Entry Input Output)) :
    ((run procedure fuel state table trace).map (fun out => prefixBad bad out.trace)) true ≤
      indicator (prefixBad bad trace) + ∑ i ∈ Finset.range fuel, epsilon (trace.length + i) := by
  induction fuel generalizing state table trace with
  | zero =>
    simp only [run, PMF.pure_map, PMF.pure_apply, Finset.range_zero, Finset.sum_empty, add_zero]
    exact RandomOracleTrap.ite_le_indicator _
  | succ fuel ih =>
    simp only [run, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      simp only [PMF.pure_map, PMF.pure_apply]
      exact RandomOracleTrap.indicator_le_add _ _
    | query input next =>
      simp only [PMF.map_bind]
      cases he : table input with
      | some old =>
        -- The trace is unchanged; one fuel unit is spent without a fresh entry.
        have hrec : record table input old trace = trace := by simp [record, he]
        simp only [Spec.RandomOracle.query, he, PMF.pure_bind, hrec]
        refine (ih (next old) table trace).trans ?_
        apply add_le_add le_rfl
        rw [Finset.sum_range_succ]
        exact le_self_add
      | none =>
        have h1 := RandomOracleTrap.bind_map_indicator_le (Spec.RandomOracle.query table input)
          (fun result => run procedure fuel (next result.1) result.2 (record table input result.1 trace))
          (fun out => prefixBad bad out.trace)
          (fun result => prefixBad bad (record table input result.1 trace))
          (∑ i ∈ Finset.range fuel, epsilon (trace.length + 1 + i))
          (fun result _ => by
            have hlen : (record table input result.1 trace).length = trace.length + 1 := by simp [record, he]
            have := ih (next result.1) result.2 (record table input result.1 trace)
            rwa [hlen] at this)
        rw [PMF.map_bind] at h1
        refine h1.trans ?_
        have h2 := query_prefix_bound bad epsilon hbad table trace input
        calc
          _ ≤ (indicator (prefixBad bad trace) + epsilon trace.length) +
              ∑ i ∈ Finset.range fuel, epsilon (trace.length + 1 + i) := add_le_add h2 le_rfl
          _ = _ := by
            rw [add_assoc, sum_shift]

/-- Prefix-dependent trap bound for the whole experiment. -/
theorem experiment_prefix_bound (procedure : Spec.RandomOracleCollision.Procedure Input Output State)
    (bad : List (Entry Input Output) → Input → Output → Bool) (epsilon : Nat → ℝ≥0∞)
    (hbad : ∀ trace input, ((PMF.uniformOfFintype Output).map (bad trace input)) true ≤ epsilon trace.length)
    (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map (fun out => prefixBad bad out.trace)) true ≤
      ∑ i ∈ Finset.range budget, epsilon i := by
  have h := run_prefix_bound procedure bad epsilon hbad budget initial (fun _ => none) []
  simpa only [experiment, prefixBad, RandomOracleTrap.indicator_false, zero_add, List.length_nil,
    Nat.zero_add] using h

theorem uniform_mem_mass (S : Finset Output) {inst : ∀ a, Decidable (a ∈ S)} :
    ((PMF.uniformOfFintype Output).map (fun answer => @decide (answer ∈ S) (inst answer))) true =
      (S.card : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  rw [RandomOracleTrap.map_true_eq, tsum_fintype]
  have hterm : ∀ a, (PMF.uniformOfFintype Output) a * indicator (@decide (a ∈ S) (inst a)) =
      if a ∈ S then (Fintype.card Output : ℝ≥0∞)⁻¹ else 0 := by
    intro a
    by_cases h : a ∈ S
    · rw [if_pos h, PMF.uniformOfFintype_apply, @decide_eq_true _ (inst a) h, RandomOracleTrap.indicator_true, mul_one]
    · rw [if_neg h, @decide_eq_false _ (inst a) h, RandomOracleTrap.indicator_false, mul_zero]
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 2
  exact congrArg Finset.card (by ext a; simp)

/-- A fresh uniform answer hits the mentions of n earlier inputs, each of
size at most m, with probability at most n*m/|Output|. -/
theorem mention_query_bound (mentions : Input → Finset Output) (m : Nat)
    (hm : ∀ input, (mentions input).card ≤ m) (log : List (Entry Input Output)) (input : Input) :
    ((PMF.uniformOfFintype Output).map (mentionBad mentions log input)) true ≤
      (log.length : ℝ≥0∞) * m * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  have h := ChallengeMixtures.boolean_union_bound (PMF.uniformOfFintype Output)
    (mentionBad mentions log input)
    (fun i : Fin log.length => fun answer => decide (answer ∈ mentions (log[i]).input)) (by
      intro answer _ hhit
      obtain ⟨entry, hmem, he⟩ := List.any_eq_true.mp hhit
      obtain ⟨index, hlt, hindex⟩ := List.mem_iff_getElem.mp hmem
      exact ⟨⟨index, hlt⟩, by simpa only [Fin.getElem_fin, hindex] using he⟩)
  refine h.trans ?_
  calc
    _ ≤ ∑ _i : Fin log.length, (m : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      rw [uniform_mem_mass]
      exact mul_le_mul_left (by exact_mod_cast hm (log[i]).input) _
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

theorem sum_range_mul (n m : Nat) (c : ℝ≥0∞) :
    ∑ i ∈ Finset.range n, (i : ℝ≥0∞) * m * c = (n.choose 2 : ℝ≥0∞) * m * c := by
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  congr 2
  rw [← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]

/-- Some fresh answer equals a value mentioned by an earlier fresh query
input with probability at most choose(budget,2)*m/|Output|. -/
theorem experiment_mention_bound (procedure : Spec.RandomOracleCollision.Procedure Input Output State)
    (mentions : Input → Finset Output) (m : Nat) (hm : ∀ input, (mentions input).card ≤ m)
    (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map (fun out => prefixBad (mentionBad mentions) out.trace)) true ≤
      (budget.choose 2 : ℝ≥0∞) * m * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  have h := experiment_prefix_bound procedure (mentionBad mentions)
    (fun n => (n : ℝ≥0∞) * m * (Fintype.card Output : ℝ≥0∞)⁻¹)
    (fun trace input => mention_query_bound mentions m hm trace input) budget initial
  rw [sum_range_mul] at h
  exact h

end
end SDitH.Proofs.RandomOracleMention
