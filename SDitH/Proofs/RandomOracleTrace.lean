import SDitH.Spec.RandomOracleTrace
import SDitH.Proofs.RandomOracleTrap

/-! Trap bound for predicates depending on the table before a fresh query,
and the trace/table invariants: fresh entries correspond exactly to stored
values, earlier tables are extended by later ones, and no stored value is
changed. The bound is budget*epsilon as for fixed predicates. -/

namespace SDitH.Proofs.RandomOracleTrace

open Spec.RandomOracleTrace Spec.RandomOracleTrap
open scoped Classical ENNReal
noncomputable section

variable {Input Output State : Type*} [Fintype Output] [Nonempty Output]

omit [Fintype Output] [Nonempty Output] in
theorem traceBad_cons (bad : (Input → Option Output) → Input → Output → Bool)
    (entry : Entry Input Output) (trace : List (Entry Input Output)) :
    traceBad bad (entry :: trace) = (bad entry.before entry.input entry.answer || traceBad bad trace) := by
  simp [traceBad, List.any_cons]

theorem query_trace_bound (bad : (Input → Option Output) → Input → Output → Bool) (epsilon : ℝ≥0∞)
    (hbad : ∀ table input, ((PMF.uniformOfFintype Output).map (bad table input)) true ≤ epsilon)
    (table : Input → Option Output) (trace : List (Entry Input Output)) (input : Input) :
    ((Spec.RandomOracle.query table input).map
      (fun result => traceBad bad (record table input result.1 trace))) true ≤
      indicator (traceBad bad trace) + epsilon := by
  cases he : table input with
  | some old =>
    simp only [Spec.RandomOracle.query, record, he, PMF.pure_map, PMF.pure_apply]
    exact RandomOracleTrap.indicator_le_add _ _
  | none =>
    simp only [Spec.RandomOracle.query, record, he, PMF.map_comp, Function.comp_def, traceBad_cons]
    have hu := RandomOracleCollision.boolean_or_mass (PMF.uniformOfFintype Output)
      (fun answer => bad table input answer) (fun _ => traceBad bad trace)
    refine hu.trans ?_
    rw [add_comm (indicator _) epsilon]
    refine add_le_add (hbad table input) ?_
    rw [RandomOracleTrap.map_const_true]

theorem run_trace_bound (procedure : Spec.RandomOracleCollision.Procedure Input Output State)
    (bad : (Input → Option Output) → Input → Output → Bool) (epsilon : ℝ≥0∞)
    (hbad : ∀ table input, ((PMF.uniformOfFintype Output).map (bad table input)) true ≤ epsilon)
    (fuel : Nat) (state : State) (table : Input → Option Output) (trace : List (Entry Input Output)) :
    ((run procedure fuel state table trace).map (fun out => traceBad bad out.trace)) true ≤
      indicator (traceBad bad trace) + fuel * epsilon := by
  induction fuel generalizing state table trace with
  | zero =>
    simp only [run, PMF.pure_map, PMF.pure_apply, Nat.cast_zero, zero_mul, add_zero]
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
      have h1 := RandomOracleTrap.bind_map_indicator_le (Spec.RandomOracle.query table input)
        (fun result => run procedure fuel (next result.1) result.2 (record table input result.1 trace))
        (fun out => traceBad bad out.trace)
        (fun result => traceBad bad (record table input result.1 trace)) (fuel * epsilon)
        (fun result _ => ih (next result.1) result.2 (record table input result.1 trace))
      rw [PMF.map_bind] at h1
      refine h1.trans ?_
      have h2 := query_trace_bound bad epsilon hbad table trace input
      calc
        _ ≤ (indicator (traceBad bad trace) + epsilon) + fuel * epsilon := add_le_add h2 le_rfl
        _ = _ := by
          push_cast
          ring

/-- The table-dependent trap bound. -/
theorem experiment_trace_bound (procedure : Spec.RandomOracleCollision.Procedure Input Output State)
    (bad : (Input → Option Output) → Input → Output → Bool) (epsilon : ℝ≥0∞)
    (hbad : ∀ table input, ((PMF.uniformOfFintype Output).map (bad table input)) true ≤ epsilon)
    (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map (fun out => traceBad bad out.trace)) true ≤ budget * epsilon := by
  have h := run_trace_bound procedure bad epsilon hbad budget initial (fun _ => none) []
  simpa only [experiment, traceBad, List.any_nil, RandomOracleTrap.indicator_false, zero_add] using h

omit [Fintype Output] [Nonempty Output] in
theorem extends_refl (table : Input → Option Output) : Extends table table := fun _ _ h => h

omit [Fintype Output] [Nonempty Output] in
theorem extends_trans {a b c : Input → Option Output} (hab : Extends a b) (hbc : Extends b c) : Extends a c :=
  fun input answer h => hbc input answer (hab input answer h)

omit [Fintype Output] [Nonempty Output] in
theorem extends_update (table : Input → Option Output) (input : Input) (answer : Output) (he : table input = none) :
    Extends table (Function.update table input (some answer)) := by
  intro q a hq
  by_cases hqi : q = input
  · subst hqi
    rw [he] at hq
    cases hq
  · rw [Function.update_of_ne hqi]
    exact hq

theorem query_extends (table : Input → Option Output) (input : Input) (result : Output × (Input → Option Output))
    (hr : result ∈ (Spec.RandomOracle.query table input).support) : Extends table result.2 := by
  unfold Spec.RandomOracle.query at hr
  cases he : table input with
  | some old =>
    rw [he, PMF.mem_support_pure_iff] at hr
    subst result
    exact extends_refl table
  | none =>
    rw [he] at hr
    obtain ⟨fresh, _, hresult⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst result
    exact extends_update table input fresh he

theorem query_traced (table : Input → Option Output) (trace : List (Entry Input Output))
    (input : Input) (result : Output × (Input → Option Output))
    (htraced : Traced table trace) (hr : result ∈ (Spec.RandomOracle.query table input).support) :
    Traced result.2 (record table input result.1 trace) := by
  have hext := query_extends table input result hr
  unfold Spec.RandomOracle.query at hr
  cases he : table input with
  | some old =>
    rw [he, PMF.mem_support_pure_iff] at hr
    subst result
    simpa only [record, he] using htraced
  | none =>
    rw [he] at hr
    obtain ⟨fresh, _, hresult⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst result
    simp only [record, he]
    constructor
    · intro q answer hq
      by_cases hqi : q = input
      · subst hqi
        have ha : fresh = answer := by simpa using hq
        exact ⟨⟨table, q, fresh⟩, List.mem_cons_self, rfl, ha, he, hext⟩
      · rw [Function.update_of_ne hqi] at hq
        obtain ⟨entry, hmem, hin, han, hnone, hextends⟩ := htraced.1 q answer hq
        exact ⟨entry, List.mem_cons_of_mem _ hmem, hin, han, hnone, extends_trans hextends hext⟩
    · intro entry hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp
      · exact hext entry.input entry.answer (htraced.2 entry hmem)

/-- Trace/table correspondence and monotone growth through any continuation. -/
theorem run_invariants (procedure : Spec.RandomOracleCollision.Procedure Input Output State) (fuel : Nat)
    (state : State) (table : Input → Option Output) (trace : List (Entry Input Output))
    (out : Result Input Output State) (hout : out ∈ (run procedure fuel state table trace).support)
    (htraced : Traced table trace) : Traced out.table out.trace ∧ Extends table out.table := by
  induction fuel generalizing state table trace out with
  | zero =>
    simp only [run, PMF.mem_support_pure_iff] at hout
    subst out
    exact ⟨htraced, extends_refl table⟩
  | succ fuel ih =>
    simp only [run] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst out
      exact ⟨htraced, extends_refl table⟩
    | query input next =>
      obtain ⟨result, hr, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      have hnext := ih (next result.1) result.2 (record table input result.1 trace) out hrun
        (query_traced table trace input result htraced hr)
      exact ⟨hnext.1, extends_trans (query_extends table input result hr) hnext.2⟩

theorem experiment_invariants (procedure : Spec.RandomOracleCollision.Procedure Input Output State) (budget : Nat) (initial : State)
    (out : Result Input Output State) (hout : out ∈ (experiment procedure budget initial).support) :
    Traced out.table out.trace :=
  (run_invariants procedure budget initial (fun _ => none) [] out hout (by simp [Traced])).1

/-- A stored trapped value whose trap already held at its fresh query time
raises the trace event. The table at that time is extended by the final one. -/
theorem stored_trap_implies_trace (procedure : Spec.RandomOracleCollision.Procedure Input Output State) (budget : Nat) (initial : State)
    (bad : (Input → Option Output) → Input → Output → Bool) (out : Result Input Output State)
    (hout : out ∈ (experiment procedure budget initial).support) (input : Input) (answer : Output)
    (hstored : out.table input = some answer)
    (hbad : ∀ before, before input = none → Extends before out.table → bad before input answer = true) :
    traceBad bad out.trace = true := by
  obtain ⟨entry, hmem, hin, han, hnone, hext⟩ := (experiment_invariants procedure budget initial out hout).1 input answer hstored
  refine List.any_eq_true.mpr ⟨entry, hmem, ?_⟩
  rw [hin, han]
  exact hbad entry.before hnone hext

end
end SDitH.Proofs.RandomOracleTrace
