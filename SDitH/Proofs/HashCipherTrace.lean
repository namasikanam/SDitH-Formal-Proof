import SDitH.Spec.HashCipherTrace
import SDitH.Proofs.HashCipher
import SDitH.Proofs.OracleChain

/-! Forgetting the log recovers the existing shared execution exactly. The
log satisfies the traced/ordered/fresh invariants, and both the table-
dependent and the prefix-dependent trap bounds hold for the instrumented
run and its mixture over the hidden cipher family. -/

namespace SDitH.Proofs.HashCipherTrace

open Spec.HashCipherTrace Spec.RandomOracleMention Spec.RandomOracleTrap Spec.OracleChain
open Spec.HashCipher (Procedure markHash)
open Spec.RandomOracleTrace (Entry record Traced Extends traceBad)
open scoped Classical ENNReal BigOperators
noncomputable section

variable {Input Digest Key Block State : Type*} [Fintype Digest] [Nonempty Digest]

omit [Fintype Digest] [Nonempty Digest] in
theorem forget_mark (hit : Bool) (out : Result Input Digest Key Block State) :
    forget (mark hit out) = markHash hit (forget out) := rfl

omit [Fintype Digest] [Nonempty Digest] in
theorem mark_trace (hit : Bool) (out : Result Input Digest Key Block State) : (mark hit out).trace = out.trace := rfl

omit [Fintype Digest] [Nonempty Digest] in
theorem mark_table (hit : Bool) (out : Result Input Digest Key Block State) : (mark hit out).hashTable = out.hashTable := rfl

/-- The instrumented execution projects exactly onto the shared execution. -/
theorem runFixed_forget (procedure : Procedure Input Digest Key Block State) (family : Spec.IdealCipher.Family Key Block)
    (fuel : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest)) :
    (runFixed procedure family fuel state table hashes ciphers log).map forget =
      Spec.HashCipher.runFixed procedure family fuel state table hashes ciphers := by
  induction fuel generalizing state table hashes ciphers log with
  | zero => simp [runFixed, Spec.HashCipher.runFixed, PMF.pure_map, forget]
  | succ fuel ih =>
    simp only [runFixed, Spec.HashCipher.runFixed, PMF.map_bind]
    congr 1
    funext action
    cases action with
    | stop => simp [PMF.pure_map, forget]
    | hash input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, forget_mark]
      congr 1
      funext result
      rw [← Function.comp_def (markHash _) forget, ← PMF.map_comp, ih]
    | cipher request next => exact ih _ _ _ _ _

theorem joint_forget (procedure : Procedure Input Digest Key Block State) [Fintype Key] [Fintype Block]
    (budget : Nat) (initial : State) :
    (jointExperiment procedure budget initial).map (fun joint => (joint.1, forget joint.2)) =
      Spec.HashCipher.jointExperiment procedure budget initial := by
  simp only [jointExperiment, Spec.HashCipher.jointExperiment, PMF.map_bind]
  congr 1
  funext family
  rw [PMF.map_comp, ← runFixed_forget, PMF.map_comp]
  rfl

/-- Invariants of the log through any continuation. -/
theorem run_invariants (procedure : Procedure Input Digest Key Block State) (family : Spec.IdealCipher.Family Key Block)
    (fuel : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support)
    (htraced : Traced table log) (hord : Ordered log) (hfresh : Fresh log)
    (hext : ∀ entry ∈ log, Extends entry.before table)
    (hstored : ∀ entry ∈ log, table entry.input = some entry.answer) :
    Traced out.hashTable out.trace ∧ Ordered out.trace ∧ Fresh out.trace ∧
      (∀ entry ∈ out.trace, Extends entry.before out.hashTable) ∧
      (∀ entry ∈ out.trace, out.hashTable entry.input = some entry.answer) ∧ Extends table out.hashTable := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact ⟨htraced, hord, hfresh, hext, hstored, RandomOracleTrace.extends_refl table⟩
  | succ fuel ih =>
    simp only [runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst out
      exact ⟨htraced, hord, hfresh, hext, hstored, RandomOracleTrace.extends_refl table⟩
    | hash input next =>
      obtain ⟨result, hr, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      have hq := RandomOracleTrace.query_traced table log input result htraced hr
      obtain ⟨h1, h2, h3, h4⟩ := OracleChain.query_ordered table log input result hr hord hfresh hext hstored
      have hgrow := RandomOracleTrace.query_extends table input result hr
      have hin := ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers (record table input result.1 log) inner hinner hq h1 h2 h3 h4
      simp only [mark_trace, mark_table]
      exact ⟨hin.1, hin.2.1, hin.2.2.1, hin.2.2.2.1, hin.2.2.2.2.1, RandomOracleTrace.extends_trans hgrow hin.2.2.2.2.2⟩
    | cipher request next =>
      exact ih _ table hashes _ log out hrest htraced hord hfresh hext hstored

theorem joint_invariants (procedure : Procedure Input Digest Key Block State) [Fintype Key] [Fintype Block]
    (budget : Nat) (initial : State) (joint : Spec.IdealCipher.Family Key Block × Result Input Digest Key Block State)
    (hout : joint ∈ (jointExperiment procedure budget initial).support) :
    Traced joint.2.hashTable joint.2.trace ∧ Ordered joint.2.trace ∧ Fresh joint.2.trace ∧
      (∀ entry ∈ joint.2.trace, Extends entry.before joint.2.hashTable) ∧
      ∀ entry ∈ joint.2.trace, joint.2.hashTable entry.input = some entry.answer := by
  obtain ⟨family, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨out, ho, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst heq
  have h := run_invariants procedure family budget initial (fun _ => none) [] [] [] out ho
    (by simp [Traced]) (by intro i j hi; simp at hi) (by simp [Fresh]) (by simp) (by simp)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Prefix-dependent trap bound on the instrumented shared execution. -/
theorem run_prefix_bound (procedure : Procedure Input Digest Key Block State) (family : Spec.IdealCipher.Family Key Block)
    (bad : List (Entry Input Digest) → Input → Digest → Bool) (epsilon : Nat → ℝ≥0∞)
    (hbad : ∀ log input, ((PMF.uniformOfFintype Digest).map (bad log input)) true ≤ epsilon log.length)
    (fuel : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest)) :
    ((runFixed procedure family fuel state table hashes ciphers log).map (fun out => prefixBad bad out.trace)) true ≤
      indicator (prefixBad bad log) + ∑ i ∈ Finset.range fuel, epsilon (log.length + i) := by
  induction fuel generalizing state table hashes ciphers log with
  | zero =>
    simp only [runFixed, PMF.pure_map, PMF.pure_apply, Finset.range_zero, Finset.sum_empty, add_zero]
    exact RandomOracleTrap.ite_le_indicator _
  | succ fuel ih =>
    simp only [runFixed, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      simp only [PMF.pure_map, PMF.pure_apply]
      exact RandomOracleTrap.indicator_le_add _ _
    | hash input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, mark_trace]
      cases he : table input with
      | some old =>
        have hrec : record table input old log = log := by simp [record, he]
        simp only [Spec.RandomOracle.query, he, PMF.pure_bind, hrec]
        refine (ih (next old) table ((input, old) :: hashes) ciphers log).trans ?_
        apply add_le_add le_rfl
        rw [Finset.sum_range_succ]
        exact le_self_add
      | none =>
        have h1 := RandomOracleTrap.bind_map_indicator_le (Spec.RandomOracle.query table input)
          (fun result => runFixed procedure family fuel (next result.1) result.2 ((input, result.1) :: hashes) ciphers
            (record table input result.1 log))
          (fun out => prefixBad bad out.trace)
          (fun result => prefixBad bad (record table input result.1 log))
          (∑ i ∈ Finset.range fuel, epsilon (log.length + 1 + i))
          (fun result _ => by
            have hlen : (record table input result.1 log).length = log.length + 1 := by simp [record, he]
            have := ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers (record table input result.1 log)
            rwa [hlen] at this)
        rw [PMF.map_bind] at h1
        refine h1.trans ?_
        have h2 := RandomOracleMention.query_prefix_bound bad epsilon hbad table log input
        calc
          _ ≤ (indicator (prefixBad bad log) + epsilon log.length) +
              ∑ i ∈ Finset.range fuel, epsilon (log.length + 1 + i) := add_le_add h2 le_rfl
          _ = _ := by rw [add_assoc, RandomOracleMention.sum_shift]
    | cipher request next =>
      refine (ih _ table hashes _ log).trans ?_
      apply add_le_add le_rfl
      rw [Finset.sum_range_succ]
      exact le_self_add

/-- Table-dependent trap bound on the instrumented shared execution. -/
theorem run_trace_bound (procedure : Procedure Input Digest Key Block State) (family : Spec.IdealCipher.Family Key Block)
    (bad : (Input → Option Digest) → Input → Digest → Bool) (epsilon : ℝ≥0∞)
    (hbad : ∀ table input, ((PMF.uniformOfFintype Digest).map (bad table input)) true ≤ epsilon)
    (fuel : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest)) :
    ((runFixed procedure family fuel state table hashes ciphers log).map (fun out => traceBad bad out.trace)) true ≤
      indicator (traceBad bad log) + fuel * epsilon := by
  induction fuel generalizing state table hashes ciphers log with
  | zero =>
    simp only [runFixed, PMF.pure_map, PMF.pure_apply, Nat.cast_zero, zero_mul, add_zero]
    exact RandomOracleTrap.ite_le_indicator _
  | succ fuel ih =>
    simp only [runFixed, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      simp only [PMF.pure_map, PMF.pure_apply]
      exact RandomOracleTrap.indicator_le_add _ _
    | hash input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, mark_trace]
      have h1 := RandomOracleTrap.bind_map_indicator_le (Spec.RandomOracle.query table input)
        (fun result => runFixed procedure family fuel (next result.1) result.2 ((input, result.1) :: hashes) ciphers
          (record table input result.1 log))
        (fun out => traceBad bad out.trace)
        (fun result => traceBad bad (record table input result.1 log)) (fuel * epsilon)
        (fun result _ => ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers (record table input result.1 log))
      rw [PMF.map_bind] at h1
      refine h1.trans ?_
      have h2 := RandomOracleTrace.query_trace_bound bad epsilon hbad table log input
      calc
        _ ≤ (indicator (traceBad bad log) + epsilon) + fuel * epsilon := add_le_add h2 le_rfl
        _ = _ := by
          push_cast
          ring
    | cipher request next =>
      refine (ih _ table hashes _ log).trans ?_
      apply add_le_add le_rfl
      push_cast
      exact mul_le_mul_left (by simp) _

variable [Fintype Key] [Fintype Block]

theorem joint_prefix_bound (procedure : Procedure Input Digest Key Block State)
    (bad : List (Entry Input Digest) → Input → Digest → Bool) (epsilon : Nat → ℝ≥0∞)
    (hbad : ∀ log input, ((PMF.uniformOfFintype Digest).map (bad log input)) true ≤ epsilon log.length)
    (budget : Nat) (initial : State) :
    ((jointExperiment procedure budget initial).map (fun joint => prefixBad bad joint.2.trace)) true ≤
      ∑ i ∈ Finset.range budget, epsilon i := by
  simp only [jointExperiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply ChallengeMixtures.bind_true_le
  intro family _
  have h := run_prefix_bound procedure family bad epsilon hbad budget initial (fun _ => none) [] [] []
  simpa only [prefixBad, RandomOracleTrap.indicator_false, zero_add, List.length_nil, Nat.zero_add] using h

theorem joint_trace_bound (procedure : Procedure Input Digest Key Block State)
    (bad : (Input → Option Digest) → Input → Digest → Bool) (epsilon : ℝ≥0∞)
    (hbad : ∀ table input, ((PMF.uniformOfFintype Digest).map (bad table input)) true ≤ epsilon)
    (budget : Nat) (initial : State) :
    ((jointExperiment procedure budget initial).map (fun joint => traceBad bad joint.2.trace)) true ≤
      budget * epsilon := by
  simp only [jointExperiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply ChallengeMixtures.bind_true_le
  intro family _
  have h := run_trace_bound procedure family bad epsilon hbad budget initial (fun _ => none) [] [] []
  simpa only [traceBad, List.any_nil, RandomOracleTrap.indicator_false, zero_add] using h

end
end SDitH.Proofs.HashCipherTrace
