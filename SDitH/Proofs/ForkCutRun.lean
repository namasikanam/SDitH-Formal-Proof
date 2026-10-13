import SDitH.Proofs.ForkCut
import SDitH.Proofs.HashCipherTrace
import SDitH.Proofs.ProductOracle

/-! The cut property along a branch, and the fixed-target event. Running
the shared traced interpreter from a table extending the fork table
preserves the cut: every fresh entry made after the fork has an earlier
table extending the fork table. A value stored after the fork whose digest
equals a fixed target raises a trace event whose per-query probability is
the inverse digest count, so the fixed-target event over a run is bounded
by the budget times that inverse; the initial log, being entirely
pre-fork, contributes nothing. This charges the lines string's absence
from the fork table in a branch. -/

namespace SDitH.Proofs.ForkCutRun

open Spec.RandomOracleTrace Spec.HashCipherTrace Spec.OracleChain
open ForkCut (Cut)
open scoped Classical ENNReal
noncomputable section

variable {Input D M Key Block State : Type*} [Fintype D] [Fintype M] [Nonempty D] [Nonempty M]

/-- All entries are pre-cut: stored by the fork table and older than it. -/
def PreCut (P : Input → Option (D × M)) (log : List (Entry Input (D × M))) : Prop :=
  ∀ entry ∈ log, Extends entry.before P ∧ P entry.input = some entry.answer

omit [Fintype D] [Fintype M] [Nonempty D] [Nonempty M] in
theorem cut_of_preCut (P : Input → Option (D × M)) (log : List (Entry Input (D × M))) (h : PreCut P log) : Cut P log :=
  fun entry hentry => Or.inr (h entry hentry)

omit [Fintype D] [Fintype M] [Nonempty D] [Nonempty M] in
theorem cut_record (P table : Input → Option (D × M)) (log : List (Entry Input (D × M))) (hcut : Cut P log)
    (hext : Extends P table) (input : Input) (answer : D × M) : Cut P (record table input answer log) := by
  unfold record
  cases table input with
  | some _ => exact hcut
  | none =>
    intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | hmem
    · exact Or.inl hext
    · exact hcut entry hmem

/-- A run from a table extending the fork table preserves the cut and the extension. -/
theorem run_cut (procedure : Spec.HashCipher.Procedure Input (D × M) Key Block State) (family : Spec.IdealCipher.Family Key Block)
    (P : Input → Option (D × M)) (fuel : Nat) (state : State) (table : Input → Option (D × M))
    (hashes : List (Input × (D × M))) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Entry Input (D × M))) (out : Result Input (D × M) Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support)
    (hcut : Cut P log) (hext : Extends P table) : Cut P out.trace ∧ Extends P out.hashTable := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact ⟨hcut, hext⟩
  | succ fuel ih =>
    simp only [runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst out
      exact ⟨hcut, hext⟩
    | hash input next =>
      obtain ⟨result, hr, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      have hgrow := RandomOracleTrace.query_extends table input result hr
      have hin := ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers (record table input result.1 log)
        inner hinner (cut_record P table log hcut hext input result.1) (RandomOracleTrace.extends_trans hext hgrow)
      simpa only [HashCipherTrace.mark_trace, HashCipherTrace.mark_table] using hin
    | cipher request next =>
      exact ih _ table hashes _ log out hrest hcut hext

/-- A fresh post-fork answer whose digest equals the target. -/
def targetBad (P : Input → Option (D × M)) (target : D) (before : Input → Option (D × M)) (_input : Input)
    (answer : D × M) : Bool :=
  decide (Extends P before ∧ answer.1 = target)

theorem map_true_mono {A : Type*} (p : PMF A) (h1 h2 : A → Bool) (himp : ∀ a, h1 a = true → h2 a = true) :
    (p.map h1) true ≤ (p.map h2) true := by
  rw [RandomOracleTrap.map_true_eq, RandomOracleTrap.map_true_eq]
  refine ENNReal.tsum_le_tsum fun a => ?_
  refine mul_le_mul_right (?_ : Spec.RandomOracleTrap.indicator (h1 a) ≤ Spec.RandomOracleTrap.indicator (h2 a)) _
  cases hb : h1 a
  · simp [Spec.RandomOracleTrap.indicator]
  · rw [himp a hb]

theorem target_query_le (P : Input → Option (D × M)) (target : D) (before : Input → Option (D × M)) (input : Input) :
    ((PMF.uniformOfFintype (D × M)).map (targetBad P target before input)) true ≤ (Fintype.card D : ℝ≥0∞)⁻¹ := by
  have h := map_true_mono (PMF.uniformOfFintype (D × M)) (targetBad P target before input)
    (fun answer => decide (answer.1 ∈ ({target} : Finset D))) (by
      intro answer ha
      simp only [targetBad, decide_eq_true_eq] at ha
      simp [ha.2])
  refine h.trans (le_of_eq ?_)
  rw [ProductOracle.uniform_fst_mem_mass]
  simp

/-- The fixed-target event over a run: the initial log's contribution plus
the budget times the inverse digest count. -/
theorem run_target_bound (procedure : Spec.HashCipher.Procedure Input (D × M) Key Block State) (family : Spec.IdealCipher.Family Key Block)
    (P : Input → Option (D × M)) (target : D) (fuel : Nat) (state : State) (table : Input → Option (D × M))
    (hashes : List (Input × (D × M))) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Entry Input (D × M))) :
    ((runFixed procedure family fuel state table hashes ciphers log).map
      (fun out => traceBad (targetBad P target) out.trace)) true ≤
      Spec.RandomOracleTrap.indicator (traceBad (targetBad P target) log) + fuel * (Fintype.card D : ℝ≥0∞)⁻¹ :=
  HashCipherTrace.run_trace_bound procedure family (targetBad P target) _ (fun before input => target_query_le P target before input)
    fuel state table hashes ciphers log

omit [Fintype D] [Fintype M] [Nonempty D] [Nonempty M] in
/-- A pre-cut fresh log raises no fixed-target event. -/
theorem traceBad_target_preCut (P : Input → Option (D × M)) (target : D) (log : List (Entry Input (D × M)))
    (hpre : PreCut P log) (hfresh : Fresh log) : traceBad (targetBad P target) log = false := by
  simp only [traceBad, List.any_eq_false, targetBad, decide_eq_true_eq, not_and]
  intro entry hentry hext
  exfalso
  have hstored := (hpre entry hentry).2
  have hnone := hfresh entry hentry
  have h := hext entry.input entry.answer hstored
  rw [hnone] at h
  cases h

omit [Fintype D] [Fintype M] [Nonempty D] [Nonempty M] in
/-- A value stored after the fork whose digest is the target raises the event. -/
theorem stored_target_implies_trace (P table : Input → Option (D × M)) (log : List (Entry Input (D × M)))
    (hcut : Cut P log) (htraced : Traced table log) (target : D) (x : Input) (y : D × M)
    (hstored : table x = some y) (hmissing : P x = none) (htarget : y.1 = target) :
    traceBad (targetBad P target) log = true := by
  obtain ⟨entry, hentry, hinput, hanswer, _, _⟩ := htraced.1 x y hstored
  simp only [traceBad, List.any_eq_true]
  refine ⟨entry, hentry, ?_⟩
  simp only [targetBad, decide_eq_true_eq]
  rcases hcut entry hentry with hpost | ⟨_, hpre⟩
  · exact ⟨hpost, by rw [hanswer, htarget]⟩
  · rw [hinput, hmissing] at hpre
    cases hpre

omit [Fintype D] [Fintype M] [Nonempty D] [Nonempty M] in
/-- A stored value with the target digest: present in the fork table, or the event. -/
theorem present_or_target (P table : Input → Option (D × M)) (log : List (Entry Input (D × M)))
    (hcut : Cut P log) (htraced : Traced table log) (target : D) (x : Input) (y : D × M)
    (hstored : table x = some y) (htarget : y.1 = target) :
    (P x).isSome ∨ traceBad (targetBad P target) log = true := by
  cases hP : P x with
  | some _ => exact Or.inl rfl
  | none => exact Or.inr (stored_target_implies_trace P table log hcut htraced target x y hstored hP htarget)

end
end SDitH.Proofs.ForkCutRun
