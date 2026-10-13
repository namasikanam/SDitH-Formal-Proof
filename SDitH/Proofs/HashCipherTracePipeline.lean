import SDitH.Spec.HashCipherTracePipeline
import SDitH.Proofs.HashCipherTrace
import SDitH.Proofs.HashCipherPipeline

/-! The traced two-phase execution projects exactly onto the existing one,
keeps the log invariants, has at most q+k fresh entries, and satisfies the
table-dependent trap bound (q+k)*epsilon and the prefix-dependent bound
summed over q+k positions for monotone epsilon. -/

namespace SDitH.Proofs.HashCipherTracePipeline

open Spec.HashCipherTracePipeline Spec.RandomOracleMention Spec.RandomOracleTrap
open Spec.HashCipherTrace (forget mark)
open Spec.OracleChain
open Spec.HashCipher (Procedure markHash)
open Spec.RandomOracleTrace (Entry record Traced Extends traceBad)
open scoped Classical ENNReal BigOperators
noncomputable section

variable {Input Digest Key Block A B : Type*} [Fintype Digest] [Nonempty Digest]

theorem runFixed_forget (first : Procedure Input Digest Key Block A) (second : Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) (family : Spec.IdealCipher.Family Key Block) (q : Nat) (state : A)
    (table : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Entry Input Digest)) :
    (runFixed first second k next family q state table hashes ciphers log).map forget =
      Spec.HashCipherPipeline.runFixed first second k next family q state table hashes ciphers := by
  simp only [runFixed, Spec.HashCipherPipeline.runFixed, PMF.map_bind]
  have hinner : ∀ start : Spec.HashCipherTrace.Result Input Digest Key Block A,
      ((Spec.HashCipherTrace.runFixed second family k (next start.state) start.hashTable start.hashHistory
        start.cipherHistory start.trace).map (mark start.hashCollided)).map forget =
      (Spec.HashCipher.runFixed second family k (next start.state) start.hashTable start.hashHistory
        start.cipherHistory).map (markHash start.hashCollided) := by
    intro start
    rw [PMF.map_comp, show forget ∘ mark start.hashCollided = markHash start.hashCollided ∘ forget from rfl,
      ← PMF.map_comp, HashCipherTrace.runFixed_forget]
  simp only [hinner]
  rw [← HashCipherTrace.runFixed_forget first family q state table hashes ciphers log, PMF.bind_map]
  rfl

theorem run_invariants (first : Procedure Input Digest Key Block A) (second : Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) (family : Spec.IdealCipher.Family Key Block) (q : Nat) (state : A)
    (table : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Entry Input Digest)) (out : Spec.HashCipherTrace.Result Input Digest Key Block B)
    (hout : out ∈ (runFixed first second k next family q state table hashes ciphers log).support)
    (htraced : Traced table log) (hord : Ordered log) (hfresh : Fresh log)
    (hext : ∀ entry ∈ log, Extends entry.before table)
    (hstored : ∀ entry ∈ log, table entry.input = some entry.answer) :
    Traced out.hashTable out.trace ∧ Ordered out.trace ∧ Fresh out.trace ∧
      (∀ entry ∈ out.trace, Extends entry.before out.hashTable) ∧
      (∀ entry ∈ out.trace, out.hashTable entry.input = some entry.answer) ∧ Extends table out.hashTable := by
  obtain ⟨start, hstart, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨tail, htail, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst heq
  have h1 := HashCipherTrace.run_invariants first family q state table hashes ciphers log start hstart
    htraced hord hfresh hext hstored
  have h2 := HashCipherTrace.run_invariants second family k (next start.state) start.hashTable start.hashHistory
    start.cipherHistory start.trace tail htail h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2.1
  simp only [HashCipherTrace.mark_trace, HashCipherTrace.mark_table]
  exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1,
    RandomOracleTrace.extends_trans h1.2.2.2.2.2 h2.2.2.2.2.2⟩

/-- A fresh entry needs a hash query, so the log grows by at most the fuel. -/
theorem run_trace_length (procedure : Procedure Input Digest Key Block A) (family : Spec.IdealCipher.Family Key Block)
    (fuel : Nat) (state : A) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Spec.HashCipherTrace.Result Input Digest Key Block A)
    (hout : out ∈ (Spec.HashCipherTrace.runFixed procedure family fuel state table hashes ciphers log).support) :
    out.trace.length ≤ log.length + fuel := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [Spec.HashCipherTrace.runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    simp
  | succ fuel ih =>
    simp only [Spec.HashCipherTrace.runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst out
      simp
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      have h := ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers (record table input result.1 log) inner hinner
      have hrec : (record table input result.1 log).length ≤ log.length + 1 := by
        unfold record
        cases table input <;> simp
      simp only [HashCipherTrace.mark_trace]
      omega
    | cipher request next =>
      have h := ih _ table hashes _ log out hrest
      omega

theorem run_trace_bound (first : Procedure Input Digest Key Block A) (second : Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) (family : Spec.IdealCipher.Family Key Block)
    (bad : (Input → Option Digest) → Input → Digest → Bool) (epsilon : ℝ≥0∞)
    (hbad : ∀ table input, ((PMF.uniformOfFintype Digest).map (bad table input)) true ≤ epsilon)
    (q : Nat) (state : A) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest)) :
    ((runFixed first second k next family q state table hashes ciphers log).map
      (fun out => traceBad bad out.trace)) true ≤ indicator (traceBad bad log) + (q + k) * epsilon := by
  simp only [runFixed]
  have h := RandomOracleTrap.bind_map_indicator_le
    (Spec.HashCipherTrace.runFixed first family q state table hashes ciphers log)
    (fun start => (Spec.HashCipherTrace.runFixed second family k (next start.state) start.hashTable start.hashHistory
      start.cipherHistory start.trace).map (mark start.hashCollided))
    (fun out => traceBad bad out.trace) (fun start => traceBad bad start.trace) (k * epsilon) (by
      intro start _
      rw [PMF.map_comp]
      simp only [Function.comp_def, HashCipherTrace.mark_trace]
      exact HashCipherTrace.run_trace_bound second family bad epsilon hbad k _ _ _ _ _)
  refine h.trans ?_
  have h1 := HashCipherTrace.run_trace_bound first family bad epsilon hbad q state table hashes ciphers log
  calc
    _ ≤ (indicator (traceBad bad log) + q * epsilon) + k * epsilon := add_le_add h1 le_rfl
    _ = _ := by
      rw [add_assoc, ← add_mul]

theorem run_prefix_bound (first : Procedure Input Digest Key Block A) (second : Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) (family : Spec.IdealCipher.Family Key Block)
    (bad : List (Entry Input Digest) → Input → Digest → Bool) (epsilon : Nat → ℝ≥0∞) (hmono : Monotone epsilon)
    (hbad : ∀ log input, ((PMF.uniformOfFintype Digest).map (bad log input)) true ≤ epsilon log.length)
    (q : Nat) (state : A) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest)) :
    ((runFixed first second k next family q state table hashes ciphers log).map
      (fun out => prefixBad bad out.trace)) true ≤
      indicator (prefixBad bad log) + ∑ i ∈ Finset.range (q + k), epsilon (log.length + i) := by
  simp only [runFixed]
  have h := RandomOracleTrap.bind_map_indicator_le
    (Spec.HashCipherTrace.runFixed first family q state table hashes ciphers log)
    (fun start => (Spec.HashCipherTrace.runFixed second family k (next start.state) start.hashTable start.hashHistory
      start.cipherHistory start.trace).map (mark start.hashCollided))
    (fun out => prefixBad bad out.trace) (fun start => prefixBad bad start.trace)
    (∑ i ∈ Finset.range k, epsilon (log.length + q + i)) (by
      intro start hstart
      rw [PMF.map_comp]
      simp only [Function.comp_def, HashCipherTrace.mark_trace]
      refine (HashCipherTrace.run_prefix_bound second family bad epsilon hbad k _ _ _ _ _).trans ?_
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      apply hmono
      have := run_trace_length first family q state table hashes ciphers log start hstart
      omega)
  refine h.trans ?_
  have h1 := HashCipherTrace.run_prefix_bound first family bad epsilon hbad q state table hashes ciphers log
  calc
    _ ≤ (indicator (prefixBad bad log) + ∑ i ∈ Finset.range q, epsilon (log.length + i)) +
        ∑ i ∈ Finset.range k, epsilon (log.length + q + i) := add_le_add h1 le_rfl
    _ = _ := by
      rw [add_assoc, Finset.sum_range_add]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega

variable [Fintype Key] [Fintype Block]

theorem joint_forget (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B) :
    (jointExperiment first q initial second k next).map (fun joint => (joint.1, forget joint.2)) =
      Spec.HashCipherPipeline.jointExperiment first q initial second k next := by
  simp only [jointExperiment, Spec.HashCipherPipeline.jointExperiment, PMF.map_bind]
  congr 1
  funext family
  rw [PMF.map_comp, ← runFixed_forget, PMF.map_comp]
  rfl

theorem joint_invariants (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (joint : Spec.IdealCipher.Family Key Block × Spec.HashCipherTrace.Result Input Digest Key Block B)
    (hout : joint ∈ (jointExperiment first q initial second k next).support) :
    Traced joint.2.hashTable joint.2.trace ∧ Ordered joint.2.trace ∧ Fresh joint.2.trace ∧
      (∀ entry ∈ joint.2.trace, Extends entry.before joint.2.hashTable) ∧
      ∀ entry ∈ joint.2.trace, joint.2.hashTable entry.input = some entry.answer := by
  obtain ⟨family, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨out, ho, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst heq
  have h := run_invariants first second k next family q initial (fun _ => none) [] [] [] out ho
    (by simp [Traced]) (by intro i j hi; simp at hi) (by simp [Fresh]) (by simp) (by simp)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem joint_trace_bound_family (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (bad : Spec.IdealCipher.Family Key Block → (Input → Option Digest) → Input → Digest → Bool) (epsilon : ℝ≥0∞)
    (hbad : ∀ family table input, ((PMF.uniformOfFintype Digest).map (bad family table input)) true ≤ epsilon) :
    ((jointExperiment first q initial second k next).map (fun joint => traceBad (bad joint.1) joint.2.trace)) true ≤
      (q + k) * epsilon := by
  simp only [jointExperiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply ChallengeMixtures.bind_true_le
  intro family _
  have h := run_trace_bound first second k next family (bad family) epsilon (hbad family) q initial (fun _ => none) [] [] []
  simpa only [traceBad, List.any_nil, RandomOracleTrap.indicator_false, zero_add] using h

theorem joint_prefix_bound (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (bad : List (Entry Input Digest) → Input → Digest → Bool) (epsilon : Nat → ℝ≥0∞) (hmono : Monotone epsilon)
    (hbad : ∀ log input, ((PMF.uniformOfFintype Digest).map (bad log input)) true ≤ epsilon log.length) :
    ((jointExperiment first q initial second k next).map (fun joint => prefixBad bad joint.2.trace)) true ≤
      ∑ i ∈ Finset.range (q + k), epsilon i := by
  simp only [jointExperiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply ChallengeMixtures.bind_true_le
  intro family _
  have h := run_prefix_bound first second k next family bad epsilon hmono hbad q initial (fun _ => none) [] [] []
  simpa only [prefixBad, RandomOracleTrap.indicator_false, zero_add, List.length_nil, Nat.zero_add] using h

end
end SDitH.Proofs.HashCipherTracePipeline
