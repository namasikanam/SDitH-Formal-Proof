import SDitH.Spec.RandomOracleTrap
import SDitH.Proofs.RandomOracleCollisionInvariant
import SDitH.Proofs.ConsistencyMatrix

/-! Adaptive trap bound: if every fresh uniform answer satisfies a fixed
query-indexed predicate with probability at most epsilon, then some recorded
query/answer pair satisfies it with probability at most budget*epsilon.
Repeated queries reuse a recorded pair and cannot create a new hit. The
kernel instantiation gives budget*|F|^(-s) for the consistency mask. -/

namespace SDitH.Proofs.RandomOracleTrap

open Spec.RandomOracleCollision Spec.RandomOracleTrap
open scoped Classical ENNReal
noncomputable section

variable {Input Output State : Type*} [Fintype Output] [Nonempty Output]

theorem indicator_true : indicator true = 1 := rfl

theorem indicator_false : indicator false = 0 := rfl

theorem map_true_eq {A : Type*} (p : PMF A) (h : A → Bool) :
    (p.map h) true = ∑' a, p a * indicator (h a) := by
  rw [PMF.map_apply]
  congr 1
  funext a
  cases hb : h a <;> simp [indicator]

theorem bind_map_indicator_le {A B : Type*} (p : PMF A) (f : A → PMF B) (g : B → Bool) (h : A → Bool)
    (c : ℝ≥0∞) (hb : ∀ a ∈ p.support, ((f a).map g) true ≤ indicator (h a) + c) :
    ((p.bind f).map g) true ≤ (p.map h) true + c := by
  rw [PMF.map_bind, PMF.bind_apply, map_true_eq]
  calc
    (∑' a, p a * ((f a).map g) true) ≤ ∑' a, p a * (indicator (h a) + c) := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : a ∈ p.support
      · exact mul_le_mul_right (hb a ha) _
      · rw [show p a = 0 from by simpa [PMF.mem_support_iff] using ha]
        simp
    _ = ∑' a, p a * indicator (h a) + ∑' a, p a * c := by
      rw [← ENNReal.tsum_add]
      congr 1
      funext a
      ring
    _ = (∑' a, p a * indicator (h a)) + c := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Fintype Output] [Nonempty Output] in
theorem historyBad_cons (bad : Input → Output → Bool) (input : Input) (answer : Output)
    (history : List (Input × Output)) :
    historyBad bad ((input, answer) :: history) = (bad input answer || historyBad bad history) := by
  simp [historyBad, List.any_cons]

theorem ite_le_indicator (b : Bool) {inst : Decidable (true = b)} :
    (@ite ℝ≥0∞ (true = b) inst 1 0) ≤ indicator b := by
  by_cases hb : true = b
  · rw [if_pos hb, ← hb]
    exact le_rfl
  · rw [if_neg hb]
    exact zero_le _

theorem indicator_le_add (b : Bool) {inst : Decidable (true = b)} (epsilon : ℝ≥0∞) :
    (@ite ℝ≥0∞ (true = b) inst 1 0) ≤ indicator b + epsilon :=
  (ite_le_indicator b).trans le_self_add

theorem map_const_true {A : Type*} (p : PMF A) (c : Bool) : (p.map (fun _ => c)) true = indicator c := by
  rw [map_true_eq, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- One query extends the trap event by at most epsilon. A repeated query
returns a recorded pair, so it cannot raise the event. -/
theorem query_trap_bound (bad : Input → Output → Bool) (epsilon : ℝ≥0∞)
    (hbad : ∀ input, ((PMF.uniformOfFintype Output).map (bad input)) true ≤ epsilon)
    (table : Input → Option Output) (history : List (Input × Output))
    (hrecorded : Recorded table history) (input : Input) :
    ((Spec.RandomOracle.query table input).map
      (fun result => historyBad bad ((input, result.1) :: history))) true ≤
      indicator (historyBad bad history) + epsilon := by
  cases he : table input with
  | some old =>
    have hmem : (input, old) ∈ history := (hrecorded input old).mp he
    have hcons : historyBad bad ((input, old) :: history) = historyBad bad history := by
      rw [historyBad_cons]
      cases hb : bad input old
      · simp
      · simp only [Bool.true_or]
        exact (List.any_eq_true.mpr ⟨(input, old), hmem, hb⟩).symm
    simp only [Spec.RandomOracle.query, he, PMF.pure_map, PMF.pure_apply, hcons]
    exact indicator_le_add _ _
  | none =>
    simp only [Spec.RandomOracle.query, he, PMF.map_comp, Function.comp_def, historyBad_cons]
    have hu := RandomOracleCollision.boolean_or_mass (PMF.uniformOfFintype Output)
      (fun answer => bad input answer) (fun _ => historyBad bad history)
    refine hu.trans ?_
    rw [add_comm (indicator _) epsilon]
    refine add_le_add (hbad input) ?_
    rw [map_const_true]

theorem run_trap_bound (procedure : Procedure Input Output State) (bad : Input → Output → Bool)
    (epsilon : ℝ≥0∞) (hbad : ∀ input, ((PMF.uniformOfFintype Output).map (bad input)) true ≤ epsilon)
    (fuel : Nat) (state : State) (table : Input → Option Output) (history : List (Input × Output))
    (hrecorded : Recorded table history) :
    ((run procedure fuel state table history).map (fun out => historyBad bad out.history)) true ≤
      indicator (historyBad bad history) + fuel * epsilon := by
  induction fuel generalizing state table history with
  | zero =>
    simp only [run, PMF.pure_map, PMF.pure_apply, Nat.cast_zero, zero_mul, add_zero]
    exact ite_le_indicator _
  | succ fuel ih =>
    simp only [run, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      simp only [PMF.pure_map, PMF.pure_apply]
      exact indicator_le_add _ _
    | query input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      have h1 := bind_map_indicator_le (Spec.RandomOracle.query table input)
        (fun result => run procedure fuel (next result.1) result.2 ((input, result.1) :: history))
        (fun out => historyBad bad out.history)
        (fun result => historyBad bad ((input, result.1) :: history)) (fuel * epsilon)
        (fun result hr => ih (next result.1) result.2 ((input, result.1) :: history)
          (RandomOracleCollisionInvariant.query_recorded table history input result hrecorded hr))
      rw [PMF.map_bind] at h1
      refine h1.trans ?_
      have h2 := query_trap_bound bad epsilon hbad table history hrecorded input
      calc
        _ ≤ (indicator (historyBad bad history) + epsilon) + fuel * epsilon := add_le_add h2 le_rfl
        _ = _ := by
          push_cast
          ring

omit [Fintype Output] [Nonempty Output] in
theorem recorded_empty : Recorded (fun _ : Input => (none : Option Output)) [] := by
  intro input answer
  simp

/-- The adaptive trap bound for the whole experiment. -/
theorem experiment_trap_bound (procedure : Procedure Input Output State) (bad : Input → Output → Bool)
    (epsilon : ℝ≥0∞) (hbad : ∀ input, ((PMF.uniformOfFintype Output).map (bad input)) true ≤ epsilon)
    (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map (fun out => historyBad bad out.history)) true ≤
      budget * epsilon := by
  have h := run_trap_bound procedure bad epsilon hbad budget initial (fun _ => none) [] recorded_empty
  simpa only [experiment, historyBad, List.any_nil, indicator_false, zero_add] using h

/-- A trapped pair stored in the final table is also in the history. -/
theorem table_trap_implies_history (procedure : Procedure Input Output State) (budget : Nat) (initial : State)
    (bad : Input → Output → Bool) (out : Result Input Output State)
    (hout : out ∈ (experiment procedure budget initial).support)
    (input : Input) (answer : Output) (hstored : out.table input = some answer) (hbad : bad input answer = true) :
    historyBad bad out.history = true :=
  List.any_eq_true.mpr ⟨(input, answer),
    ((RandomOracleCollisionInvariant.experiment_invariants procedure budget initial out hout).1 input answer).mp hstored, hbad⟩

section Kernel

variable {F : Type*} [Field F] [Fintype F] {s payload : Nat}

theorem uniform_kernel_trap_le (vector : Input → Fin (s + payload) → F) (input : Input) :
    ((PMF.uniformOfFintype (Matrix (Fin s) (Fin payload) F)).map (kernelTrap vector input)) true ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ ^ s := by
  by_cases hv : vector input = 0
  · have hzero : kernelTrap vector input = fun _ => false := by
      funext M
      simp [kernelTrap, hv]
    rw [hzero, map_const_true, indicator_false]
    exact zero_le _
  · have hk := ConsistencyMatrix.kernel_probability_le (vector input) hv
    rw [Spec.ConsistencyMatrix.kernelProbability, Spec.UniformChallenges.probability,
      ← ChallengeMixtures.eventOutcome_true, Spec.UniformChallenges.eventOutcome] at hk
    have hshape : kernelTrap vector input = fun M =>
        @decide (∀ a, Spec.ConsistencyMatrix.masked M (vector input) a = 0) (Classical.propDecidable _) := by
      funext M
      simp only [kernelTrap, ne_eq, hv, not_false_eq_true, true_and]
      exact decide_eq_decide.mpr Iff.rfl
    rw [hshape]
    exact hk

/-- Any adaptive procedure making at most budget mask queries sees a mask
annihilating the fixed vector of its own query input with probability at
most budget*|F|^(-s). -/
theorem kernel_trap_experiment_bound (procedure : Procedure Input (Matrix (Fin s) (Fin payload) F) State)
    (budget : Nat) (initial : State) (vector : Input → Fin (s + payload) → F) :
    ((experiment procedure budget initial).map (fun out => historyBad (kernelTrap vector) out.history)) true ≤
      budget * (Fintype.card F : ℝ≥0∞)⁻¹ ^ s :=
  experiment_trap_bound procedure (kernelTrap vector) _ (fun input => uniform_kernel_trap_le vector input) budget initial

end Kernel

theorem binary_kernel_trap_bound {lambda B payload : Nat}
    (procedure : Procedure Input (Matrix (Fin (lambda + B)) (Fin payload) (ZMod 2)) State)
    (budget : Nat) (initial : State) (vector : Input → Fin ((lambda + B) + payload) → ZMod 2) :
    ((experiment procedure budget initial).map (fun out => historyBad (kernelTrap vector) out.history)) true ≤
      budget * (2 : ℝ≥0∞)⁻¹ ^ (lambda + B) := by
  have h := kernel_trap_experiment_bound procedure budget initial vector
  simpa [ZMod.card] using h

end
end SDitH.Proofs.RandomOracleTrap
