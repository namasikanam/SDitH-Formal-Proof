import SDitH.Spec.RandomOraclePipeline
import SDitH.Proofs.RandomOracleCollisionInvariant

namespace SDitH.Proofs.RandomOraclePipeline

open Spec.RandomOracleCollision
open scoped Classical ENNReal
noncomputable section

variable {Input Output A B : Type*}
variable [Fintype Output] [Nonempty Output]

theorem run_history_length (p : Procedure Input Output A) (fuel : Nat) (state : A)
    (table : Input → Option Output) (history : List (Input × Output)) (out : Result Input Output A)
    (hout : out ∈ (run p fuel state table history).support) : out.history.length ≤ history.length + fuel := by
  induction fuel generalizing state table history out with
  | zero =>
    simp only [run, PMF.mem_support_pure_iff] at hout
    subst out
    exact Nat.le_refl _
  | succ fuel ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      rw [PMF.mem_support_pure_iff] at hnext
      subst out
      exact Nat.le_add_right _ _
    | query input next =>
      obtain ⟨result, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst out
      have h := ih (next result.1) result.2 ((input, result.1) :: history) tail ht
      simpa only [List.length_cons, Nat.add_right_comm history.length 1 fuel] using h

theorem choose_two_add (q k : Nat) : q.choose 2 + (k * q + k.choose 2) = (q + k).choose 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    change q.choose 2 + ((k + 1) * q + (k + 1).choose 2) = ((q + k) + 1).choose 2
    rw [Nat.choose_succ_succ k 1, Nat.choose_succ_succ (q + k) 1, Nat.choose_one_right, Nat.choose_one_right]
    rw [← ih]
    ring

/-- The second phase has no independent fresh oracle. Its collision cost
includes matches with answers from the complete first-phase query history. -/
theorem collision_bound (first : Procedure Input Output A) (q : Nat) (initial : A)
    (second : Procedure Input Output B) (k : Nat) (next : A → B) :
    ((Spec.RandomOraclePipeline.experiment first q initial second k next).map Result.collided) true ≤
      ((q + k).choose 2 : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  have hrest (start : Result Input Output A) (hs : start ∈ (experiment first q initial).support) :
      ((run second k (next start.state) start.table start.history).map Result.collided) true ≤
        ((k * q + k.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
    have hlen : start.history.length ≤ q := by
      simpa only [List.length_nil, Nat.zero_add] using
        run_history_length first q initial (fun _ => none) [] start hs
    apply (RandomOracleCollision.run_collision_bound second k (next start.state) start.table start.history).trans
    have hc : ((k * start.history.length + k.choose 2 : Nat) : ℝ≥0∞) ≤
        ((k * q + k.choose 2 : Nat) : ℝ≥0∞) := by
      exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left k hlen) (k.choose 2)
    exact mul_le_mul hc le_rfl (zero_le _) (zero_le _)
  have h := RandomOracleCollision.bind_or_bound (experiment first q initial)
    (fun start => run second k (next start.state) start.table start.history)
    Result.collided Result.collided _ hrest
  simp only [Spec.RandomOraclePipeline.experiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply h.trans
  calc
    _ ≤ (q.choose 2 : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ +
        ((k * q + k.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ :=
      add_le_add (RandomOracleCollision.experiment_collision_bound first q initial) le_rfl
    _ = _ := by rw [← add_mul, ← Nat.cast_add, choose_two_add]

theorem invariants (first : Procedure Input Output A) (q : Nat) (initial : A)
    (second : Procedure Input Output B) (k : Nat) (next : A → B) (out : Result Input Output B)
    (hout : out ∈ (Spec.RandomOraclePipeline.experiment first q initial second k next).support) :
    Recorded out.table out.history ∧ (out.collided = false → CollisionFree out.table) := by
  obtain ⟨start, hs, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst out
  have hfirst := RandomOracleCollisionInvariant.experiment_invariants first q initial start hs
  have hsecond := RandomOracleCollisionInvariant.run_invariants second k (next start.state)
    start.table start.history tail ht hfirst.1
  refine ⟨hsecond.1, ?_⟩
  intro hflag
  have hh : start.collided = false ∧ tail.collided = false := Bool.or_eq_false_iff.mp hflag
  exact hsecond.2 (hfirst.2 hh.1) hh.2

theorem stored_collision_implies_flag (first : Procedure Input Output A) (q : Nat) (initial : A)
    (second : Procedure Input Output B) (k : Nat) (next : A → B) (out : Result Input Output B)
    (hout : out ∈ (Spec.RandomOraclePipeline.experiment first q initial second k next).support)
    (pair : Input × Input) (hwin : storedCollision pair out = true) : out.collided = true := by
  obtain ⟨hne, answer, hl, hr⟩ := of_decide_eq_true hwin
  cases he : out.collided with
  | true => rfl
  | false =>
    exact False.elim (hne ((invariants first q initial second k next out hout).2 he pair.1 pair.2 answer hl hr))

/-- A computed bad event covered by actual stored collisions inherits the
total-budget bound. The event-to-collision premise must be proved by callers. -/
theorem event_bound (first : Procedure Input Output A) (q : Nat) (initial : A)
    (second : Procedure Input Output B) (k : Nat) (next : A → B) (bad : Result Input Output B → Bool)
    (hbad : ∀ out ∈ (Spec.RandomOraclePipeline.experiment first q initial second k next).support,
      bad out = true → ∃ pair, storedCollision pair out = true) :
    ((Spec.RandomOraclePipeline.experiment first q initial second k next).map bad) true ≤
      ((q + k).choose 2 : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  apply le_trans ?_ (collision_bound first q initial second k next)
  simp only [PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro out
  by_cases hs : out ∈ (Spec.RandomOraclePipeline.experiment first q initial second k next).support
  · by_cases hw : bad out = true
    · obtain ⟨pair, hp⟩ := hbad out hs hw
      have hf := stored_collision_implies_flag first q initial second k next out hs pair hp
      simp [hw, hf]
    · simp [hw]
  · have hz : Spec.RandomOraclePipeline.experiment first q initial second k next out = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hs
    simp [hz]

end
end SDitH.Proofs.RandomOraclePipeline
