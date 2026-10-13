import SDitH.Spec.RandomOracleCollision
import SDitH.Proofs.ChallengeMixtures

namespace SDitH.Proofs.RandomOracleCollision

open Spec.RandomOracleCollision
open scoped Classical ENNReal
noncomputable section

theorem boolean_or_mass {A : Type*} (p : PMF A) (left right : A → Bool) :
    (p.map (fun a => left a || right a)) true ≤ (p.map left) true + (p.map right) true := by
  simp only [PMF.map_apply]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro a
  cases left a <;> cases right a <;> simp

/-- Union bound for an event seen before an adaptive continuation. Its future
failure law need only satisfy the stated bound on the actual prefix support. -/
theorem bind_or_bound {A B : Type*} (p : PMF A) (next : A → PMF B)
    (first : A → Bool) (later : B → Bool) (epsilon : ℝ≥0∞)
    (h : ∀ a ∈ p.support, ((next a).map later) true ≤ epsilon) :
    (p.bind (fun a => (next a).map (fun b => first a || later b))) true ≤
      (p.map first) true + epsilon := by
  let joint := p.bind (fun a => (next a).map (fun b => (a, b)))
  have hu := boolean_or_mass joint (fun ab => first ab.1) (fun ab => later ab.2)
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def] at hu
  have hfirst : (p.bind (fun a => (next a).map (fun _ => first a))) = p.map first := by
    calc
      _ = p.bind (fun a => PMF.pure (first a)) := by
        congr 1
        funext a
        exact PMF.map_const _ _
      _ = p.map first := rfl
  rw [hfirst] at hu
  exact hu.trans (add_le_add le_rfl (ChallengeMixtures.bind_true_le p _ epsilon h))

variable {Input Output State : Type*}
variable [Fintype Output] [Nonempty Output]

theorem uniform_guess (answer : Output) :
    ((PMF.uniformOfFintype Output).map (fun fresh => decide (answer = fresh))) true =
      (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  rw [← PMF.uniformOfFintype_apply answer]
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  congr 1
  ext fresh
  simp [eq_comm]

theorem uniform_history_hit (history : List (Input × Output)) :
    ((PMF.uniformOfFintype Output).map
      (fun answer => history.any (fun old => decide (old.2 = answer)))) true ≤
      (history.length : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  have h := ChallengeMixtures.boolean_union_bound (PMF.uniformOfFintype Output)
    (fun answer => history.any (fun old => decide (old.2 = answer)))
    (fun i : Fin history.length => fun answer => decide ((history[i]).2 = answer)) (by
      intro answer _ hhit
      obtain ⟨old, hold, he⟩ := List.any_eq_true.mp hhit
      obtain ⟨index, hlt, hindex⟩ := List.mem_iff_getElem.mp hold
      exact ⟨⟨index, hlt⟩, by simpa only [Fin.getElem_fin, hindex] using he⟩)
  simpa only [uniform_guess, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

theorem query_hit_bound (table : Input → Option Output) (history : List (Input × Output)) (input : Input) :
    ((Spec.RandomOracle.query table input).map (fun result => freshHit table history input result.1)) true ≤
      (history.length : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  cases he : table input with
  | some answer => simp [Spec.RandomOracle.query, he, freshHit, PMF.pure_map]
  | none =>
    simpa only [Spec.RandomOracle.query, he, PMF.map_comp, Function.comp_def,
      freshHit, Option.isNone_none, Bool.true_and] using uniform_history_hit history

/-- Bound for arbitrary adaptive continuation from any table and history.
It counts collisions newly flagged during this continuation, not past collisions. -/
theorem run_collision_bound (procedure : Procedure Input Output State) (fuel : Nat)
    (state : State) (table : Input → Option Output) (history : List (Input × Output)) :
    ((run procedure fuel state table history).map Result.collided) true ≤
      ((fuel * history.length + fuel.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  induction fuel generalizing state table history with
  | zero => simp [run, PMF.pure_map]
  | succ fuel ih =>
    simp only [run, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop => simp [PMF.pure_map]
    | query input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      have hrest (result : Output × (Input → Option Output)) :
          ((run procedure fuel (next result.1) result.2 ((input, result.1) :: history)).map Result.collided) true ≤
            ((fuel * (history.length + 1) + fuel.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ :=
        ih (next result.1) result.2 ((input, result.1) :: history)
      have hu := bind_or_bound (Spec.RandomOracle.query table input)
        (fun result => run procedure fuel (next result.1) result.2 ((input, result.1) :: history))
        (fun result => freshHit table history input result.1) Result.collided _ (fun result _ => hrest result)
      apply hu.trans
      calc
        _ ≤ (history.length : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ +
            ((fuel * (history.length + 1) + fuel.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ :=
          add_le_add (query_hit_bound table history input) le_rfl
        _ = _ := by
          rw [← add_mul, ← Nat.cast_add]
          congr 2
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          ring

/-- The adaptive birthday bound. Queries may repeat and depend on all previous
answers; their total count is bounded by budget. -/
theorem experiment_collision_bound (procedure : Procedure Input Output State) (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map Result.collided) true ≤
      (budget.choose 2 : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  simpa only [experiment, List.length_nil, Nat.mul_zero, Nat.zero_add] using
    run_collision_bound procedure budget initial (fun _ => none) []

end
end SDitH.Proofs.RandomOracleCollision
