import SDitH.Proofs.RandomOracleCollision

namespace SDitH.Proofs.RandomOracleCollisionInvariant

open Spec.RandomOracleCollision
open scoped Classical ENNReal
noncomputable section

variable {Input Output State : Type*}
variable [Fintype Output] [Nonempty Output]

theorem query_recorded (table : Input → Option Output) (history : List (Input × Output))
    (input : Input) (result : Output × (Input → Option Output))
    (hrecorded : Recorded table history) (hr : result ∈ (Spec.RandomOracle.query table input).support) :
    Recorded result.2 ((input, result.1) :: history) := by
  unfold Spec.RandomOracle.query at hr
  cases he : table input with
  | some old =>
    rw [he, PMF.mem_support_pure_iff] at hr
    subst result
    intro q answer
    simp only [List.mem_cons, Prod.mk.injEq]
    constructor
    · exact fun h => Or.inr ((hrecorded q answer).mp h)
    · rintro (⟨rfl, rfl⟩ | h)
      · exact he
      · exact (hrecorded q answer).mpr h
  | none =>
    rw [he] at hr
    obtain ⟨fresh, _, hresult⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst result
    intro q answer
    by_cases hq : q = input
    · subst q
      simp [← hrecorded input answer, he, eq_comm]
    · simp [hq, ← hrecorded q answer]

theorem query_collisionFree (table : Input → Option Output) (history : List (Input × Output))
    (input : Input) (result : Output × (Input → Option Output))
    (hrecorded : Recorded table history) (hfree : CollisionFree table)
    (hr : result ∈ (Spec.RandomOracle.query table input).support)
    (hhit : freshHit table history input result.1 = false) : CollisionFree result.2 := by
  unfold Spec.RandomOracle.query at hr
  cases he : table input with
  | some old =>
    rw [he, PMF.mem_support_pure_iff] at hr
    subst result
    exact hfree
  | none =>
    rw [he] at hr
    obtain ⟨fresh, _, hresult⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst result
    have habsent (q : Input) : table q ≠ some fresh := by
      intro hq
      have hmem := (hrecorded q fresh).mp hq
      have htrue : history.any (fun old => decide (old.2 = fresh)) = true :=
        List.any_eq_true.mpr ⟨(q, fresh), hmem, by simp⟩
      simp [freshHit, he, htrue] at hhit
    intro left right answer hl hr
    by_cases hleft : left = input
    · subst left
      have hfresh : fresh = answer := by simpa using hl
      by_cases hright : right = input
      · exact hright.symm
      · have hold : table right = some fresh := by simpa [Function.update_of_ne hright, ← hfresh] using hr
        exact False.elim (habsent right hold)
    · by_cases hright : right = input
      · subst right
        have hfresh : fresh = answer := by simpa using hr
        have hold : table left = some fresh := by simpa [Function.update_of_ne hleft, ← hfresh] using hl
        exact False.elim (habsent left hold)
      · exact hfree left right answer
          (by simpa [Function.update_of_ne hleft] using hl)
          (by simpa [Function.update_of_ne hright] using hr)

/-- The execution maintains exact table/log correspondence. Starting with a
collision-free table, any final stored collision must have raised the flag. -/
theorem run_invariants (procedure : Procedure Input Output State) (fuel : Nat)
    (state : State) (table : Input → Option Output) (history : List (Input × Output))
    (out : Result Input Output State) (hout : out ∈ (run procedure fuel state table history).support)
    (hrecorded : Recorded table history) :
    Recorded out.table out.history ∧ (CollisionFree table → out.collided = false → CollisionFree out.table) := by
  induction fuel generalizing state table history out with
  | zero =>
    simp only [run, PMF.mem_support_pure_iff] at hout
    subst out
    exact ⟨hrecorded, fun h _ => h⟩
  | succ fuel ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      rw [PMF.mem_support_pure_iff] at hnext
      subst out
      exact ⟨hrecorded, fun h _ => h⟩
    | query input next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst out
      have hs := ih (next result.1) result.2 ((input, result.1) :: history) tail ht
        (query_recorded table history input result hrecorded hr)
      refine ⟨hs.1, ?_⟩
      intro hfree hfalse
      have hh : freshHit table history input result.1 = false ∧ tail.collided = false :=
        Bool.or_eq_false_iff.mp hfalse
      exact hs.2 (query_collisionFree table history input result hrecorded hfree hr hh.1) hh.2

theorem experiment_invariants (procedure : Procedure Input Output State) (budget : Nat) (initial : State)
    (out : Result Input Output State) (hout : out ∈ (experiment procedure budget initial).support) :
    Recorded out.table out.history ∧ (out.collided = false → CollisionFree out.table) := by
  have h := run_invariants procedure budget initial (fun _ => none) [] out hout (by simp [Recorded])
  exact ⟨h.1, h.2 (by simp [CollisionFree])⟩

theorem stored_collision_implies_flag (procedure : Procedure Input Output State) (budget : Nat) (initial : State)
    (out : Result Input Output State) (hout : out ∈ (experiment procedure budget initial).support)
    (pair : Input × Input) (hwin : storedCollision pair out = true) : out.collided = true := by
  obtain ⟨hne, answer, hleft, hright⟩ := of_decide_eq_true hwin
  cases he : out.collided with
  | true => rfl
  | false =>
    exact False.elim (hne ((experiment_invariants procedure budget initial out hout).2 he
      pair.1 pair.2 answer hleft hright))

/-- An arbitrary adaptive selector of actual stored collisions satisfies the
birthday bound. This includes selectors inspecting the complete final table. -/
theorem selection_collision_bound (procedure : Procedure Input Output State) (budget : Nat) (initial : State)
    (pick : Result Input Output State → Option (Input × Input)) :
    ((experiment procedure budget initial).map (selectionWins pick)) true ≤
      (budget.choose 2 : ℝ≥0∞) * (Fintype.card Output : ℝ≥0∞)⁻¹ := by
  apply le_trans ?_ (RandomOracleCollision.experiment_collision_bound procedure budget initial)
  simp only [PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro out
  by_cases hs : out ∈ (experiment procedure budget initial).support
  · by_cases hwin : selectionWins pick out = true
    · have hflag : out.collided = true := by
        cases he : pick out with
        | none => simp [selectionWins, he] at hwin
        | some pair =>
          exact stored_collision_implies_flag procedure budget initial out hs pair
            (by simpa only [selectionWins, he] using hwin)
      simp [hwin, hflag]
    · simp [hwin]
  · have hz : experiment procedure budget initial out = 0 := by simpa only [PMF.mem_support_iff, not_not] using hs
    simp [hz]

end
end SDitH.Proofs.RandomOracleCollisionInvariant
