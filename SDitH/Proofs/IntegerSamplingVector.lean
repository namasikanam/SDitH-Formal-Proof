import SDitH.Spec.IntegerSamplingVector
import SDitH.Proofs.IntegerSampling

namespace SDitH.Proofs.IntegerSampling

set_option maxRecDepth 4096

open Spec.IntegerSampling Spec.ByteSampling Spec.DomainSeparation

theorem finishedVector_toList {m n : Nat} (state : PartialVector m n)
    (complete : state.values.length = n) : (finishedVector state complete).toList = state.values := by
  cases state with
  | mk values bounded next =>
    dsimp only at complete
    subst n
    simp [finishedVector, Vector.toList_ofFn, List.ofFn_getElem]

theorem threshold_power_two (kappa : Nat) (hk : kappa ≤ 32) :
    sourceThreshold (2 ^ kappa) = wordBound := by
  exact Nat.div_mul_cancel (Nat.pow_dvd_pow 2 hk)

/-- For every stream, every candidate is accepted at the power-of-two ranges
used by evaluation challenges. This does not resolve the accepted assignment. -/
theorem attempt_power_two (kappa : Nat) (hk : kappa ≤ 32) (src : Reader) :
    attempt (2 ^ kappa) src = .accepted (readCandidate src) := by
  simp only [attempt, attemptWith, threshold_power_two kappa hk,
    if_pos (readCandidate_bound src)]

theorem vectorPending_finished {m n : Nat} (state : PartialVector m n)
    (complete : state.values.length = n) :
    vectorPending state = .returned (finishedVector state complete) state.next := by
  rw [vectorPending, dif_pos complete]

theorem vectorStep_finished (m : Nat) (hm : 0 < m) (n : Nat) (binding : Option Nat)
    (resume : PartialVector m n → VectorObservation m n) (state : PartialVector m n)
    (complete : state.values.length = n) :
    vectorStep m hm n binding resume state = .returned (finishedVector state complete) state.next := by
  rw [vectorStep, dif_pos complete]

theorem vectorStep_missing (m : Nat) (hm : 0 < m) (n : Nat)
    (resume : PartialVector m n → VectorObservation m n) (state : PartialVector m n)
    (incomplete : state.values.length ≠ n) (candidate : Candidate)
    (ha : attempt m state.next = .accepted candidate) :
    vectorStep m hm n none resume state = .undefinedAssignment state candidate := by
  rw [vectorStep, dif_neg incomplete, ha]

theorem observeVector_finished (m : Nat) (hm : 0 < m) (n : Nat) (binding : Option Nat)
    (fuel : Nat) (state : PartialVector m n) (complete : state.values.length = n) :
    observeVector m hm n binding fuel state = .returned (finishedVector state complete) state.next := by
  cases fuel with
  | zero => exact vectorPending_finished state complete
  | succ fuel => exact vectorStep_finished m hm n binding _ state complete

theorem sampleVector_empty (m : Nat) (hm : 0 < m) (binding : Option Nat) (fuel : Nat) (src : Reader) :
    sampleVectorWithBinding m hm 0 binding fuel src = .returned #v[] src := by
  rw [sampleVectorWithBinding, observeVector_finished m hm 0 binding fuel _ rfl]
  apply congrArg (fun v => VectorObservation.returned v src)
  apply Vector.ext
  intro i hi
  omega

/-- No return can skip the actual read of the missing B in a nonempty
request, even if some or all earlier candidates are rejected. -/
theorem observeVector_unbound_no_return (m : Nat) (hm : 0 < m) (n fuel : Nat)
    (state : PartialVector m n) (incomplete : state.values.length < n)
    (values : Vector (Fin m) n) (next : Reader) :
    observeVector m hm n none fuel state ≠ .returned values next := by
  induction fuel generalizing state with
  | zero => simp [observeVector, vectorPending, Nat.ne_of_lt incomplete]
  | succ fuel ih =>
    rw [observeVector, vectorStep, dif_neg (Nat.ne_of_lt incomplete)]
    cases ha : attempt m state.next with
    | accepted candidate => simp
    | rejected later => exact ih ⟨state.values, state.bounded, later⟩ incomplete

theorem sampleVector_unbound_no_return (m : Nat) (hm : 0 < m) (n fuel : Nat) (hn : 0 < n)
    (src : Reader) (values : Vector (Fin m) n) (next : Reader) :
    sampleVector m hm n fuel src ≠ .returned values next :=
  observeVector_unbound_no_return m hm n fuel ⟨[], by simp, src⟩ hn values next

/-- At a power-of-two range the missing assignment is reached after the first
four-byte read, for every byte stream and every positive observation budget. -/
theorem sampleVector_power_missing (kappa : Nat) (hk : kappa ≤ 32) (n fuel : Nat) (hn : 0 < n)
    (src : Reader) :
    sampleVector (2 ^ kappa) (pow_pos (by decide) _) n (fuel + 1) src =
      .undefinedAssignment ⟨[], by simp, src⟩ (readCandidate src) := by
  exact vectorStep_missing (2 ^ kappa) (pow_pos (by decide) _) n _ ⟨[], by simp, src⟩
    (Nat.ne_of_lt hn) _ (attempt_power_two kappa hk src)

theorem observeVector_returned_stable (m : Nat) (hm : 0 < m) (n : Nat) (binding : Option Nat)
    (fuel extra : Nat) (state : PartialVector m n) (values : Vector (Fin m) n) (next : Reader)
    (h : observeVector m hm n binding fuel state = .returned values next) :
    observeVector m hm n binding (fuel + extra) state = .returned values next := by
  induction fuel generalizing state with
  | zero =>
    by_cases complete : state.values.length = n
    · simpa only [observeVector_finished m hm n binding _ state complete] using h
    · simp [observeVector, vectorPending, complete] at h
  | succ fuel ih =>
    by_cases complete : state.values.length = n
    · simpa only [observeVector_finished m hm n binding _ state complete] using h
    · rw [observeVector, vectorStep, dif_neg complete] at h
      rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega,
        observeVector, vectorStep, dif_neg complete]
      cases ha : attempt m state.next with
      | rejected later =>
        simp only [ha] at h ⊢
        exact ih _ h
      | accepted candidate =>
        simp only [ha] at h ⊢
        cases binding with
        | none => contradiction
        | some value => exact ih _ h

/-- An external, fixed B binding produces its literal repeated residue. This
is not a replacement for v or a proof that the intended sampler is uniform. -/
theorem observeVector_power_complete (kappa : Nat) (hk : kappa ≤ 32) (n fuel value : Nat)
    (state : PartialVector (2 ^ kappa) n) (enough : n ≤ state.values.length + fuel) :
    ∃ values next,
      observeVector (2 ^ kappa) (pow_pos (by decide) _) n (some value) fuel state = .returned values next ∧
      values.toList = state.values ++ List.replicate (n - state.values.length)
        (⟨value % (2 ^ kappa), Nat.mod_lt _ (pow_pos (by decide) _)⟩ : Fin (2 ^ kappa)) ∧
      next = advance state.next (4 * (n - state.values.length)) := by
  induction fuel generalizing state with
  | zero =>
    have complete : state.values.length = n := by have hb := state.bounded; omega
    refine ⟨finishedVector state complete, state.next, ?_, ?_, ?_⟩
    · exact observeVector_finished _ _ _ _ _ _ complete
    · simp [finishedVector_toList, complete]
    · cases hn : state.next
      simp [complete, advance]
  | succ fuel ih =>
    by_cases complete : state.values.length = n
    · refine ⟨finishedVector state complete, state.next, ?_, ?_, ?_⟩
      · exact observeVector_finished _ _ _ _ _ _ complete
      · simp [finishedVector_toList, complete]
      · cases hn : state.next
        simp [complete, advance]
    · have hb := state.bounded
      let current : Fin (2 ^ kappa) := ⟨value % (2 ^ kappa), Nat.mod_lt _ (pow_pos (by decide) _)⟩
      let updated : PartialVector (2 ^ kappa) n :=
        ⟨state.values ++ [current], by simp only [List.length_append, List.length_singleton]; omega,
          (readCandidate state.next).next⟩
      have hlen : updated.values.length = state.values.length + 1 := by simp [updated]
      obtain ⟨values, next, hr, hv, hn⟩ := ih updated (by rw [hlen]; omega)
      refine ⟨values, next, ?_, ?_, ?_⟩
      · rw [observeVector, vectorStep, dif_neg complete, attempt_power_two kappa hk]
        exact hr
      · have hremaining : n - state.values.length = (n - (state.values.length + 1)) + 1 := by omega
        rw [hv, hlen, hremaining, List.replicate_succ]
        simp [updated, current, List.append_assoc]
      · rw [hn]
        change advance (advance state.next 4) (4 * (n - updated.values.length)) =
          advance state.next (4 * (n - state.values.length))
        rw [hlen]
        cases hs : state.next with
        | mk stream position =>
          simp only [advance]
          congr 1
          omega

theorem sampleVector_power_complete (kappa : Nat) (hk : kappa ≤ 32) (n value : Nat) (src : Reader) :
    sampleVectorWithBinding (2 ^ kappa) (pow_pos (by decide) _) n (some value) n src =
      .returned (Vector.replicate n
        (⟨value % (2 ^ kappa), Nat.mod_lt _ (pow_pos (by decide) _)⟩ : Fin (2 ^ kappa)))
        (advance src (4 * n)) := by
  obtain ⟨values, next, hr, hv, hn⟩ :=
    observeVector_power_complete kappa hk n n value ⟨[], by simp, src⟩ (by simp)
  have he : values = Vector.replicate n
      (⟨value % (2 ^ kappa), Nat.mod_lt _ (pow_pos (by decide) _)⟩ : Fin (2 ^ kappa)) := by
    apply Vector.toList_inj.mp
    simpa using hv
  simpa only [sampleVectorWithBinding, he, hn, List.length_nil, Nat.sub_zero] using hr

end SDitH.Proofs.IntegerSampling
