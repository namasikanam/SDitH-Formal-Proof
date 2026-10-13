import SDitH.Spec.PartialBLCRetry
import SDitH.Proofs.ConcreteChallenges
import SDitH.Proofs.BLCRetry

namespace SDitH.Proofs.PartialBLCRetry

open Spec.PartialBLCRetry Spec.ConcreteChallenges Spec.DomainSeparation

variable {F : Type*} [Zero F] [DecidableEq F] {lambda tau kappa wpow : Nat}

theorem step_decided_iff (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (counter : Spec.BLCRetry.Counter)
    (out : Spec.BLCRetry.Step (Spec.BAVC.Opening lambda tau)) :
    step key Topen expand encode counter = .decided out ↔
      ∃ challenge cursor, expand counter = .returned challenge cursor ∧
        Spec.BLCRetry.step (Spec.BLCRetry.attempt key Topen (fun _ => challenge) encode) counter = out := by
  cases he : expand counter <;> simp [step, he]

/-- When expansion returns, this is exactly the existing actual BAVC/retry
step. No law relating a supplied total expander to SHAKE is assumed. -/
theorem step_total (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (cursor : Spec.BLCRetry.Counter → Spec.ByteSampling.Reader)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (counter : Spec.BLCRetry.Counter) :
    step key Topen (fun ctr => .returned (expand ctr) (cursor ctr)) encode counter =
      .decided (Spec.BLCRetry.step (Spec.BLCRetry.attempt key Topen expand encode) counter) := rfl

theorem observe_total (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (cursor : Spec.BLCRetry.Counter → Spec.ByteSampling.Reader)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat) (counter : Spec.BLCRetry.Counter) :
    observe key Topen (fun ctr => .returned (expand ctr) (cursor ctr)) encode fuel counter =
      liftTotal (Spec.BLCRetry.observe (Spec.BLCRetry.attempt key Topen expand encode) fuel counter) := by
  induction fuel generalizing counter with
  | zero => rfl
  | succ fuel ih =>
    rw [observe, step_total, Spec.BLCRetry.observe]
    cases hs : Spec.BLCRetry.step (Spec.BLCRetry.attempt key Topen expand encode) counter with
    | again next => exact ih next
    | done ctr opening => rfl
    | undefined fault => rfl

/-- Every returned opening has an actual returned expansion, successful BAVC
opening and passing header at its final counter. Undefined expansion is never
hidden behind an assumed challenge. -/
theorem observe_returned (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat)
    (start result : Spec.BLCRetry.Counter) (opening : Spec.BAVC.Opening lambda tau)
    (h : observe key Topen expand encode fuel start = .returned result opening) :
    start.val ≤ result.val ∧ ∃ challenge cursor,
      expand result = .returned challenge cursor ∧
      Spec.BAVC.openCommitment key challenge.hidden Topen = .ok opening ∧
      Spec.BLCRetry.GrindingPassed challenge.grinding ∧ encode challenge.hidden ≠ 0 := by
  induction fuel generalizing start with
  | zero => simp [observe] at h
  | succ fuel ih =>
    cases hs : step key Topen expand encode start with
    | expansionPending state => simp [observe, hs] at h
    | undefinedExpansion state candidate => simp [observe, hs] at h
    | decided decision =>
      obtain ⟨challenge, cursor, he, hd⟩ := (step_decided_iff key Topen expand encode start decision).mp hs
      cases decision with
      | again next =>
        simp only [observe, hs] at h
        obtain ⟨hle, witness⟩ := ih next h
        have hn := BLCRetry.step_again (Spec.BLCRetry.attempt key Topen (fun _ => challenge) encode)
          start next hd
        exact ⟨by omega, witness⟩
      | done counter value =>
        simp only [observe, hs, Observation.returned.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, ha⟩ := (BLCRetry.step_done_iff
          (Spec.BLCRetry.attempt key Topen (fun _ => challenge) encode) start counter value).mp hd
        obtain ⟨ho, hg, hn⟩ := (BLCRetry.attempt_ready_iff key Topen (fun _ => challenge) encode
          start value).mp ha
        exact ⟨le_rfl, challenge, cursor, he, ho, hg, hn⟩
      | undefined fault => simp [observe, hs] at h

theorem observe_no_expansion_return (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hn : ∀ ctr challenge cursor, expand ctr ≠ .returned challenge cursor)
    (fuel : Nat) (start result : Spec.BLCRetry.Counter) (opening : Spec.BAVC.Opening lambda tau) :
    observe key Topen expand encode fuel start ≠ .returned result opening := by
  intro h
  obtain ⟨_, challenge, cursor, he, _⟩ := observe_returned key Topen expand encode fuel start result opening h
  exact hn result challenge cursor he

theorem observe_returned_stable (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel extra : Nat)
    (start result : Spec.BLCRetry.Counter) (opening : Spec.BAVC.Opening lambda tau)
    (h : observe key Topen expand encode fuel start = .returned result opening) :
    observe key Topen expand encode (fuel + extra) start = .returned result opening := by
  induction fuel generalizing start with
  | zero => simp [observe] at h
  | succ fuel ih =>
    cases hs : step key Topen expand encode start with
    | expansionPending state => simp [observe, hs] at h
    | undefinedExpansion state candidate => simp [observe, hs] at h
    | decided decision =>
      cases decision with
      | again next =>
        simp only [observe, hs] at h
        simpa only [Nat.succ_add, observe, hs] using ih next h
      | done counter value => simpa only [Nat.succ_add, observe, hs] using h
      | undefined fault => simp [observe, hs] at h

theorem hashOpen_no_return (category : Spec.FieldRepresentation.Category) (tau kappa wpow : Nat)
    (ht : 0 < tau) (key : Spec.BAVC.Key (Spec.FieldRepresentation.width category) tau (2 ^ kappa))
    (Topen : Nat) (encoding : CounterEncoding) (digest : Bits (2 * Spec.FieldRepresentation.width category))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel count : Nat)
    (enough : wpow ≤ 8 * count) (counter : Spec.BLCRetry.Counter)
    (opening : Spec.BAVC.Opening (Spec.FieldRepresentation.width category) tau) :
    hashOpen category tau kappa wpow key Topen encoding digest encode innerFuel outerFuel count enough ≠
      .returned counter opening := by
  apply observe_no_expansion_return
  intro ctr challenge cursor
  exact ConcreteChallenges.hashEvaluation_no_return category tau kappa wpow ht encoding digest ctr
    innerFuel count enough challenge cursor

/-- For submitted-sized index ranges, the concrete Algorithm-11 caller stops
at counter zero's first integer assignment, before BAVC.Open or any retry. -/
theorem hashOpen_missing (category : Spec.FieldRepresentation.Category) (tau kappa wpow : Nat)
    (ht : 0 < tau) (hk : kappa ≤ 32)
    (key : Spec.BAVC.Key (Spec.FieldRepresentation.width category) tau (2 ^ kappa))
    (Topen : Nat) (encoding : CounterEncoding) (digest : Bits (2 * Spec.FieldRepresentation.width category))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel count : Nat)
    (enough : wpow ≤ 8 * count) :
    let src := Spec.SHAKE.reader category (evaluationInput encoding digest 0)
    hashOpen category tau kappa wpow key Topen encoding digest encode (innerFuel + 1) (outerFuel + 1)
      count enough = .undefinedExpansion 0 ⟨[], by simp, src⟩ (Spec.IntegerSampling.readCandidate src) := by
  dsimp only
  rw [hashOpen, observe, step, ConcreteChallenges.hashEvaluation_missing category tau kappa wpow ht hk]

end SDitH.Proofs.PartialBLCRetry
