import SDitH.Spec.BLCRetry
import SDitH.Proofs.BAVCOpeningSafety
import Mathlib.Tactic

namespace SDitH.Proofs.BLCRetry

open Spec.BLCRetry

variable {α : Type*}

theorem step_done_iff (evaluate : Counter → Attempt α) (start result : Counter) (value : α) :
    step evaluate start = .done result value ↔ start = result ∧ evaluate start = .ready value := by
  cases h : evaluate start with
  | retry => simp [step, h, advance]; split <;> simp
  | ready v => simp [step, h]
  | undefinedOpening err => simp [step, h]

theorem step_again (evaluate : Counter → Attempt α) (start next : Counter)
    (h : step evaluate start = .again next) :
    evaluate start = .retry ∧ next.val = start.val + 1 := by
  cases he : evaluate start with
  | retry =>
    refine ⟨rfl, ?_⟩
    simp only [step, he, advance] at h
    split at h
    · cases h
      rfl
    · contradiction
  | ready value => simp [step, he] at h
  | undefinedOpening err => simp [step, he] at h

/-- A returned observation certifies a successful attempt at that counter and
that every preceding counter from the starting point was tried and rejected. -/
theorem observe_returned (evaluate : Counter → Attempt α) (fuel : Nat)
    (start result : Counter) (value : α)
    (h : observe evaluate fuel start = .returned result value) :
    evaluate result = .ready value ∧ start.val ≤ result.val ∧
      ∀ ctr : Counter, start.val ≤ ctr.val → ctr.val < result.val → evaluate ctr = .retry := by
  induction fuel generalizing start with
  | zero => simp [observe] at h
  | succ fuel ih =>
    cases hs : step evaluate start with
    | again next =>
      have hn := step_again evaluate start next hs
      simp only [observe, hs] at h
      obtain ⟨hr, hle, hearly⟩ := ih next h
      refine ⟨hr, by omega, ?_⟩
      intro ctr hstart hresult
      by_cases hc : ctr.val = start.val
      · have hc' : ctr = start := Fin.ext hc
        simpa [hc'] using hn.1
      · exact hearly ctr (by omega) hresult
    | done counter opening =>
      simp only [observe, hs, Observation.returned.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, he⟩ := (step_done_iff evaluate start counter opening).mp hs
      exact ⟨he, le_rfl, fun ctr hle hlt => False.elim (by omega)⟩
    | undefined fault => simp [observe, hs] at h

/-- The first passing counter is returned after exactly enough observations.
This is a conditional termination theorem, not an assumption that such a counter
exists in the 32-bit range for every hash/cipher input. -/
theorem observe_first_success (evaluate : Counter → Attempt α) (distance : Nat)
    (start result : Counter) (value : α)
    (hd : result.val = start.val + distance) (hr : evaluate result = .ready value)
    (hearly : ∀ ctr : Counter, start.val ≤ ctr.val → ctr.val < result.val → evaluate ctr = .retry) :
    observe evaluate (distance + 1) start = .returned result value := by
  induction distance generalizing start with
  | zero =>
    have he : result = start := Fin.ext (by omega)
    subst result
    simp [observe, step, hr]
  | succ distance ih =>
    have hstep : start.val < result.val := by omega
    have hbound : start.val + 1 < 2 ^ 32 := by have hb := result.isLt; omega
    let next : Counter := ⟨start.val + 1, hbound⟩
    have hre := hearly start le_rfl hstep
    have hs : step evaluate start = .again next := by
      simp only [step, hre, advance, dif_pos hbound]
      rfl
    rw [observe, hs]
    apply ih next
    · dsimp [next]
      omega
    · intro ctr hnext hlt
      exact hearly ctr (by dsimp [next] at hnext; omega) hlt

/-- Extending an observation cannot change an already returned result. -/
theorem observe_returned_stable (evaluate : Counter → Attempt α) (fuel extra : Nat)
    (start result : Counter) (value : α)
    (h : observe evaluate fuel start = .returned result value) :
    observe evaluate (fuel + extra) start = .returned result value := by
  induction fuel generalizing start with
  | zero => simp [observe] at h
  | succ fuel ih =>
    cases hs : step evaluate start with
    | again next =>
      simp only [observe, hs] at h
      simpa [Nat.succ_add, observe, hs] using ih next h
    | done counter opening =>
      simpa [Nat.succ_add, observe, hs] using h
    | undefined fault => simp [observe, hs] at h

/-- Two observations of the same run cannot return different openings or
counters, even if they stop observing after different numbers of attempts. -/
theorem observe_returned_unique (evaluate : Counter → Attempt α) (fuel₁ fuel₂ : Nat)
    (start result₁ result₂ : Counter) (value₁ value₂ : α)
    (h₁ : observe evaluate fuel₁ start = .returned result₁ value₁)
    (h₂ : observe evaluate fuel₂ start = .returned result₂ value₂) :
    result₁ = result₂ ∧ value₁ = value₂ := by
  have he₁ := observe_returned_stable evaluate fuel₁ fuel₂ start result₁ value₁ h₁
  have he₂ := observe_returned_stable evaluate fuel₂ fuel₁ start result₂ value₂ h₂
  rw [Nat.add_comm fuel₂ fuel₁, he₁] at he₂
  exact Observation.returned.inj he₂

theorem observe_no_undefined_opening (evaluate : Counter → Attempt α)
    (hsafe : ∀ ctr err, evaluate ctr ≠ .undefinedOpening err)
    (fuel : Nat) (start : Counter) (err : Spec.BAVC.OpeningError) :
    observe evaluate fuel start ≠ .undefined (.undefinedOpening err) := by
  induction fuel generalizing start with
  | zero => simp [observe]
  | succ fuel ih =>
    cases he : evaluate start with
    | retry =>
      simp only [observe, step, he, advance]
      by_cases hb : start.val + 1 < 2 ^ 32
      · rw [dif_pos hb]
        exact ih _
      · rw [dif_neg hb]
        simp
    | ready value => simp [observe, step, he]
    | undefinedOpening error => exact False.elim (hsafe start error he)

/-- The source's last counter can succeed; a retry at that point reaches the
unspecified overflow operation. It is not silently wrapped to zero. -/
theorem last_counter_retry_overflows (evaluate : Counter → Attempt α)
    (ctr : Counter) (hlast : ctr.val + 1 = 2 ^ 32) (hretry : evaluate ctr = .retry) :
    observe evaluate 1 ctr = .undefined .counterOverflow := by
  simp only [observe, step, hretry, advance]
  rw [dif_neg (by omega)]

theorem attempt_ready_iff {F : Type*} [Zero F] [DecidableEq F]
    {lambda tau N wpow : Nat} (key : Spec.BAVC.Key lambda tau N) (Topen : Nat)
    (expand : Counter → Challenge tau N wpow) (encode : (Fin tau → Fin N) → F)
    (ctr : Counter) (opening : Spec.BAVC.Opening lambda tau) :
    attempt key Topen expand encode ctr = .ready opening ↔
      Spec.BAVC.openCommitment key (expand ctr).hidden Topen = .ok opening ∧
      GrindingPassed (expand ctr).grinding ∧ encode (expand ctr).hidden ≠ 0 := by
  unfold attempt
  dsimp only
  cases he : Spec.BAVC.openCommitment key (expand ctr).hidden Topen with
  | error err => cases err <;> simp
  | ok result =>
    simp only
    split <;> simp_all

/-- Legal BAVC inputs exclude the undefined-opening branch of the retry model. -/
theorem attempt_not_undefined {F : Type*} [Zero F] [DecidableEq F]
    {lambda tau N wpow : Nat} (key : Spec.BAVC.Key lambda tau N) (Topen : Nat)
    (expand : Counter → Challenge tau N wpow) (encode : (Fin tau → Fin N) → F)
    (ctr : Counter) (ht : 0 < tau) (err : Spec.BAVC.OpeningError) :
    attempt key Topen expand encode ctr ≠ .undefinedOpening err := by
  have hs := BAVC.openCommitment_source_outcome key (expand ctr).hidden Topen ht
  unfold attempt
  dsimp only
  cases he : Spec.BAVC.openCommitment key (expand ctr).hidden Topen with
  | error error =>
    have hb : error = .boundExceeded := by simpa [BAVC.SourceOutcome, he] using hs
    subst error
    simp
  | ok opening =>
    simp only
    split <;> simp

/-- Every Algorithm-11 return passes the literal Algorithm-12 header check,
using the same expansion and encoding, and contains an actual successful BAVC
opening. The later reconstruction discrepancy is not assumed away. -/
theorem returned_header_and_opening {F : Type*} [Field F] [DecidableEq F]
    {lambda tau N wpow : Nat} (key : Spec.BAVC.Key lambda tau N) (Topen : Nat)
    (expand : Counter → Challenge tau N wpow) (encode : (Fin tau → Fin N) → F)
    (fuel : Nat) (ctr : Counter) (opening : Spec.BAVC.Opening lambda tau)
    (h : openRandomEvaluation key Topen expand encode fuel = .returned ctr opening) :
    checkEvaluationHeader expand encode ctr = some (encode (expand ctr).hidden)⁻¹ ∧
      encode (expand ctr).hidden ≠ 0 ∧
      Spec.BAVC.openCommitment key (expand ctr).hidden Topen = .ok opening := by
  have hr := (observe_returned (attempt key Topen expand encode) fuel 0 ctr opening h).1
  obtain ⟨ho, hg, hd⟩ := (attempt_ready_iff key Topen expand encode ctr opening).mp hr
  exact ⟨by simp [checkEvaluationHeader, hg, hd], hd, ho⟩

/-- The only undefined-operation outcome left for legal BAVC inputs is the
explicitly unprovided counter-overflow behavior. -/
theorem openRandomEvaluation_no_undefined_opening {F : Type*} [Zero F] [DecidableEq F]
    {lambda tau N wpow : Nat} (key : Spec.BAVC.Key lambda tau N) (Topen : Nat)
    (expand : Counter → Challenge tau N wpow) (encode : (Fin tau → Fin N) → F)
    (ht : 0 < tau) (fuel : Nat) (err : Spec.BAVC.OpeningError) :
    openRandomEvaluation key Topen expand encode fuel ≠ .undefined (.undefinedOpening err) := by
  exact observe_no_undefined_opening _
    (fun ctr error => attempt_not_undefined key Topen expand encode ctr ht error) fuel 0 err

/-- No unconditional success guarantee follows merely from the retry loop:
if all expanded challenges encode zero, it never returns an opening. -/
theorem zero_challenges_never_return {F : Type*} [Zero F] [DecidableEq F]
    {lambda tau N wpow : Nat} (key : Spec.BAVC.Key lambda tau N) (Topen : Nat)
    (expand : Counter → Challenge tau N wpow) (encode : (Fin tau → Fin N) → F)
    (hz : ∀ ctr, encode (expand ctr).hidden = 0)
    (fuel : Nat) (ctr : Counter) (opening : Spec.BAVC.Opening lambda tau) :
    openRandomEvaluation key Topen expand encode fuel ≠ .returned ctr opening := by
  intro h
  have hr := (observe_returned (attempt key Topen expand encode) fuel 0 ctr opening h).1
  exact ((attempt_ready_iff key Topen expand encode ctr opening).mp hr).2.2 (hz ctr)

end SDitH.Proofs.BLCRetry
