import SDitH.Spec.CipherBLCRetry
import SDitH.Proofs.CipherEvaluation
import SDitH.Proofs.PartialBLCRetry

namespace SDitH.Proofs.CipherBLCRetry

open Spec.CipherBLCRetry Spec.CipherEvaluation Spec.ConcreteChallenges Spec.DomainSeparation

variable {F : Type*} [Zero F] [DecidableEq F] {lambda tau kappa wpow : Nat}

theorem observe_partial (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat) (counter : Spec.BLCRetry.Counter) :
    observe key Topen (fun ctr => .ok (expand ctr)) encode fuel counter =
      .ok (Spec.PartialBLCRetry.observe key Topen expand encode fuel counter) := by
  induction fuel generalizing counter with
  | zero => rfl
  | succ fuel ih =>
    have he : step key Topen (fun ctr => .ok (expand ctr)) encode counter =
        .ok (Spec.PartialBLCRetry.step key Topen expand encode counter) := rfl
    rw [observe, he, Spec.PartialBLCRetry.observe]
    cases hs : Spec.PartialBLCRetry.step key Topen expand encode counter with
    | expansionPending state => rfl
    | undefinedExpansion state candidate => rfl
    | decided decision => cases decision with
      | again next => exact ih next
      | done result opening => rfl
      | undefined fault => rfl

theorem step_decided_iff (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → Except (Boundary lambda) (EvaluationObservation tau kappa wpow))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (counter : Spec.BLCRetry.Counter)
    (out : Spec.BLCRetry.Step (Spec.BAVC.Opening lambda tau)) :
    step key Topen expand encode counter = .ok (.decided out) ↔
      ∃ challenge cursor, expand counter = .ok (.returned challenge cursor) ∧
        Spec.BLCRetry.step (Spec.BLCRetry.attempt key Topen (fun _ => challenge) encode) counter = out := by
  cases he : expand counter with
  | error fault => simp [step, he]
  | ok observation => cases observation <;> simp [step, he, Spec.PartialBLCRetry.step]

/-- Every returned opening retains actual successful cipher expansion at its
reported counter. Missing source interpretations cannot be bypassed by retry. -/
theorem observe_returned (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → Except (Boundary lambda) (EvaluationObservation tau kappa wpow))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat)
    (start result : Spec.BLCRetry.Counter) (opening : Spec.BAVC.Opening lambda tau)
    (h : observe key Topen expand encode fuel start = .ok (.returned result opening)) :
    start.val ≤ result.val ∧ ∃ challenge cursor,
      expand result = .ok (.returned challenge cursor) ∧
      Spec.BAVC.openCommitment key challenge.hidden Topen = .ok opening ∧
      Spec.BLCRetry.GrindingPassed challenge.grinding ∧ encode challenge.hidden ≠ 0 := by
  induction fuel generalizing start with
  | zero => simp [observe] at h
  | succ fuel ih =>
    cases hs : step key Topen expand encode start with
    | error fault => simp [observe, hs] at h
    | ok inner => cases inner with
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
          simp only [observe, hs, Except.ok.injEq, Spec.PartialBLCRetry.Observation.returned.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨rfl, ha⟩ := (BLCRetry.step_done_iff
            (Spec.BLCRetry.attempt key Topen (fun _ => challenge) encode) start counter value).mp hd
          obtain ⟨ho, hg, hn⟩ := (BLCRetry.attempt_ready_iff key Topen (fun _ => challenge) encode
            start value).mp ha
          exact ⟨le_rfl, challenge, cursor, he, ho, hg, hn⟩
        | undefined fault => simp [observe, hs] at h

theorem observe_returned_stable (key : Spec.BAVC.Key lambda tau (2 ^ kappa)) (Topen : Nat)
    (expand : Spec.BLCRetry.Counter → Except (Boundary lambda) (EvaluationObservation tau kappa wpow))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel extra : Nat)
    (start result : Spec.BLCRetry.Counter) (opening : Spec.BAVC.Opening lambda tau)
    (h : observe key Topen expand encode fuel start = .ok (.returned result opening)) :
    observe key Topen expand encode (fuel + extra) start = .ok (.returned result opening) := by
  induction fuel generalizing start with
  | zero => simp [observe] at h
  | succ fuel ih =>
    cases hs : step key Topen expand encode start with
    | error fault => simp [observe, hs] at h
    | ok inner => cases inner with
      | expansionPending state => simp [observe, hs] at h
      | undefinedExpansion state candidate => simp [observe, hs] at h
      | decided decision => cases decision with
        | again next =>
          simp only [observe, hs] at h
          simpa only [Nat.succ_add, observe, hs] using ih next h
        | done counter value => simpa only [Nat.succ_add, observe, hs] using h
        | undefined fault => simp [observe, hs] at h

theorem openLiteral_missing (category : Spec.FieldRepresentation.Category) (tau kappa wpow : Nat)
    (key : Spec.BAVC.Key (Spec.FieldRepresentation.width category) tau (2 ^ kappa))
    (Topen : Nat) (encoding : CounterEncoding) (digest : Bits (2 * Spec.FieldRepresentation.width category))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel : Nat) :
    openLiteral category tau kappa wpow key Topen encoding digest encode innerFuel (outerFuel + 1) =
      .error (0, .materialParse (readCipherMaterial category encoding digest 0)) := rfl

theorem open_unbound_no_return (category : Spec.FieldRepresentation.Category) (tau kappa wpow : Nat)
    (ht : 0 < tau) (key : Spec.BAVC.Key (Spec.FieldRepresentation.width category) tau (2 ^ kappa))
    (Topen : Nat) (encoding : CounterEncoding) (digest : Bits (2 * Spec.FieldRepresentation.width category))
    (bindings : Bindings category wpow) (hb : bindings.integerValue = none)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel : Nat)
    (counter : Spec.BLCRetry.Counter) (opening : Spec.BAVC.Opening (Spec.FieldRepresentation.width category) tau) :
    openWithBindings category tau kappa wpow key Topen encoding digest bindings encode innerFuel outerFuel ≠
      .ok (.returned counter opening) := by
  intro h
  obtain ⟨_, challenge, cursor, he, _⟩ := observe_returned key Topen _ encode outerFuel 0 counter opening h
  exact CipherEvaluation.evaluate_unbound_no_return category tau kappa wpow ht encoding digest counter
    bindings hb innerFuel challenge cursor he

theorem open_missing_integer (category : Spec.FieldRepresentation.Category) (tau kappa wpow : Nat)
    (ht : 0 < tau) (hk : kappa ≤ 32)
    (key : Spec.BAVC.Key (Spec.FieldRepresentation.width category) tau (2 ^ kappa))
    (Topen : Nat) (encoding : CounterEncoding) (digest : Bits (2 * Spec.FieldRepresentation.width category))
    (parse : MaterialParser category) (mapping : CounterEncoding)
    (extract : Bits (Spec.FieldRepresentation.width category) → Bits wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel : Nat) :
    let state := cipherAfterMaterial category mapping 0
      (parse (readCipherMaterial category encoding digest 0).value)
    let src := Spec.SHAKE.reader category (cipherInput encoding digest 0 state.ciphertexts)
    openWithBindings category tau kappa wpow key Topen encoding digest
      ⟨some parse, some mapping, some extract, none⟩ encode (innerFuel + 1) (outerFuel + 1) =
      .ok (.undefinedExpansion 0 ⟨[], by simp, src⟩ (Spec.IntegerSampling.readCandidate src)) := by
  dsimp only
  rw [openWithBindings, observe, step, CipherEvaluation.evaluate_missing_integer category tau kappa wpow ht hk]
  rfl

end SDitH.Proofs.CipherBLCRetry
