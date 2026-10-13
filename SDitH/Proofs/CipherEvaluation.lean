import SDitH.Spec.CipherEvaluation
import SDitH.Proofs.ConcreteChallenges

namespace SDitH.Proofs.CipherEvaluation

open Spec.CipherEvaluation Spec.ConcreteChallenges Spec.DomainSeparation
open Spec.FieldRepresentation Spec.ByteSampling

theorem finishCipher_returned_iff {tau kappa wpow : Nat} (grinding : Bits wpow)
    (integers : Spec.IntegerSampling.VectorObservation (2 ^ kappa) tau)
    (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (next : Reader) :
    finishCipher grinding integers = .returned challenge next ↔
      ∃ values, integers = .returned values next ∧
        challenge = ⟨(fun e => values[e]), grinding⟩ := by
  cases integers <;> simp [finishCipher, eq_comm, and_comm]

theorem afterExtraction_no_return (category : Category) (tau kappa wpow : Nat) (ht : 0 < tau)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : Spec.BLCRetry.Counter) (state : ExtractionBoundary (width category))
    (grinding : Bits wpow) (fuel : Nat)
    (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (next : Reader) :
    cipherAfterExtraction category tau kappa wpow encoding digest counter state grinding none fuel ≠
      .returned challenge next := by
  intro h
  obtain ⟨values, hi, _⟩ := (finishCipher_returned_iff grinding _ challenge next).mp h
  exact IntegerSampling.sampleVector_unbound_no_return (2 ^ kappa) (pow_pos (by decide) _)
    tau fuel ht _ values next hi

theorem afterExtraction_returned_stable (category : Category) (tau kappa wpow : Nat)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : Spec.BLCRetry.Counter) (state : ExtractionBoundary (width category))
    (grinding : Bits wpow) (binding : Option Nat) (fuel extra : Nat)
    (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (next : Reader)
    (h : cipherAfterExtraction category tau kappa wpow encoding digest counter state grinding
      binding fuel = .returned challenge next) :
    cipherAfterExtraction category tau kappa wpow encoding digest counter state grinding
      binding (fuel + extra) = .returned challenge next := by
  obtain ⟨values, hi, hc⟩ := (finishCipher_returned_iff grinding _ challenge next).mp h
  apply (finishCipher_returned_iff grinding _ challenge next).mpr
  exact ⟨values, IntegerSampling.observeVector_returned_stable (2 ^ kappa) (pow_pos (by decide) _)
    tau binding fuel extra _ values next hi, hc⟩

/-- A real return exposes the material parser, counter map and xor extraction,
and the actual final SHAKE integer sample. No output of a missing stage can
be substituted for these equations. -/
theorem evaluate_returned_iff (category : Category) (tau kappa wpow : Nat)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : Spec.BLCRetry.Counter) (bindings : Bindings category wpow) (fuel : Nat)
    (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (next : Reader) :
    evaluateWithBindings category tau kappa wpow encoding digest counter bindings fuel =
      .ok (.returned challenge next) ↔
    ∃ parse mapping extract,
      bindings.materialParser = some parse ∧ bindings.counterMap = some mapping ∧
      bindings.extraction = some extract ∧
      let state := cipherAfterMaterial category mapping counter
        (parse (readCipherMaterial category encoding digest counter).value)
      ∃ values, Spec.IntegerSampling.sampleVectorWithBinding (2 ^ kappa) (pow_pos (by decide) _)
          tau bindings.integerValue fuel
          (Spec.SHAKE.reader category (cipherInput encoding digest counter state.ciphertexts)) =
          .returned values next ∧ challenge = ⟨(fun e => values[e]), extract state.xorValue⟩ := by
  cases hp : bindings.materialParser <;> cases hm : bindings.counterMap <;>
    cases he : bindings.extraction <;>
    simp [evaluateWithBindings, afterParsed, hp, hm, he, cipherAfterExtraction,
      finishCipher_returned_iff]

theorem evaluate_missing_material (category : Category) (tau kappa wpow : Nat)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : Spec.BLCRetry.Counter) (fuel : Nat) :
    evaluate category tau kappa wpow encoding digest counter fuel =
      .error (.materialParse (readCipherMaterial category encoding digest counter)) := rfl

theorem evaluate_missing_counter_map (category : Category) (tau kappa wpow : Nat)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : Spec.BLCRetry.Counter) (parse : MaterialParser category)
    (extraction : Option (Bits (width category) → Bits wpow)) (binding : Option Nat) (fuel : Nat) :
    evaluateWithBindings category tau kappa wpow encoding digest counter
      ⟨some parse, none, extraction, binding⟩ fuel =
      .error (.counterMap (parse (readCipherMaterial category encoding digest counter).value)) := rfl

theorem evaluate_missing_extraction (category : Category) (tau kappa wpow : Nat)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : Spec.BLCRetry.Counter) (parse : MaterialParser category) (mapping : CounterEncoding)
    (binding : Option Nat) (fuel : Nat) :
    evaluateWithBindings category tau kappa wpow encoding digest counter
      ⟨some parse, some mapping, none, binding⟩ fuel =
      .error (.extraction (cipherAfterMaterial category mapping counter
        (parse (readCipherMaterial category encoding digest counter).value))) := rfl

/-- Missing B prevents a challenge return even after all preceding source
interpretations have been supplied, for any finite integer observation. -/
theorem evaluate_unbound_no_return (category : Category) (tau kappa wpow : Nat) (ht : 0 < tau)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : Spec.BLCRetry.Counter) (bindings : Bindings category wpow)
    (hb : bindings.integerValue = none) (fuel : Nat)
    (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (next : Reader) :
    evaluateWithBindings category tau kappa wpow encoding digest counter bindings fuel ≠
      .ok (.returned challenge next) := by
  intro h
  obtain ⟨parse, mapping, extract, _, _, _, values, hi, _⟩ :=
    (evaluate_returned_iff category tau kappa wpow encoding digest counter bindings fuel challenge next).mp h
  rw [hb] at hi
  exact IntegerSampling.sampleVector_unbound_no_return (2 ^ kappa) (pow_pos (by decide) _)
    tau fuel ht _ values next hi

theorem evaluate_returned_stable (category : Category) (tau kappa wpow : Nat)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : Spec.BLCRetry.Counter) (bindings : Bindings category wpow) (fuel extra : Nat)
    (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (next : Reader)
    (h : evaluateWithBindings category tau kappa wpow encoding digest counter bindings fuel =
      .ok (.returned challenge next)) :
    evaluateWithBindings category tau kappa wpow encoding digest counter bindings (fuel + extra) =
      .ok (.returned challenge next) := by
  obtain ⟨parse, mapping, extract, hp, hm, he, values, hi, hc⟩ :=
    (evaluate_returned_iff category tau kappa wpow encoding digest counter bindings fuel challenge next).mp h
  apply (evaluate_returned_iff category tau kappa wpow encoding digest counter bindings
    (fuel + extra) challenge next).mpr
  exact ⟨parse, mapping, extract, hp, hm, he, values,
    IntegerSampling.observeVector_returned_stable (2 ^ kappa) (pow_pos (by decide) _)
      tau bindings.integerValue fuel extra _ values next hi, hc⟩

/-- With the preceding interpretations supplied, the exact missing integer
read occurs on the fresh final SHAKE input, including both actual ciphertexts. -/
theorem evaluate_missing_integer (category : Category) (tau kappa wpow : Nat)
    (ht : 0 < tau) (hk : kappa ≤ 32) (encoding : CounterEncoding)
    (digest : Bits (2 * width category)) (counter : Spec.BLCRetry.Counter)
    (parse : MaterialParser category) (mapping : CounterEncoding)
    (extract : Bits (width category) → Bits wpow) (fuel : Nat) :
    let state := cipherAfterMaterial category mapping counter
      (parse (readCipherMaterial category encoding digest counter).value)
    let src := Spec.SHAKE.reader category (cipherInput encoding digest counter state.ciphertexts)
    evaluateWithBindings category tau kappa wpow encoding digest counter
      ⟨some parse, some mapping, some extract, none⟩ (fuel + 1) =
      .ok (.undefinedIntegerAssignment ⟨[], by simp, src⟩ (Spec.IntegerSampling.readCandidate src)) := by
  dsimp only
  unfold evaluateWithBindings afterParsed
  dsimp only
  rw [ConcreteChallenges.cipherAfterExtraction_missing category tau kappa wpow ht hk]

theorem evaluate_bound_result (category : Category) (tau kappa wpow : Nat)
    (hk : kappa ≤ 32) (encoding : CounterEncoding)
    (digest : Bits (2 * width category)) (counter : Spec.BLCRetry.Counter)
    (parse : MaterialParser category) (mapping : CounterEncoding)
    (extract : Bits (width category) → Bits wpow) (binding : Nat) :
    let state := cipherAfterMaterial category mapping counter
      (parse (readCipherMaterial category encoding digest counter).value)
    evaluateWithBindings category tau kappa wpow encoding digest counter
      ⟨some parse, some mapping, some extract, some binding⟩ tau =
      .ok (.returned
        ⟨(fun _ => ⟨binding % (2 ^ kappa), Nat.mod_lt _ (pow_pos (by decide) _)⟩), extract state.xorValue⟩
        (advance (Spec.SHAKE.reader category (cipherInput encoding digest counter state.ciphertexts)) (4 * tau))) := by
  dsimp only
  unfold evaluateWithBindings afterParsed
  dsimp only
  rw [ConcreteChallenges.cipherAfterExtraction_bound_result category tau kappa wpow hk]

end SDitH.Proofs.CipherEvaluation
