import SDitH.Spec.ConcreteChallenges
import SDitH.Proofs.IntegerSamplingVector
import SDitH.Proofs.HashPrimitives
import SDitH.Proofs.CipherGrinding
import SDitH.Spec.Parameters

namespace SDitH.Proofs.ConcreteChallenges

open Spec.ConcreteChallenges Spec.DomainSeparation Spec.FieldRepresentation Spec.ByteSampling

set_option maxRecDepth 4096

theorem evaluationInput_length {lambda : Nat} (encoding : CounterEncoding)
    (digest : Bits (2 * lambda)) (ctr : Spec.BLCRetry.Counter) :
    (evaluationInput encoding digest ctr).length = 2 * lambda + 32 := by
  simp [evaluationInput]

theorem evaluationInput_eq_iff {lambda : Nat} (encoding : CounterEncoding)
    (first second : Bits (2 * lambda)) (a b : Spec.BLCRetry.Counter) :
    evaluationInput encoding first a = evaluationInput encoding second b ↔
      first = second ∧ encoding a = encoding b := by
  constructor
  · intro h
    obtain ⟨hd, hc⟩ := List.append_inj h (by simp)
    exact ⟨List.ofFn_injective hd, List.ofFn_injective hc⟩
  · rintro ⟨rfl, he⟩
    simp only [evaluationInput, he]

/-- Counter factoring changes the initial XOF input whenever its supplied
encoding is injective. This asserts nothing about equality of SHAKE outputs. -/
theorem initial_input_counter_dependent {lambda : Nat} (encoding : CounterEncoding)
    (hinj : Function.Injective encoding) (digest : Bits (2 * lambda))
    (a b : Spec.BLCRetry.Counter) (hne : a ≠ b) :
    evaluationInput encoding digest a ≠ evaluationInput encoding digest b := by
  intro he
  exact hne (hinj ((evaluationInput_eq_iff encoding digest digest a b).mp he).2)

theorem cipherInput_length {lambda : Nat} (encoding : CounterEncoding)
    (digest : Bits (2 * lambda)) (ctr : Spec.BLCRetry.Counter) (ciphertexts : Bits lambda × Bits lambda) :
    (cipherInput encoding digest ctr ciphertexts).length = 4 * lambda + 32 := by
  simp only [cipherInput, List.length_append, evaluationInput_length, List.length_ofFn]
  omega

theorem finishHash_returned_iff {tau kappa wpow : Nat} (count : Nat) (enough : wpow ≤ 8 * count)
    (integers : Spec.IntegerSampling.VectorObservation (2 ^ kappa) tau)
    (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (next : Reader) :
    finishHash count enough integers = .returned challenge next ↔
      ∃ values cursor, integers = .returned values cursor ∧
        challenge = ⟨(fun e => values[e]), (sampleBinary cursor wpow count enough).value⟩ ∧
        next = advance cursor count := by
  cases integers <;> simp [finishHash, eq_comm, sampleBinary]

theorem finishHash_replicate {tau kappa wpow : Nat} (count : Nat) (enough : wpow ≤ 8 * count)
    (index : Fin (2 ^ kappa)) (src : Reader) :
    finishHash count enough (.returned (Vector.replicate tau index) src) =
      .returned ⟨(fun _ => index), (sampleBinary src wpow count enough).value⟩ (advance src count) := by
  simp [finishHash, sampleBinary]

theorem advance_add (src : Reader) (a b : Nat) : advance (advance src a) b = advance src (a + b) := by
  cases src
  simp [advance, Nat.add_assoc]

theorem finishHash_empty {kappa wpow : Nat} (count : Nat) (enough : wpow ≤ 8 * count) (src : Reader) :
    finishHash (kappa := kappa) count enough (.returned #v[] src) =
      .returned ⟨Fin.elim0, (sampleBinary src wpow count enough).value⟩ (advance src count) := by
  have hindex : (fun e : Fin 0 => (#v[] : Vector (Fin (2 ^ kappa)) 0)[e]) = Fin.elim0 := by
    funext e
    exact Fin.elim0 e
  change EvaluationObservation.returned
    ⟨(fun e => (#v[] : Vector (Fin (2 ^ kappa)) 0)[e]), (sampleBinary src wpow count enough).value⟩
    (advance src count) = _
  rw [hindex]

theorem hashEvaluation_missing (category : Category) (tau kappa wpow : Nat)
    (ht : 0 < tau) (hk : kappa ≤ 32) (encoding : CounterEncoding)
    (digest : Bits (2 * width category)) (ctr : Spec.BLCRetry.Counter)
    (fuel count : Nat) (enough : wpow ≤ 8 * count) :
    let src := Spec.SHAKE.reader category (evaluationInput encoding digest ctr)
    hashEvaluation category tau kappa wpow encoding digest ctr (fuel + 1) count enough =
      .undefinedIntegerAssignment ⟨[], by simp, src⟩ (Spec.IntegerSampling.readCandidate src) := by
  dsimp only
  unfold hashEvaluation hashEvaluationWithBinding
  dsimp only
  rw [show Spec.IntegerSampling.sampleVectorWithBinding (2 ^ kappa) (pow_pos (by decide) _)
      tau none (fuel + 1) (Spec.SHAKE.reader category (evaluationInput encoding digest ctr)) =
      Spec.IntegerSampling.sampleVector (2 ^ kappa) (pow_pos (by decide) _) tau (fuel + 1)
        (Spec.SHAKE.reader category (evaluationInput encoding digest ctr)) from rfl]
  rw [IntegerSampling.sampleVector_power_missing kappa hk tau fuel ht]
  rfl

theorem hashEvaluation_no_return (category : Category) (tau kappa wpow : Nat) (ht : 0 < tau)
    (encoding : CounterEncoding) (digest : Bits (2 * width category)) (ctr : Spec.BLCRetry.Counter)
    (fuel count : Nat) (enough : wpow ≤ 8 * count)
    (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (next : Reader) :
    hashEvaluation category tau kappa wpow encoding digest ctr fuel count enough ≠
      .returned challenge next := by
  intro h
  obtain ⟨values, cursor, hi, _, _⟩ := (finishHash_returned_iff count enough _ challenge next).mp h
  exact IntegerSampling.sampleVector_unbound_no_return (2 ^ kappa) (pow_pos (by decide) _)
    tau fuel ht _ values cursor hi

/-- A supplied fixed B yields constant hidden indices. Its actual grinding
bits begin after 4*tau bytes, not after packed kappa-bit indices. -/
theorem hashEvaluation_bound_result (category : Category) (tau kappa wpow : Nat)
    (hk : kappa ≤ 32) (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (ctr : Spec.BLCRetry.Counter) (binding count : Nat) (enough : wpow ≤ 8 * count) :
    hashEvaluationWithBinding category tau kappa wpow encoding digest ctr (some binding)
      tau count enough = .returned
      ⟨(fun _ => ⟨binding % (2 ^ kappa), Nat.mod_lt _ (pow_pos (by decide) _)⟩),
        (fun j => Spec.SHAKE.bitStream category (evaluationInput encoding digest ctr) (32 * tau + j.val))⟩
      (advance (Spec.SHAKE.reader category (evaluationInput encoding digest ctr)) (4 * tau + count)) := by
  unfold hashEvaluationWithBinding
  dsimp only
  rw [IntegerSampling.sampleVector_power_complete kappa hk tau binding]
  rw [finishHash_replicate, advance_add]
  have hg : (sampleBinary (advance (Spec.SHAKE.reader category (evaluationInput encoding digest ctr))
      (4 * tau)) wpow count enough).value =
      (fun j => Spec.SHAKE.bitStream category (evaluationInput encoding digest ctr) (32 * tau + j.val)) := by
    funext j
    rw [SHAKE.sampleBinary_reader]
    have he : 8 * (4 * tau) + j.val = 32 * tau + j.val := by omega
    rw [he]
  rw [hg]

theorem hashEvaluation_empty (category : Category) (kappa wpow : Nat) (encoding : CounterEncoding)
    (digest : Bits (2 * width category)) (ctr : Spec.BLCRetry.Counter)
    (fuel count : Nat) (enough : wpow ≤ 8 * count) :
    hashEvaluation category 0 kappa wpow encoding digest ctr fuel count enough =
      .returned ⟨Fin.elim0,
        (fun j => Spec.SHAKE.bitStream category (evaluationInput encoding digest ctr) j.val)⟩
        (advance (Spec.SHAKE.reader category (evaluationInput encoding digest ctr)) count) := by
  unfold hashEvaluation hashEvaluationWithBinding
  dsimp only
  rw [IntegerSampling.sampleVector_empty, finishHash_empty]
  have hg : (sampleBinary (Spec.SHAKE.reader category (evaluationInput encoding digest ctr))
      wpow count enough).value =
      (fun j => Spec.SHAKE.bitStream category (evaluationInput encoding digest ctr) j.val) := by
    funext j
    simpa [Spec.ByteSampling.advance, Spec.SHAKE.reader] using
      SHAKE.sampleBinary_reader category (evaluationInput encoding digest ctr) 0 wpow count enough j
  rw [hg]

theorem readCipherMaterial_coordinates (category : Category) (encoding : CounterEncoding)
    (digest : Bits (2 * width category)) (ctr : Spec.BLCRetry.Counter) :
    (∀ j, (readCipherMaterial category encoding digest ctr).value j =
      Spec.SHAKE.byteStream category (evaluationInput encoding digest ctr) j.val) ∧
    (readCipherMaterial category encoding digest ctr).next.position = 4 * width category := by
  simp [readCipherMaterial, readBytes, advance, Spec.SHAKE.reader]

/-- Conditional size comparison: four lambda-bit windows do not exhaust the
printed 4*lambda-byte read. This does not choose the missing material parser. -/
theorem four_windows_not_full_read (category : Category) :
    4 * width category ≠ 8 * (4 * width category) := by
  cases category <;> decide

theorem cipher_after_material_calls (category : Category) (mapping : CounterEncoding)
    (ctr : Spec.BLCRetry.Counter) (material : Spec.CipherGrinding.Material (width category)) :
    (cipherAfterMaterial category mapping ctr material).ciphertexts =
      (Spec.CipherPrimitives.encStar category (Spec.CipherGrinding.prepareKey false material.k0)
        (Spec.CipherGrinding.preparePlaintext (mapping ctr) material.p0),
       Spec.CipherPrimitives.encStar category (Spec.CipherGrinding.prepareKey true material.k1)
        (Spec.CipherGrinding.preparePlaintext (mapping ctr) material.p1)) ∧
    (∀ j, (cipherAfterMaterial category mapping ctr material).xorValue j = Bool.xor
      ((cipherAfterMaterial category mapping ctr material).ciphertexts.1 j)
      ((cipherAfterMaterial category mapping ctr material).ciphertexts.2 j)) :=
  ⟨rfl, fun _ => rfl⟩

/-- Even supplied all-zero grinding does not omit the printed index expansion.
The precise undefined assignment is reached on its fresh SHAKE stream. -/
theorem cipherAfterExtraction_missing (category : Category) (tau kappa wpow : Nat)
    (ht : 0 < tau) (hk : kappa ≤ 32) (encoding : CounterEncoding)
    (digest : Bits (2 * width category)) (ctr : Spec.BLCRetry.Counter)
    (state : ExtractionBoundary (width category)) (grinding : Bits wpow) (fuel : Nat) :
    let src := Spec.SHAKE.reader category (cipherInput encoding digest ctr state.ciphertexts)
    cipherAfterExtraction category tau kappa wpow encoding digest ctr state grinding none (fuel + 1) =
      .undefinedIntegerAssignment ⟨[], by simp, src⟩ (Spec.IntegerSampling.readCandidate src) := by
  dsimp only
  unfold cipherAfterExtraction
  dsimp only
  change finishCipher grinding
      (Spec.IntegerSampling.sampleVector (2 ^ kappa) (pow_pos (by decide) _) tau (fuel + 1) _) = _
  rw [IntegerSampling.sampleVector_power_missing kappa hk tau fuel ht]
  rfl

theorem cipherAfterExtraction_bound_result (category : Category) (tau kappa wpow : Nat)
    (hk : kappa ≤ 32) (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (ctr : Spec.BLCRetry.Counter) (state : ExtractionBoundary (width category))
    (grinding : Bits wpow) (binding : Nat) :
    cipherAfterExtraction category tau kappa wpow encoding digest ctr state grinding (some binding) tau =
      .returned ⟨(fun _ => ⟨binding % (2 ^ kappa), Nat.mod_lt _ (pow_pos (by decide) _)⟩), grinding⟩
        (advance (Spec.SHAKE.reader category (cipherInput encoding digest ctr state.ciphertexts)) (4 * tau)) := by
  unfold cipherAfterExtraction
  dsimp only
  rw [IntegerSampling.sampleVector_power_complete kappa hk tau binding]
  simp [finishCipher]

theorem batching_layout (category : Category) (order : Spec.FieldBytes.ByteOrder category)
    (r w count₁ count₂ : Nat)
    (h₁ : Spec.Batching.blockCount r (width category) * Spec.FieldBytes.byteCount category ≤ count₁)
    (h₂ : w * Spec.FieldBytes.byteCount category ≤ count₂) (digest : Bits (2 * width category)) :
    (batching category order r w count₁ count₂ h₁ h₂ digest).value =
      ((fun i => Spec.FieldBytes.decode category order (fun j =>
        Spec.SHAKE.byteStream category (List.ofFn digest) (i.val * Spec.FieldBytes.byteCount category + j.val))),
       (fun i => Spec.FieldBytes.decode category order (fun j =>
        Spec.SHAKE.byteStream category (List.ofFn digest) (count₁ + (i.val * Spec.FieldBytes.byteCount category + j.val))))) ∧
    (batching category order r w count₁ count₂ h₁ h₂ digest).next.position = count₁ + count₂ :=
  ByteSampling.expandBatching_layout _ _ _ _ _ _ h₁ h₂ _

/-- The two actual calls use disjoint byte packs and stay inside their
specified consumed-byte intervals. This is not statistical independence. -/
theorem batching_byte_ranges (category : Category) (r w count₁ count₂ : Nat)
    (h₁ : Spec.Batching.blockCount r (width category) * Spec.FieldBytes.byteCount category ≤ count₁)
    (h₂ : w * Spec.FieldBytes.byteCount category ≤ count₂)
    (i : Fin (Spec.Batching.blockCount r (width category))) (j : Fin (Spec.FieldBytes.byteCount category))
    (i' : Fin w) (j' : Fin (Spec.FieldBytes.byteCount category)) :
    i.val * Spec.FieldBytes.byteCount category + j.val < count₁ ∧
    count₁ ≤ count₁ + (i'.val * Spec.FieldBytes.byteCount category + j'.val) ∧
    count₁ + (i'.val * Spec.FieldBytes.byteCount category + j'.val) < count₁ + count₂ := by
  have hi := Nat.mul_le_mul_right (Spec.FieldBytes.byteCount category) i.isLt
  have hi' := Nat.mul_le_mul_right (Spec.FieldBytes.byteCount category) i'.isLt
  have hj := j.isLt
  have hj' := j'.isLt
  simp only [Nat.succ_mul] at hi hi'
  omega

theorem submitted_index_ranges :
    ∀ p ∈ Spec.hashProofParameters ++ Spec.cipherProofParameters, 0 < p.tau ∧ p.kappa ≤ 32 := by
  decide

end SDitH.Proofs.ConcreteChallenges
