import SDitH.Spec.IntegerSamplingTrace
import SDitH.Proofs.IntegerSamplingVector
import SDitH.Proofs.PRGSampling

namespace SDitH.Proofs.IntegerSampling

open Spec.IntegerSampling Spec.ByteSampling Spec.DomainSeparation

set_option maxRecDepth 4096

theorem vectorPending_trace_congr {m n : Nat} (src₁ src₂ : Reader)
    (hc : src₁.position = src₂.position) (values : List (Fin m)) (bounded : values.length ≤ n) :
    vectorTrace (vectorPending ⟨values, bounded, src₁⟩) =
      vectorTrace (vectorPending ⟨values, bounded, src₂⟩) := by
  by_cases complete : values.length = n
  · simp only [vectorPending, dif_pos complete, vectorTrace, hc]
    rfl
  · simp only [vectorPending, dif_neg complete, vectorTrace, hc]

theorem vectorStep_rejected (m : Nat) (hm : 0 < m) (n : Nat) (binding : Option Nat)
    (resume : PartialVector m n → VectorObservation m n) (state : PartialVector m n)
    (incomplete : state.values.length ≠ n) (next : Reader)
    (ha : attempt m state.next = .rejected next) :
    vectorStep m hm n binding resume state = resume ⟨state.values, state.bounded, next⟩ := by
  rw [vectorStep, dif_neg incomplete, ha]

theorem vectorStep_bound_accepted (m : Nat) (hm : 0 < m) (n value : Nat)
    (resume : PartialVector m n → VectorObservation m n) (state : PartialVector m n)
    (incomplete : state.values.length ≠ n) (candidate : Candidate)
    (ha : attempt m state.next = .accepted candidate) :
    vectorStep m hm n (some value) resume state =
      resume ⟨state.values ++ [⟨value % m, Nat.mod_lt _ hm⟩],
        by have hb := state.bounded; simp only [List.length_append, List.length_singleton]; omega,
        candidate.next⟩ := by
  rw [vectorStep, dif_neg incomplete, ha]

theorem attempt_rejected_of_not_lt (m : Nat) (src : Reader)
    (h : ¬ (readCandidate src).value < sourceThreshold m) :
    attempt m src = .rejected (advance src 4) := by
  rw [attempt, attemptWith, if_neg h]
  rfl

/-- A single literal step with abstract continuations keeps the proof independent
of the recursive sampler's implementation term. The continuations must already
agree on every possible accumulated prefix after these same four byte reads. -/
theorem vectorStep_trace_congr (m : Nat) (hm : 0 < m) (n : Nat) (binding : Option Nat)
    (resume₁ resume₂ : PartialVector m n → VectorObservation m n)
    (src₁ src₂ : Reader) (hc : src₁.position = src₂.position)
    (hb : readBytes src₁ 4 = readBytes src₂ 4)
    (hresume : ∀ (values : List (Fin m)) (bounded : values.length ≤ n),
      vectorTrace (resume₁ ⟨values, bounded, advance src₁ 4⟩) =
        vectorTrace (resume₂ ⟨values, bounded, advance src₂ 4⟩))
    (values : List (Fin m)) (bounded : values.length ≤ n) :
    vectorTrace (vectorStep m hm n binding resume₁ ⟨values, bounded, src₁⟩) =
      vectorTrace (vectorStep m hm n binding resume₂ ⟨values, bounded, src₂⟩) := by
  by_cases complete : values.length = n
  · rw [vectorStep_finished m hm n binding resume₁ ⟨values, bounded, src₁⟩ complete,
      vectorStep_finished m hm n binding resume₂ ⟨values, bounded, src₂⟩ complete]
    simp only [vectorTrace, hc]
    rfl
  · have hv : (readCandidate src₁).value = (readCandidate src₂).value :=
      congrArg (fun bytes => (word32 bytes).val) hb
    by_cases accepted : (readCandidate src₁).value < sourceThreshold m
    · have ha₁ := (attempt_accepted_iff m src₁ (readCandidate src₁)).mpr ⟨rfl, accepted⟩
      have ha₂ := (attempt_accepted_iff m src₂ (readCandidate src₂)).mpr ⟨rfl, hv ▸ accepted⟩
      cases binding with
      | none =>
        rw [vectorStep_missing m hm n resume₁ ⟨values, bounded, src₁⟩ complete (readCandidate src₁) ha₁,
          vectorStep_missing m hm n resume₂ ⟨values, bounded, src₂⟩ complete (readCandidate src₂) ha₂]
        change VectorTrace.undefinedAssignment values src₁.position (readCandidate src₁).value
          (src₁.position + 4) =
          VectorTrace.undefinedAssignment values src₂.position (readCandidate src₂).value (src₂.position + 4)
        rw [hc, hv]
      | some value =>
        rw [vectorStep_bound_accepted m hm n value resume₁ ⟨values, bounded, src₁⟩ complete (readCandidate src₁) ha₁,
          vectorStep_bound_accepted m hm n value resume₂ ⟨values, bounded, src₂⟩ complete (readCandidate src₂) ha₂]
        exact hresume _ _
    · rw [vectorStep_rejected m hm n binding resume₁ ⟨values, bounded, src₁⟩ complete (advance src₁ 4)
          (attempt_rejected_of_not_lt m src₁ accepted),
        vectorStep_rejected m hm n binding resume₂ ⟨values, bounded, src₂⟩ complete (advance src₂ 4)
          (attempt_rejected_of_not_lt m src₂ (hv ▸ accepted))]
      exact hresume values bounded

/-- Four bytes per observed attempt suffice even when every candidate is
rejected. No comparison of unconsumed infinite tails is required. -/
theorem observeVector_trace_congr (m : Nat) (hm : 0 < m) (n : Nat) (binding : Option Nat)
    (fuel : Nat) (src₁ src₂ : Reader) (hc : src₁.position = src₂.position)
    (hw : ∀ i < 4 * fuel, src₁.stream (src₁.position + i) = src₂.stream (src₂.position + i))
    (values : List (Fin m)) (bounded : values.length ≤ n) :
    vectorTrace (observeVector m hm n binding fuel ⟨values, bounded, src₁⟩) =
      vectorTrace (observeVector m hm n binding fuel ⟨values, bounded, src₂⟩) := by
  induction fuel generalizing src₁ src₂ values with
  | zero => exact vectorPending_trace_congr src₁ src₂ hc values bounded
  | succ fuel ih =>
    have hb : readBytes src₁ 4 = readBytes src₂ 4 := by
      funext i
      exact hw i.val (by have hi := i.isLt; omega)
    apply vectorStep_trace_congr m hm n binding _ _ src₁ src₂ hc hb
    intro current bounded'
    apply ih (advance src₁ 4) (advance src₂ 4) (by simp only [advance, hc]) _ current bounded'
    intro i hi
    simpa only [advance, Nat.add_assoc] using hw (4 + i) (by omega)

theorem sampleVector_trace_congr (m : Nat) (hm : 0 < m) (n : Nat) (binding : Option Nat)
    (fuel : Nat) (src₁ src₂ : Reader) (hc : src₁.position = src₂.position)
    (hw : ∀ i < 4 * fuel, src₁.stream (src₁.position + i) = src₂.stream (src₂.position + i)) :
    vectorTrace (sampleVectorWithBinding m hm n binding fuel src₁) =
      vectorTrace (sampleVectorWithBinding m hm n binding fuel src₂) :=
  observeVector_trace_congr m hm n binding fuel src₁ src₂ hc hw [] (by simp)

/-- Every observed read is covered by an actual successful finite Algorithm-6
request. The finite reader's zero extension is irrelevant within this bound. -/
theorem sampleVector_trace_from_run (category : Spec.FieldRepresentation.Category)
    (variant : Grinding) (size : Spec.PRG.BlockSize)
    (seed : Bits (Spec.FieldRepresentation.width category)) (nbytes : Nat) (out : Vector Byte nbytes)
    (hr : Spec.PRG.run category variant size seed none none nbytes = some out)
    (m : Nat) (hm : 0 < m) (n : Nat) (binding : Option Nat) (fuel : Nat)
    (within : 4 * fuel ≤ nbytes) :
    vectorTrace (sampleVectorWithBinding m hm n binding fuel
      (finiteReader (count := nbytes) (fun i => out[i]))) =
      vectorTrace (sampleVectorWithBinding m hm n binding fuel
        (Spec.PRG.reader category seed (fun _ => false))) := by
  refine sampleVector_trace_congr m hm n binding fuel
    (finiteReader (count := nbytes) (fun i => out[i]))
    (Spec.PRG.reader category seed (fun _ => false)) rfl ?_
  intro i hi
  have hb : i < nbytes := hi.trans_le within
  have ho := PRG.run_output_coordinate category variant size seed none none nbytes out
    (fun _ => false) rfl hr ⟨i, hb⟩
  simpa only [finiteReader, Spec.PRG.reader, Nat.zero_add, dif_pos hb, Fin.getElem_fin] using ho

end SDitH.Proofs.IntegerSampling
