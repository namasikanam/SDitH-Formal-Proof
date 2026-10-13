import SDitH.Spec.SignatureQuerySelection
import SDitH.Proofs.SignatureReplayConsistency

namespace SDitH.Proofs.SignatureQuerySelection

open Spec.SignatureSecurity Spec.SignatureReplay Spec.SignatureQuerySelection
open scoped Classical ENNReal
noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

theorem record_refines_run
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
    (world : World HashInput Digest Other) (trace : Trace Message HashInput Query) :
    (record scheme adversary fuel pk sk state world trace).map Recorded.terminal =
      run scheme adversary fuel pk sk state world trace := by
  induction fuel generalizing state world trace with
  | zero => simp [record, run, PMF.pure_map]
  | succ fuel ih =>
    simp only [record, run, PMF.map_bind]
    congr 1
    funext action
    cases action with
    | abort => simp [PMF.pure_map]
    | finish message signature => simp only [PMF.map_comp, Function.comp_def]; rfl
    | sign message next =>
      simp only [PMF.map_bind]
      congr 1
      funext result
      exact ih (next result.1) result.2 _
    | hash input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, prepend]
      congr 1
      funext result
      exact ih (next result.1) _ _
    | query input next =>
      simp only [PMF.map_bind]
      congr 1
      funext result
      exact ih (next result.1) result.2 _

theorem finalize_record_refines
    (record : Recorded Message Signature HashInput Digest Other Query) :
    (finalizeRecord record).map CheckedRecord.checked = finalize record.terminal := by
  simp only [finalizeRecord, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

theorem recorded_experiment_refines
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) :
    (recordedExperiment scheme adversary fuel).map CheckedRecord.checked =
      experiment scheme adversary fuel := by
  simp only [recordedExperiment, experiment, terminalLaw, PMF.map_bind,
    finalize_record_refines, PMF.bind_bind]
  congr 1
  funext generated
  congr 1
  funext state
  rw [← record_refines_run scheme adversary fuel generated.1 generated.2.1 state generated.2.2 _]
  rw [PMF.bind_map]
  rfl

theorem record_length_le
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
    (world : World HashInput Digest Other) (trace : Trace Message HashInput Query)
    (out : Recorded Message Signature HashInput Digest Other Query)
    (ho : out ∈ (record scheme adversary fuel pk sk state world trace).support) :
    out.requests.length ≤ fuel := by
  induction fuel generalizing state world trace out with
  | zero =>
    simp only [record, PMF.mem_support_pure_iff] at ho
    subst out
    simp
  | succ fuel ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp ho
    cases action with
    | abort =>
      simp only [PMF.mem_support_pure_iff] at hnext
      subst out
      simp
    | finish message signature =>
      obtain ⟨result, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      subst out
      simp
    | sign message next =>
      obtain ⟨result, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      exact (ih (next result.1) result.2 _ out hrest).trans (Nat.le_succ _)
    | hash input next =>
      obtain ⟨result, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst out
      exact Nat.succ_le_succ (ih (next result.1) _ _ tail ht)
    | query input next =>
      obtain ⟨result, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      exact (ih (next result.1) result.2 _ out hrest).trans (Nat.le_succ _)

theorem selected_empty (index : Nat) (terminal : Terminal Message Signature HashInput Digest Other Query) :
    selectedRecord index ⟨terminal, []⟩ = PMF.pure false := by
  simp only [selectedRecord, finalizeRecord, PMF.map_comp, Function.comp_def, marked,
    List.getElem?_nil, Bool.and_false]
  exact PMF.map_const _ _

theorem selected_prepend_succ (index : Nat) (input : HashInput) (fresh : Bool)
    (out : Recorded Message Signature HashInput Digest Other Query) :
    selectedRecord (index + 1) (prepend input fresh out) = selectedRecord index out := by
  simp only [selectedRecord, finalizeRecord, PMF.map_comp, Function.comp_def, marked,
    prepend, List.getElem?_cons_succ]

theorem selected_prepend_false (input : HashInput)
    (out : Recorded Message Signature HashInput Digest Other Query) :
    selectedRecord 0 (prepend input false out) = PMF.pure false := by
  simp only [selectedRecord, finalizeRecord, PMF.map_comp, Function.comp_def, marked,
    prepend, List.getElem?_cons_zero, Bool.and_false]
  exact PMF.map_const _ _

theorem selected_prepend_true (input : HashInput)
    (out : Recorded Message Signature HashInput Digest Other Query) :
    selectedRecord 0 (prepend input true out) = (finalize out.terminal).map (checkedTarget input) := by
  simp only [selectedRecord, finalizeRecord, PMF.map_comp, Function.comp_def, marked,
    prepend, List.getElem?_cons_zero]
  congr 1
  funext checked
  unfold checkedTarget
  cases checked.terminal <;> rfl

theorem single_fresh_snapshot
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hfresh : snapshot.world.hashTable snapshot.input = none) :
    singleAtCut scheme adversary (.saved snapshot) =
      ((resume scheme adversary snapshot).bind finalize).map (checkedTarget snapshot.input) := by
  have h := congrArg (fun p => p.map (checkedTarget snapshot.input))
    (SignatureReplay.fresh_branch_refines_resume scheme adversary snapshot hfresh)
  simpa only [singleAtCut, hfresh, PMF.map_comp, Function.comp_def, targetWin, checkedTarget] using h

/-- Selecting the indexed fresh request in the recorded execution is exactly
the defined cut/resume single-success experiment, not a postselected oracle law. -/
theorem selected_record_eq_cut
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
    (world : World HashInput Digest Other) (trace : Trace Message HashInput Query) :
    (record scheme adversary fuel pk sk state world trace).bind (selectedRecord index) =
      (cut scheme adversary index fuel pk sk state world trace).bind (singleAtCut scheme adversary) := by
  induction fuel generalizing index state world trace with
  | zero => simp [record, cut, selected_empty, singleAtCut]
  | succ fuel ih =>
    simp only [record, cut, PMF.bind_bind]
    congr 1
    funext action
    cases action with
    | abort => simp [selected_empty, singleAtCut]
    | finish message signature =>
      simp only [PMF.bind_map, Function.comp_def, selected_empty, singleAtCut]
    | sign message next =>
      simp only [PMF.bind_bind]
      congr 1
      funext result
      exact ih index (next result.1) result.2 _
    | query input next =>
      simp only [PMF.bind_bind]
      congr 1
      funext result
      exact ih index (next result.1) result.2 _
    | hash input next =>
      cases index with
      | succ index =>
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, selected_prepend_succ]
        congr 1
        funext result
        exact ih index (next result.1) _ _
      | zero =>
        simp only [PMF.pure_bind]
        cases he : world.hashTable input with
        | some answer =>
          simp only [he, Option.isNone_some, PMF.bind_bind, PMF.bind_map, Function.comp_def,
            selected_prepend_false, PMF.bind_const, singleAtCut]
        | none =>
          rw [single_fresh_snapshot scheme adversary _ he]
          simp only [resume, PMF.bind_bind, PMF.map_bind, PMF.bind_map, Function.comp_def,
            Option.isNone_none, selected_prepend_true]
          congr 1
          funext result
          rw [← record_refines_run scheme adversary fuel pk sk (next result.1) _ _]
          rw [PMF.bind_map]
          rfl

theorem selected_experiment_eq
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (index fuel : Nat) :
    (recordedExperiment scheme adversary fuel).map (marked index) =
      singleExperiment scheme adversary index fuel := by
  simp only [recordedExperiment, PMF.map_bind, singleExperiment, cutExperiment, PMF.bind_bind]
  congr 1
  funext generated
  congr 1
  funext state
  exact selected_record_eq_cut scheme adversary index fuel generated.1 generated.2.1 state generated.2.2 _

end
end SDitH.Proofs.SignatureQuerySelection
