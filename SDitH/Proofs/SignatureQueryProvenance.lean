import SDitH.Proofs.SignatureQuerySelection

/-! A winning table-present forgery has an adversarial request that was fresh
when made. Honest signing calls on other messages cannot supply that entry.
This is proved for the recorded execution, not imposed as an oracle contract. -/

namespace SDitH.Proofs.SignatureQueryProvenance

open Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureQuerySelection
open scoped Classical ENNReal
noncomputable section

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

theorem run_attempt_properties
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) (pk : PublicKey) (secret : PublicKey × SecretKey) (state : State)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (trace : Trace Message (HashInput PublicKey Message Payload) Query)
    (a : Attempt Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (hout : Terminal.attempt a ∈ (run (scheme components) adversary fuel pk secret state world trace).support) :
    trace.signingRequests ⊆ a.trace.signingRequests ∧ a.input.message = a.message := by
  induction fuel generalizing state world trace with
  | zero => simp [run] at hout
  | succ fuel ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | abort => simp at hnext
    | finish message signature =>
      obtain ⟨prepared, hp, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      obtain ⟨result, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      subst prepared
      cases hh : result.1 with
      | none => simp [hh] at he
      | some payload =>
        simp only [hh, Option.map_some, Terminal.attempt.injEq] at he
        subst a
        exact ⟨List.Subset.refl _, rfl⟩
    | sign message next =>
      obtain ⟨result, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨hsub, hmessage⟩ := ih (next result.1) result.2 _ hrest
      exact ⟨fun m hm => hsub (List.mem_cons_of_mem _ hm), hmessage⟩
    | hash input next =>
      obtain ⟨result, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      exact ih (next result.1) { world with hashTable := result.2 }
        { trace with hashRequests := input :: trace.hashRequests } hrest
    | query input next =>
      obtain ⟨result, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      exact ih (next result.1) result.2
        { trace with publicRequests := input :: trace.publicRequests } hrest

theorem recorded_attempt_run
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) (pk : PublicKey) (secret : PublicKey × SecretKey) (state : State)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (trace : Trace Message (HashInput PublicKey Message Payload) Query)
    (out : Recorded Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (hout : out ∈ (record (scheme components) adversary fuel pk secret state world trace).support)
    (a : Attempt Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (ha : out.terminal = .attempt a) :
    Terminal.attempt a ∈ (run (scheme components) adversary fuel pk secret state world trace).support := by
  rw [← SignatureQuerySelection.record_refines_run]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨out, hout, ha⟩

theorem signing_entry_origin
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (secret : PublicKey × SecretKey) (message : Message)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (result : Signature Digest Body × World (HashInput PublicKey Message Payload) Digest Other)
    (hr : result ∈ ((scheme components).sign secret message world).support)
    (q : HashInput PublicKey Message Payload) (hq : (result.2.hashTable q).isSome = true) :
    (world.hashTable q).isSome = true ∨ q.message = message := by
  obtain ⟨answer, hanswer⟩ := Option.isSome_iff_exists.mp hq
  obtain ⟨prepared, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨hashResult, hhash, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨opened, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst result
  rcases AbstractSignature.oracle_lookup_origin world.hashTable
    ⟨secret.1, message, prepared.1⟩ hashResult hhash q answer hanswer with he | hold
  · exact Or.inr (congrArg HashInput.message he)
  · exact Or.inl (Option.isSome_iff_exists.mpr ⟨answer, hold⟩)

/-- An output table entry was present initially, arose from a genuinely fresh
adversarial request in this execution, or belongs to a logged signed message. -/
theorem recorded_entry_origin
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) (pk : PublicKey) (secret : PublicKey × SecretKey) (state : State)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (trace : Trace Message (HashInput PublicKey Message Payload) Query)
    (out : Recorded Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (hout : out ∈ (record (scheme components) adversary fuel pk secret state world trace).support)
    (a : Attempt Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (ha : out.terminal = .attempt a)
    (q : HashInput PublicKey Message Payload) (hq : (a.world.hashTable q).isSome = true) :
    (world.hashTable q).isSome = true ∨ (q, true) ∈ out.requests ∨ q.message ∈ a.trace.signingRequests := by
  induction fuel generalizing state world trace out with
  | zero =>
    simp only [record, PMF.mem_support_pure_iff] at hout
    subst out
    cases ha
  | succ fuel ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | abort =>
      simp only [PMF.mem_support_pure_iff] at hnext
      subst out
      cases ha
    | finish message signature =>
      obtain ⟨prepared, hp, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      obtain ⟨result, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      subst prepared
      subst out
      cases hh : result.1 with
      | none => simp [hh] at ha
      | some payload =>
        simp only [hh, Option.map_some, Terminal.attempt.injEq] at ha
        subst a
        exact Or.inl hq
    | sign message next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      rcases ih (next result.1) result.2 _ out hrest ha with hold | hrequest | hsign
      · rcases signing_entry_origin components secret message world result hr q hold with hold | he
        · exact Or.inl hold
        · have hrun := recorded_attempt_run components adversary fuel pk secret (next result.1) result.2 _ out hrest a ha
          have hs := (run_attempt_properties components adversary fuel pk secret (next result.1) result.2 _ a hrun).1
          exact Or.inr (Or.inr (by rw [he]; exact hs List.mem_cons_self))
      · exact Or.inr (Or.inl hrequest)
      · exact Or.inr (Or.inr hsign)
    | hash input next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst out
      rcases ih (next result.1) _ _ tail ht ha with hold | hrequest | hsign
      · obtain ⟨answer, hanswer⟩ := Option.isSome_iff_exists.mp hold
        rcases AbstractSignature.oracle_lookup_origin world.hashTable input result hr q answer hanswer with heq | hold
        · subst q
          cases hf : world.hashTable input with
          | some old => exact Or.inl (by simp)
          | none => exact Or.inr (Or.inl (by simp [prepend]))
        · exact Or.inl (Option.isSome_iff_exists.mpr ⟨answer, hold⟩)
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hrequest))
      · exact Or.inr (Or.inr hsign)
    | query input next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨output, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst result
      exact ih (next output.1) { world with other := output.2 }
        { trace with publicRequests := input :: trace.publicRequests } out hrest ha

/-- For every supported table-present winning execution, at least one eligible
index is below the action budget and names a fresh query at its final input. -/
theorem present_winner_has_mark
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat)
    (out : CheckedRecord Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (ho : out ∈ (recordedExperiment (scheme components) adversary fuel).support)
    (hw : out.checked.wins = true) (hp : out.checked.inputWasPresent = true) :
    ∃ index : Fin fuel, marked index.val out = true := by
  obtain ⟨generated, hg, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp ho
  obtain ⟨keys, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hg
  subst generated
  obtain ⟨state, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨recorded, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨checked, hc, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst out
  obtain ⟨a, ha, hchecked, hfresh, hpresent⟩ :=
    SignatureSecurity.finalize_winning_attempt recorded.terminal checked hc hw
  have hrun := recorded_attempt_run components adversary fuel keys.1 (keys.1, keys.2.1)
    state _ _ recorded hr a ha
  have hmessage := (run_attempt_properties components adversary fuel keys.1 (keys.1, keys.2.1)
    state _ _ a hrun).2
  have htable : (a.world.hashTable a.input).isSome = true := hpresent ▸ hp
  have horigin := recorded_entry_origin components adversary fuel keys.1 (keys.1, keys.2.1)
    state _ _ recorded hr a ha a.input htable
  have hrequest : (a.input, true) ∈ recorded.requests := by
    rcases horigin with hnone | hquery | hsign
    · simp at hnone
    · exact hquery
    · exact False.elim (hfresh (hmessage ▸ hsign))
  obtain ⟨index, hget⟩ := List.mem_iff_getElem?.mp hrequest
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hget
  have hlength := SignatureQuerySelection.record_length_le (scheme components) adversary fuel
    keys.1 (keys.1, keys.2.1) state _ _ recorded hr
  refine ⟨⟨index, hlt.trans_le hlength⟩, ?_⟩
  simpa [marked, hchecked, hget] using hw

end
end SDitH.Proofs.SignatureQueryProvenance
