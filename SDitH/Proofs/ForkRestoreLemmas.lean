import SDitH.Proofs.ForkRestore

/-! Supporting facts for the restored fork: the game run only extends the
inner history, a resampled world is the world with its family replaced,
and a branch's embedded history shifts with its attempt's world. -/

namespace SDitH.Proofs.ForkRestoreLemmas

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun HistoryShiftGame CipherResample ForkRestore
open scoped Classical

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}

/-- The game run only extends the inner history. -/
theorem runW_history
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsignG : ∀ sk m, Grows (scheme.sign sk m)) (hpubG : ∀ q, Grows (scheme.publicOracle q))
    (hprepG : ∀ pk m sig, Grows (scheme.prepareVerification pk m sig)) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (w : GW HashInput Digest lambda s wit rnd)
      (trace : Trace Message HashInput Query), ∀ r ∈ (runW scheme adversary fuel pk sk state w trace).support,
      ∃ new, r.2.other.cipherHistory = new ++ w.other.cipherHistory := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state w trace r hr
    simp only [runW, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨[], rfl⟩
  | succ fuel ih =>
    intro pk sk state w trace r hr
    simp only [runW, PMF.mem_support_bind_iff] at hr
    obtain ⟨action, -, hr⟩ := hr
    cases action with
    | abort =>
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨[], rfl⟩
    | finish message signature =>
      simp only [PMF.support_map, Set.mem_image] at hr
      obtain ⟨result, hres, rfl⟩ := hr
      exact hprepG pk message signature w result hres
    | sign message next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres, hr⟩ := hr
      obtain ⟨new₁, h₁⟩ := hsignG sk message w result hres
      obtain ⟨new₂, h₂⟩ := ih pk sk _ _ _ r hr
      exact ⟨new₂ ++ new₁, by rw [h₂, h₁, List.append_assoc]⟩
    | hash input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, -, hr⟩ := hr
      exact ih pk sk _ { w with hashTable := result.2 } _ r hr
    | query input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres, hr⟩ := hr
      obtain ⟨new₁, h₁⟩ := hpubG input w result hres
      obtain ⟨new₂, h₂⟩ := ih pk sk _ _ _ r hr
      exact ⟨new₂ ++ new₁, by rw [h₂, h₁, List.append_assoc]⟩

omit [Fintype Digest] [Nonempty Digest] in
/-- A resampled world is the world with its family replaced. -/
theorem eq_setFamily_of_mem_resampleW (w w' : GW HashInput Digest lambda s wit rnd)
    (hw' : w' ∈ (resampleW resample w).support) : ∃ f, w' = setFamily w f := by
  simp only [resampleW, resample, PMF.map_comp, PMF.support_map] at hw'
  obtain ⟨f, -, rfl⟩ := hw'
  exact ⟨f, rfl⟩

/-- A branch with its attempt's embedded history shifted. -/
def shiftBranch (H : List (Entry (Bits lambda) (Bits lambda)))
    (b : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) :
    Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query :=
  ⟨b.answer, { b.checked with terminal := shiftT H b.checked.terminal }⟩

/-- Finalizing a shifted terminal is finalizing the terminal with the
checked terminal shifted. -/
theorem finalize_shiftT (H : List (Entry (Bits lambda) (Bits lambda)))
    (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) :
    finalize (shiftT H t) = (finalize t).map fun c => { c with terminal := shiftT H c.terminal } := by
  cases t with
  | attempt a =>
    simp only [shiftT, finalize, PMF.map_comp]
    rfl
  | exhausted trace => simp only [shiftT, finalize, PMF.pure_map]
  | aborted trace => simp only [shiftT, finalize, PMF.pure_map]
  | rejected trace => simp only [shiftT, finalize, PMF.pure_map]

end
end SDitH.Proofs.ForkRestoreLemmas
