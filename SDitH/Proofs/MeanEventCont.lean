import SDitH.Proofs.MeanForkCont2
import SDitH.Proofs.ChargeCut

/-! The mean-form hybrid of the end-resampled event experiment: from a
resampled key, the first scheme's experiment is within three times the
fuel times the per-call bounds of the second scheme's, the cut run
contributing the fuel and the fork twice the fuel. -/

namespace SDitH.Proofs.MeanEventCont

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq ForkRestoreEnd EventRestore SharedResample SignBridge HiddenSlice MeanHybrid ChargeCutExpect
open RunHybrid MeanHybridCont MeanHybridContW MeanForkCont MeanForkCont2 CutHybridGen EventHybrid
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (ε : ℝ≥0∞) (B : Nat)
  (Inv : Nat → GW HashInput Digest lambda s wit rnd → Prop)
  (hmono : ∀ (n m : Nat) (world : GW HashInput Digest lambda s wit rnd), n ≤ m → Inv n world → Inv m world)
  (hres : ∀ (n : Nat) (world : GW HashInput Digest lambda s wit rnd), Inv n world →
    ∀ w ∈ (resampleW resample world).support, Inv n w)
  (hquery : ∀ (world : GW HashInput Digest lambda s wit rnd) (input : HashInput) (n : Nat)
    (r : Digest × (HashInput → Option Digest)), Inv n world →
    r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
  (hpres : ∀ (sk : SecretKey) (message : Message) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
    (r : Signature × GW HashInput Digest lambda s wit rnd), Inv n world →
    r ∈ (sch₁.sign sk message world).support → Inv (n + 1) r.2)
  (hpres₂ : ∀ (sk : SecretKey) (message : Message) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
    (r : Signature × GW HashInput Digest lambda s wit rnd), Inv n world →
    r ∈ (sch₂.sign sk message world).support → Inv (n + 1) r.2)
  (hpub : ∀ (query : Query) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
    (r : Answer × GW HashInput Digest lambda s wit rnd),
    Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
  (hprepInv : ∀ (pk : PublicKey) (message : Message) (signature : Signature) (world : GW HashInput Digest lambda s wit rnd)
    (n : Nat) (r : Option HashInput × GW HashInput Digest lambda s wit rnd), Inv n world →
    r ∈ (sch₂.prepareVerification pk message signature world).support → Inv (n + 1) r.2)
  (hupdate : ∀ (world : GW HashInput Digest lambda s wit rnd) (input : HashInput) (n : Nat) (d : Digest), Inv n world →
    Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) })
  (hrestore : ∀ (n : Nat) (W wL : GW HashInput Digest lambda s wit rnd), Inv n W → Inv n wL → Inv n (restore W wL))
  (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw resample (sch₁.sign sk message))
  (hsignLaw₂ : ∀ (sk : SecretKey) (message : Message), PostLaw resample (sch₂.sign sk message))
  (hpubLaw : ∀ query : Query, PostLaw resample (sch₂.publicOracle query))
  (E : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) → Bool)

/-- The fork evaluation after a cut: nothing on an ended run, the
end-resampled event fork at a saved snapshot. -/
def eventBranch (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer) :
    Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State → PMF Bool
  | .ended _ => PMF.pure false
  | .saved snapshot => forkEventE sch adversary E snapshot

/-- The end-resampled event experiment through the fork evaluation. -/
theorem eventExpE_eq_branch (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest
    (Spec.SharedScheme.World lambda s wit rnd) Query Answer) (index fuel : Nat) :
    eventExpE sch adversary E index fuel = (cutExperiment sch adversary index fuel).bind (eventBranch adversary E sch) := by
  unfold eventExpE
  refine congrArg _ (funext fun c => ?_)
  cases c <;> rfl

include hagree hmono hres hquery hpres hpres₂ hpub hprepInv hupdate hrestore hsignLaw hsignLaw₂ hpubLaw in
/-- The end-resampled event experiment hybrid in mean form. -/
theorem eventExpE_le_mean
    (hkeygen : sch₁.keygen = sch₁.keygen.bind fun g => (resampleW resample g.2.2).map fun w => (g.1, g.2.1, w))
    (hgood : ∀ generated ∈ sch₁.keygen.support, Good generated.2.1)
    (hinit : ∀ generated ∈ sch₁.keygen.support, Inv 0 generated.2.2)
    (hsignCut : SignCutMean (C := Bool) resample sch₁ sch₂ adversary Good ε B Inv)
    (hsignRunW : SignRunWMean (C := Bool) resample sch₁ sch₂ adversary Good ε B Inv)
    (hEleft : ∀ snapshot' left right g, E snapshot' (some (setFamilyBranch g left, right)) = E snapshot' (some (left, right)))
    (index fuel : Nat) (hB : 3 * fuel + 2 ≤ B) :
    (eventExpE sch₁ adversary E index fuel) true ≤
      (eventExpE sch₂ adversary E index fuel) true + (fuel * ε + 2 * fuel * ε) := by
  rw [eventExpE_eq_branch, eventExpE_eq_branch]
  unfold cutExperiment
  rw [← hagree.keygen, hkeygen]
  simp only [PMF.bind_bind, mean_bind_apply, mean_map]
  rw [← mean_add_const]
  refine mean_le_mean _ _ _ fun g hg => ?_
  dsimp only
  rw [mean_comm]
  conv_rhs => rw [mean_comm, ← mean_add_const]
  refine mean_le_mean _ _ _ fun state _ => ?_
  have h1 := cut_le_cut_mean_cont resample sch₁ sch₂ adversary hagree Good ε B Inv hmono hres hquery hpres hpub hsignLaw hpubLaw
    hsignCut index fuel g.1 g.2.1 (hgood g hg) state g.2.2 ⟨[], [], []⟩ 0 (hinit g hg) (by omega)
    (eventBranch adversary E sch₁) true
  simp only [mean_bind_apply] at h1
  have h2 : mean (resampleW resample g.2.2) (fun w =>
        mean (cut sch₂ adversary index fuel g.1 g.2.1 state w ⟨[], [], []⟩) fun c => (eventBranch adversary E sch₁ c) true) ≤
      mean (resampleW resample g.2.2) (fun w =>
        mean (cut sch₂ adversary index fuel g.1 g.2.1 state w ⟨[], [], []⟩) fun c => (eventBranch adversary E sch₂ c) true) +
        2 * fuel * ε := by
    rw [← mean_bind, cut_postLaw resample resample_idem sch₂ adversary hsignLaw₂ hpubLaw]
    conv_rhs => rw [← mean_bind, cut_postLaw resample resample_idem sch₂ adversary hsignLaw₂ hpubLaw]
    simp only [mean_bind]
    rw [← mean_add_const]
    refine mean_le_mean _ _ _ fun w hw => ?_
    rw [← mean_add_const]
    refine mean_le_mean _ _ _ fun c hc => ?_
    cases c with
    | ended t =>
      simp only [resampleCut, mean_pure, eventBranch]
      exact le_self_add
    | saved snapshot =>
      simp only [resampleCut, mean_map, eventBranch]
      have hrem : snapshot.remaining ≤ fuel :=
        ForkEventUnion.cut_remaining_le sch₂ adversary index fuel _ _ state _ _ _ hc snapshot rfl
      have hkey : snapshot.secretKey = g.2.1 :=
        cut_saved_secretKey sch₂ adversary index fuel _ _ state _ _ _ hc snapshot rfl
      have hsk' : Good snapshot.secretKey := by rw [hkey]; exact hgood g hg
      have hsup : Inv (0 + fuel) snapshot.world :=
        cut_saved_gen Inv hmono hquery sch₂ adversary hpres₂ hpub index fuel _ _ state _ _ 0 (hres 0 g.2.2 (hinit g hg) w hw) _ hc
          snapshot rfl
      refine (forkEventE_le_mean sch₁ sch₂ adversary hagree Good ε B Inv hmono hres hquery hpres hpub hprepInv hupdate
        hrestore hsignLaw hpubLaw E hsignRunW hEleft snapshot hsk' (0 + fuel) hsup (by omega)).trans ?_
      exact add_le_add le_rfl (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr hrem)) le_rfl)
  calc _ ≤ _ := h1
    _ ≤ _ := add_le_add h2 le_rfl
    _ = _ := by ring

end
end SDitH.Proofs.MeanEventCont
