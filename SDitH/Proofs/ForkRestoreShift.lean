import SDitH.Proofs.ForkRestoreLemmas

/-! Shifts and resampling for the restored fork: the run with its final
world obeys the resampling law in mean form; a fresh branch from a world
with entries appended to its history is the branch with its attempt's
history shifted; and the snapshot's world with a family, or restored from
a final world, is a shift of the empty-history base. -/

namespace SDitH.Proofs.ForkRestoreShift

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open SharedResample
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)

/-- The run with its final world obeys the resampling law in mean form. -/
theorem runW_postLaw_mean (hsignLaw : ∀ sk m, PostLaw resample (scheme.sign sk m))
    (hpubLaw : ∀ q, PostLaw resample (scheme.publicOracle q))
    (hprepLaw : ∀ pk m sig, PostLaw resample (scheme.prepareVerification pk m sig))
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : GW HashInput Digest lambda s wit rnd)
    (trace : Trace Message HashInput Query)
    (φ : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → ℝ≥0∞) :
    mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) φ) =
      mean (resampleW resample world) (fun w => mean (runW scheme adversary fuel pk sk state w trace) fun r =>
        mean (resampleW resample r.2) fun w' => φ (withWorld r.1 w', w')) := by
  have h := congrArg (fun p => mean p φ)
    (runW_postLaw resample resample_idem scheme adversary hsignLaw hpubLaw hprepLaw fuel pk sk state world trace)
  simp only [mean_bind, mean_map] at h
  exact h

/-- The fresh branch through the run with its final world. -/
theorem freshBranch_eq
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State) :
    freshBranch scheme adversary snapshot = (PMF.uniformOfFintype Digest).bind fun answer =>
      (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
        { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).bind fun r =>
        (finalize r.1).map fun checked =>
          (⟨answer, checked⟩ : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) := by
  unfold freshBranch continueWith
  refine congrArg _ (funext fun answer => ?_)
  rw [run_eq_runW, PMF.bind_map, PMF.map_bind]
  rfl

/-- A fresh branch from a world with entries appended to its history is the
branch with its attempt's history shifted. -/
theorem freshBranch_shift (hsign : ∀ sk m, ShiftLaw (scheme.sign sk m)) (hpub : ∀ q, ShiftLaw (scheme.publicOracle q))
    (hprep : ∀ pk m sig, ShiftLaw (scheme.prepareVerification pk m sig))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (H : List (Entry (Bits lambda) (Bits lambda))) :
    freshBranch scheme adversary { snapshot with world := shiftG H snapshot.world } =
      (freshBranch scheme adversary snapshot).map (shiftBranch H) := by
  rw [freshBranch_eq, freshBranch_eq, PMF.map_bind]
  refine congrArg _ (funext fun answer => ?_)
  dsimp only
  set W' := shiftG H snapshot.world with hW'
  have hT : W'.hashTable = snapshot.world.hashTable := rfl
  have hw : ∀ T, ({ W' with hashTable := T } : GW HashInput Digest lambda s wit rnd) =
      shiftG H { snapshot.world with hashTable := T } := fun T => rfl
  rw [hT, hw, runW_shift scheme adversary hsign hpub hprep, PMF.bind_map, PMF.map_bind]
  simp only [Function.comp_def]
  refine congrArg _ (funext fun r => ?_)
  rw [finalize_shiftT, PMF.map_comp, PMF.map_comp]
  rfl

omit [Fintype Digest] [Nonempty Digest] in
/-- The world with a family is the shift of its empty-history base by its
history. -/
theorem setFamily_eq_shiftG (W : GW HashInput Digest lambda s wit rnd) (f : Family (Bits lambda) (Bits lambda)) :
    setFamily W f = shiftG W.other.cipherHistory { W with other := { W.other with family := f, cipherHistory := [] } } := by
  simp only [setFamily, shiftG, List.nil_append]

omit [Fintype Digest] [Nonempty Digest] in
/-- The restored world is the shift of the empty-history base by the final
history. -/
theorem restore_eq_shiftG (W final : GW HashInput Digest lambda s wit rnd) :
    restore W final =
      shiftG final.other.cipherHistory { W with other := { W.other with family := final.other.family, cipherHistory := [] } } := by
  simp only [restore, shiftG, List.nil_append]

end
end SDitH.Proofs.ForkRestoreShift
