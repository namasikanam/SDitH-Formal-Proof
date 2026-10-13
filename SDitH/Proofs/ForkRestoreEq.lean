import SDitH.Proofs.ForkRestoreShift
import SDitH.Proofs.SignBridge
import SDitH.Proofs.HiddenSlice
import SDitH.Proofs.MeanHybrid

/-! The shared and restored event forks agree from a resampled snapshot
world. The shared fork runs both branches from the same world; the
restored event fork runs the first branch with its final world, resamples
the family given its final history, finalizes the first branch with that
world, and runs the second branch from the snapshot's tables with that
family and history. For an event insensitive to the second branch's
history suffix and evaluated at the snapshot with the resampled family,
the two have the same probability: the first branch's start is the
snapshot's world with the output's family, so the second branch is a
function of the first's output and the resampling law applies, and the
restored second branch differs from the shared one only by a history
shift. -/

namespace SDitH.Proofs.ForkRestoreEq

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift SharedResample SignBridge HiddenSlice MeanHybrid ChargeCutExpect
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (E : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) → Bool)

/-- The restored event fork. -/
def forkEventR (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query State) : PMF Bool :=
  match snapshot.world.hashTable snapshot.input with
  | some _ => PMF.pure (E snapshot none)
  | none => (PMF.uniformOfFintype Digest).bind fun answer =>
      (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
        { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).bind fun r =>
      (resampleW resample r.2).bind fun w' =>
        (finalize (withWorld r.1 w')).bind fun checked =>
          (freshBranch scheme adversary { snapshot with world := restore snapshot.world w' }).map fun right =>
            E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨answer, checked⟩, right))

omit [Fintype Digest] [Nonempty Digest] in
/-- The probability of a decided event under a mapped distribution. -/
theorem map_true {α : Type*} (p : PMF α) (h : α → Bool) : (p.map h) true = mean p fun a => indicator (h a) :=
  RandomOracleTrap.map_true_eq p h

/-- The common form of both forks. -/
def common (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query State) : ℝ≥0∞ :=
  mean (PMF.uniformOfFintype Digest) fun a =>
    mean (resampleW resample
        { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) }) fun w =>
      mean (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) w
          { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        mean (resampleW resample r.2) fun w' =>
          mean (finalize (withWorld r.1 w')) fun c =>
            mean (freshBranch scheme adversary { snapshot with world := setFamily snapshot.world w'.other.family }) fun right =>
              indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨a, c⟩, right)))

/-- The shared fork from a resampled snapshot world has the common form. -/
theorem shared_eq_common (hsignLaw : ∀ sk m, PostLaw resample (scheme.sign sk m))
    (hpubLaw : ∀ q, PostLaw resample (scheme.publicOracle q))
    (hprepLaw : ∀ pk m sig, PostLaw resample (scheme.prepareVerification pk m sig))
    (hsignF : ∀ sk m, KeepsFamily (scheme.sign sk m)) (hpubF : ∀ q, KeepsFamily (scheme.publicOracle q))
    (hprepF : ∀ pk m sig, KeepsFamily (scheme.prepareVerification pk m sig))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (hlook : snapshot.world.hashTable snapshot.input = none) :
    mean (resampleW resample snapshot.world) (fun w =>
        ((forkAt scheme adversary { snapshot with world := w }).map (E { snapshot with world := w })) true) =
      common scheme adversary E snapshot := by
  have hpt : ∀ w ∈ (resampleW resample snapshot.world).support,
      ((forkAt scheme adversary { snapshot with world := w }).map (E { snapshot with world := w })) true =
      mean (PMF.uniformOfFintype Digest) fun a =>
        mean (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a)
            { w with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) }
            { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
          mean (finalize r.1) fun c =>
            mean (freshBranch scheme adversary { snapshot with world := setFamily snapshot.world r.2.other.family }) fun right =>
              indicator (E { snapshot with world := setFamily snapshot.world r.2.other.family } (some (⟨a, c⟩, right))) := by
    intro w hw
    obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW snapshot.world w hw
    have hlook' : (setFamily snapshot.world f).hashTable snapshot.input = none := hlook
    have hT : (setFamily snapshot.world f).hashTable = snapshot.world.hashTable := rfl
    simp only [forkAt, hlook']
    rw [map_true, mean_bind]
    conv_lhs => enter [1]; rw [freshBranch_eq]
    simp only [mean_bind, mean_map, hT]
    refine congrArg _ (funext fun a => ?_)
    refine mean_congr_support _ _ _ fun r hr => ?_
    have hfam : r.2.other.family = f := runW_family scheme adversary hsignF hpubF hprepF _ _ _ _ _ _ r hr
    rw [hfam]
  rw [mean_congr_support _ _ _ hpt, mean_comm]
  unfold common
  refine congrArg _ (funext fun a => ?_)
  rw [mean_resampleW_update resample snapshot.world (Function.update snapshot.world.hashTable snapshot.input (some a)),
    ← mean_resampleW_update resample snapshot.world (Function.update snapshot.world.hashTable snapshot.input (some a))
      (fun w => mean (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) w
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
          mean (finalize r.1) fun c =>
            mean (freshBranch scheme adversary { snapshot with world := setFamily snapshot.world r.2.other.family }) fun right =>
              indicator (E { snapshot with world := setFamily snapshot.world r.2.other.family } (some (⟨a, c⟩, right)))),
    runW_postLaw_mean scheme adversary hsignLaw hpubLaw hprepLaw,
    mean_resampleW_update resample snapshot.world (Function.update snapshot.world.hashTable snapshot.input (some a))]

/-- The restored event fork from a resampled snapshot world has the common
form, for an event insensitive to the second branch's history suffix. -/
theorem restored_eq_common (hsignG : ∀ sk m, Grows (scheme.sign sk m)) (hpubG : ∀ q, Grows (scheme.publicOracle q))
    (hprepG : ∀ pk m sig, Grows (scheme.prepareVerification pk m sig))
    (hsignS : ∀ sk m, ShiftLaw (scheme.sign sk m)) (hpubS : ∀ q, ShiftLaw (scheme.publicOracle q))
    (hprepS : ∀ pk m sig, ShiftLaw (scheme.prepareVerification pk m sig))
    (hE : ∀ snapshot' left right H, E snapshot' (some (left, shiftBranch H right)) = E snapshot' (some (left, right)))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (hlook : snapshot.world.hashTable snapshot.input = none) :
    mean (resampleW resample snapshot.world) (fun w => (forkEventR scheme adversary E { snapshot with world := w }) true) =
      common scheme adversary E snapshot := by
  have hpt : ∀ w ∈ (resampleW resample snapshot.world).support,
      (forkEventR scheme adversary E { snapshot with world := w }) true =
      mean (PMF.uniformOfFintype Digest) fun a =>
        mean (runW scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a)
            { w with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) }
            { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
          mean (resampleW resample r.2) fun w' =>
            mean (finalize (withWorld r.1 w')) fun c =>
              mean (freshBranch scheme adversary { snapshot with world := restore snapshot.world w' }) fun right =>
                indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨a, c⟩, right))) := by
    intro w hw
    obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW snapshot.world w hw
    have hlook' : (setFamily snapshot.world f).hashTable snapshot.input = none := hlook
    have hT : (setFamily snapshot.world f).hashTable = snapshot.world.hashTable := rfl
    have hres : ∀ w', restore (setFamily snapshot.world f) w' = restore snapshot.world w' := fun w' => rfl
    have hset : ∀ g, setFamily (setFamily snapshot.world f) g = setFamily snapshot.world g := fun g => rfl
    simp only [forkEventR, hlook', mean_bind_apply, map_true, hT, hres, hset]
  rw [mean_congr_support _ _ _ hpt, mean_comm]
  unfold common
  refine congrArg _ (funext fun a => ?_)
  rw [mean_resampleW_update resample snapshot.world (Function.update snapshot.world.hashTable snapshot.input (some a))]
  refine mean_congr_support _ _ _ fun w hw => mean_congr_support _ _ _ fun r hr => mean_congr_support _ _ _ fun w' hw' =>
    congrArg _ (funext fun c => ?_)
  obtain ⟨new, hnew⟩ := runW_history scheme adversary hsignG hpubG hprepG _ _ _ _ _ _ r hr
  have hwhist : w.other.cipherHistory = snapshot.world.other.cipherHistory := history_of_mem_resampleW _ _ hw
  have hw'hist : w'.other.cipherHistory = new ++ snapshot.world.other.cipherHistory := by
    rw [history_of_mem_resampleW _ _ hw', hnew]
    exact congrArg _ hwhist
  rw [restore_eq_shiftG, setFamily_eq_shiftG, hw'hist]
  have hL := freshBranch_shift scheme adversary hsignS hpubS hprepS
    { snapshot with world := { snapshot.world with other := { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }
    (new ++ snapshot.world.other.cipherHistory)
  have hR := freshBranch_shift scheme adversary hsignS hpubS hprepS
    { snapshot with world := { snapshot.world with other := { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }
    snapshot.world.other.cipherHistory
  simp only at hL hR
  rw [hL, hR, mean_map, mean_map]
  simp only [hE]

/-- The shared and restored event forks agree from a resampled snapshot
world. -/
theorem fork_restore_eq (hsignLaw : ∀ sk m, PostLaw resample (scheme.sign sk m))
    (hpubLaw : ∀ q, PostLaw resample (scheme.publicOracle q))
    (hprepLaw : ∀ pk m sig, PostLaw resample (scheme.prepareVerification pk m sig))
    (hsignF : ∀ sk m, KeepsFamily (scheme.sign sk m)) (hpubF : ∀ q, KeepsFamily (scheme.publicOracle q))
    (hprepF : ∀ pk m sig, KeepsFamily (scheme.prepareVerification pk m sig))
    (hsignG : ∀ sk m, Grows (scheme.sign sk m)) (hpubG : ∀ q, Grows (scheme.publicOracle q))
    (hprepG : ∀ pk m sig, Grows (scheme.prepareVerification pk m sig))
    (hsignS : ∀ sk m, ShiftLaw (scheme.sign sk m)) (hpubS : ∀ q, ShiftLaw (scheme.publicOracle q))
    (hprepS : ∀ pk m sig, ShiftLaw (scheme.prepareVerification pk m sig))
    (hE : ∀ snapshot' left right H, E snapshot' (some (left, shiftBranch H right)) = E snapshot' (some (left, right)))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State) :
    mean (resampleW resample snapshot.world) (fun w =>
        ((forkAt scheme adversary { snapshot with world := w }).map (E { snapshot with world := w })) true) =
      mean (resampleW resample snapshot.world) (fun w => (forkEventR scheme adversary E { snapshot with world := w }) true) := by
  cases hlook : snapshot.world.hashTable snapshot.input with
  | some d =>
    refine mean_congr_support _ _ _ fun w hw => ?_
    obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW snapshot.world w hw
    have hlook' : (setFamily snapshot.world f).hashTable snapshot.input = some d := hlook
    simp only [forkAt, forkEventR, hlook', PMF.pure_map]
  | none =>
    rw [shared_eq_common scheme adversary E hsignLaw hpubLaw hprepLaw hsignF hpubF hprepF snapshot hlook,
      restored_eq_common scheme adversary E hsignG hpubG hprepG hsignS hpubS hprepS hE snapshot hlook]

end
end SDitH.Proofs.ForkRestoreEq
