import SDitH.Proofs.MeanForkCont

/-! The mean-form hybrid of the end-resampled event fork. From a resampled
snapshot world, the first scheme's fork is within twice the remaining fuel
times the per-call bound of the second scheme's: the second branch is
replaced first, from the resampled restored world, then the first branch,
whose continuation is now a fixed game run. -/

namespace SDitH.Proofs.MeanForkCont2

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq ForkRestoreEnd EventRestore SharedResample SignBridge HiddenSlice MeanHybrid ChargeCutExpect
open RunHybrid MeanHybridCont MeanHybridContW MeanForkCont
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
  (hpubLaw : ∀ query : Query, PostLaw resample (sch₂.publicOracle query))
  (E : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) → Bool)

/-- The end-resampled event fork in mean form, for a scheme and a snapshot
with a resampled world. -/
theorem forkEventE_mean (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest
      (Spec.SharedScheme.World lambda s wit rnd) Query Answer)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (hlook : snapshot.world.hashTable snapshot.input = none) (w : GW HashInput Digest lambda s wit rnd)
    (hw : w ∈ (resampleW resample snapshot.world).support) :
    (forkEventE sch adversary E { snapshot with world := w }) true =
      mean (PMF.uniformOfFintype Digest) fun a =>
        mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a)
            { w with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) }
            { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
          mean (resampleW resample r.2) fun w' =>
            mean (finalize (withWorld r.1 w')) fun c =>
              mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
                mean (resampleW resample rw.2) fun w'' =>
                  indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) := by
  obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW snapshot.world w hw
  have hlook' : (setFamily snapshot.world f).hashTable snapshot.input = none := hlook
  have hT : (setFamily snapshot.world f).hashTable = snapshot.world.hashTable := rfl
  have hres' : ∀ w', restore (setFamily snapshot.world f) w' = restore snapshot.world w' := fun _ => rfl
  have hset : ∀ g, setFamily (setFamily snapshot.world f) g = setFamily snapshot.world g := fun _ => rfl
  simp only [forkEventE, hlook', mean_bind_apply, map_true, hT, hres', hset]

include hagree hmono hres hquery hpres hpub hprepInv hupdate hrestore hsignLaw hpubLaw in
/-- The end-resampled event fork hybrid: within twice the remaining fuel
times the per-call bound. -/
theorem forkEventE_le_mean (hsign : SignRunWMean (C := Bool) resample sch₁ sch₂ adversary Good ε B Inv)
    (hEleft : ∀ snapshot' left right g, E snapshot' (some (setFamilyBranch g left, right)) = E snapshot' (some (left, right)))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world) (hB : m + 2 * snapshot.remaining + 2 ≤ B) :
    mean (resampleW resample snapshot.world) (fun w => (forkEventE sch₁ adversary E { snapshot with world := w }) true) ≤
      mean (resampleW resample snapshot.world) (fun w => (forkEventE sch₂ adversary E { snapshot with world := w }) true) +
        2 * snapshot.remaining * ε := by
  cases hlook : snapshot.world.hashTable snapshot.input with
  | some d =>
    refine le_trans (le_of_eq (mean_congr_support _ _ _ fun w hw => ?_)) le_self_add
    obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW snapshot.world w hw
    have hlook' : (setFamily snapshot.world f).hashTable snapshot.input = some d := hlook
    simp only [forkEventE, hlook']
  | none =>
    rw [mean_congr_support _ _ _ (forkEventE_mean adversary E sch₁ snapshot hlook),
      mean_congr_support _ _ _ (forkEventE_mean adversary E sch₂ snapshot hlook), mean_comm]
    conv_rhs => rw [mean_comm, ← mean_add_const]
    refine mean_le_mean _ _ _ fun a _ => ?_
    dsimp only
    set T := Function.update snapshot.world.hashTable snapshot.input (some a) with hTdef
    set tr := { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests } with htr
    -- the inner evaluation after the first branch, for a scheme of the second branch
    set inner : (Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
        Query Answer) → Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
        GW HashInput Digest lambda s wit rnd → ℝ≥0∞ := fun sch r =>
      mean (resampleW resample r.2) fun w' =>
        mean (finalize (withWorld r.1 w')) fun c =>
          mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
            mean (resampleW resample rw.2) fun w'' =>
              indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) with hinner
    rw [← mean_resampleW_update resample snapshot.world T
        (fun y => mean (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
          (inner sch₁)),
      ← mean_resampleW_update resample snapshot.world T
        (fun y => mean (runW sch₂ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
          (inner sch₂))]
    have hX : Inv (m + 1) { snapshot.world with hashTable := T } := hupdate snapshot.world snapshot.input m a hm
    -- step A: the second branch, for every output of the first
    have hA : ∀ y ∈ (resampleW resample { snapshot.world with hashTable := T }).support,
        ∀ r ∈ (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr).support,
        inner sch₁ r ≤ inner sch₂ r + snapshot.remaining * ε := by
      intro y hy r hr
      have hInvr : Inv (m + 1 + snapshot.remaining) r.2 :=
        runW_inv sch₁ sch₂ adversary hagree Inv hmono hquery hpres hpub hprepInv _ _ _ _ _ _ (m + 1) (hres _ _ hX y hy) r hr
      -- the first branch's checked terminal carries the resampled family, which the event ignores
      have hleft : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest
          (Spec.SharedScheme.World lambda s wit rnd) Query Answer),
          inner sch r = mean (finalize r.1) fun c => mean (resampleW resample r.2) fun w' =>
            mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
              mean (resampleW resample rw.2) fun w'' =>
                indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) := by
        intro sch
        simp only [hinner]
        rw [← mean_comm]
        refine mean_congr_support _ _ _ fun w' hw' => ?_
        obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW r.2 w' hw'
        rw [withWorld_setFamily, runW_attempt sch₁ adversary _ _ _ _ _ _ r hr, finalize_setFamilyT, mean_map]
        refine congrArg _ (funext fun c => congrArg _ (funext fun rw => congrArg _ (funext fun w'' => ?_)))
        exact congrArg _ (hEleft _ ⟨a, c⟩ rw.1 f)
      rw [hleft sch₁, hleft sch₂, ← mean_add_const]
      refine mean_le_mean _ _ _ fun c _ => ?_
      have hK : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest
          (Spec.SharedScheme.World lambda s wit rnd) Query Answer),
          mean (resampleW resample r.2) (fun w' =>
            mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
              mean (resampleW resample rw.2) fun w'' =>
                indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1)))) =
          mean (resampleW resample (restore snapshot.world r.2)) (fun y' =>
            mean (freshBranchW sch adversary { snapshot with world := y' }) fun rw =>
              (((resampleW resample rw.2).map fun w'' =>
                E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) true)) := by
        intro sch
        rw [mean_resampleW_restore snapshot.world r.2 (fun y' => mean (freshBranchW sch adversary { snapshot with world := y' })
          fun rw => mean (resampleW resample rw.2) fun w'' =>
            indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))))]
        simp only [map_true]
      rw [hK sch₁, hK sch₂]
      have hInvY : Inv (m + 1 + snapshot.remaining) (restore snapshot.world r.2) :=
        hrestore _ _ _ (hmono _ _ _ (by omega) hm) hInvr
      have h := freshBranchW_le_mean sch₁ sch₂ adversary hagree Good ε B Inv hmono hres hquery hpres hpub hupdate hsignLaw hpubLaw
        hsign { snapshot with world := restore snapshot.world r.2 } hsk (m + 1 + snapshot.remaining) hInvY
        (by show m + 1 + snapshot.remaining + 1 + snapshot.remaining ≤ B; omega)
        (fun rw => (resampleW resample rw.2).map fun w'' =>
          E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1)))
      simpa using h
    -- step B: the first branch, with the second scheme's second branch
    have hB' : mean (resampleW resample { snapshot.world with hashTable := T }) (fun y =>
        mean (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
          (inner sch₂)) ≤
        mean (resampleW resample { snapshot.world with hashTable := T }) (fun y =>
          mean (runW sch₂ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
            (inner sch₂)) + snapshot.remaining * ε := by
      have hF : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest
          (Spec.SharedScheme.World lambda s wit rnd) Query Answer) (y : GW HashInput Digest lambda s wit rnd),
          mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
            (inner sch₂) =
          ((runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr).bind fun r =>
            (resampleW resample r.2).bind fun w' =>
              (finalize (withWorld r.1 w')).bind fun c =>
                (freshBranchW sch₂ adversary { snapshot with world := restore snapshot.world w' }).bind fun rw =>
                  (resampleW resample rw.2).map fun w'' =>
                    E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) true := by
        intro sch y
        simp only [hinner, mean_bind_apply, map_true]
      simp only [hF]
      exact runW_le_runW_mean_cont resample sch₁ sch₂ adversary hagree Good ε B Inv hmono hres hquery hpres hpub hsignLaw hpubLaw
        hsign snapshot.remaining _ _ hsk _ _ _ (m + 1) hX (by omega) _ true
    calc mean (resampleW resample { snapshot.world with hashTable := T }) (fun y =>
            mean (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
              (inner sch₁))
        ≤ mean (resampleW resample { snapshot.world with hashTable := T }) (fun y =>
            mean (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
              (inner sch₂) + snapshot.remaining * ε) :=
          mean_le_mean _ _ _ fun y hy => by
            rw [← mean_add_const]
            exact mean_le_mean _ _ _ fun r hr => hA y hy r hr
      _ = mean (resampleW resample { snapshot.world with hashTable := T }) (fun y =>
            mean (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
              (inner sch₂)) + snapshot.remaining * ε := mean_add_const _ _ _
      _ ≤ (mean (resampleW resample { snapshot.world with hashTable := T }) (fun y =>
            mean (runW sch₂ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
              (inner sch₂)) + snapshot.remaining * ε) + snapshot.remaining * ε := add_le_add hB' le_rfl
      _ = _ := by ring

end
end SDitH.Proofs.MeanForkCont2
