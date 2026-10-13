import SDitH.Proofs.PairRun
import SDitH.Proofs.PruneCompatClosure
import SDitH.Proofs.SignBridge

/-! The pair mass through the fork: an event that, whenever it holds, is
witnessed by every family matching the union of the two branches'
attempt histories has probability at most the pair mass of the second
branch's final world when it runs from the first branch's final history
with the family resampled, which the common form of the fork and the
shift law provide; the run bounds then give the probability from the
snapshot's pair mass and two branches' costs. -/

namespace SDitH.Proofs.PairFork

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher Spec.IdealCipherPairCollision
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq ForkRestoreEnd SharedResample HiddenSlice MeanHybrid PairMass PairOracles PairRun
open SignBridge PruneCompatClosure IdealCipherPairCollision
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)

/-- The attempt's embedded history of a branch, empty otherwise. -/
def attemptHistory (b : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) :
    List (Entry (Bits lambda) (Bits lambda)) :=
  match b.checked.terminal with
  | .attempt a => a.world.other.cipherHistory
  | _ => []

omit [Fintype Digest] [Nonempty Digest] in
theorem attemptHistory_shift (H : List (Entry (Bits lambda) (Bits lambda)))
    (b : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) :
    attemptHistory (shiftBranch H b) ⊆ attemptHistory b ++ H := by
  unfold attemptHistory shiftBranch shiftT
  cases b.checked.terminal <;> simp [shiftG]

omit [Fintype Digest] [Nonempty Digest] in
theorem attemptHistory_setFamily (f : Family (Bits lambda) (Bits lambda))
    (b : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) :
    attemptHistory (setFamilyBranch f b) = attemptHistory b := by
  unfold attemptHistory setFamilyBranch setFamilyT
  cases b.checked.terminal <;> rfl

/-- The fresh branch with its final world is the shift of the branch from
the empty-history base. -/
theorem freshBranchW_shift (hsign : ∀ sk m, ShiftLaw (sch.sign sk m)) (hpub : ∀ q, ShiftLaw (sch.publicOracle q))
    (hprep : ∀ pk m sig, ShiftLaw (sch.prepareVerification pk m sig))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (H : List (Entry (Bits lambda) (Bits lambda))) :
    freshBranchW sch adversary { snapshot with world := shiftG H snapshot.world } =
      (freshBranchW sch adversary snapshot).map fun rw => (shiftBranch H rw.1, shiftG H rw.2) := by
  unfold freshBranchW
  rw [PMF.map_bind]
  refine congrArg _ (funext fun answer => ?_)
  dsimp only
  set W' := shiftG H snapshot.world with hW'
  have hT : W'.hashTable = snapshot.world.hashTable := rfl
  have hw : ∀ T, ({ W' with hashTable := T } : GW HashInput Digest lambda s wit rnd) =
      shiftG H { snapshot.world with hashTable := T } := fun T => rfl
  rw [hT, hw, runW_shift sch adversary hsign hpub hprep, PMF.bind_map, PMF.map_bind]
  simp only [Function.comp_def]
  refine congrArg _ (funext fun r => ?_)
  rw [finalize_shiftT, PMF.map_comp, PMF.map_comp]
  rfl

/-- The attempt of a fresh branch embeds the branch's final world. -/
theorem freshBranchW_attempt
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (rw : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) (h : rw ∈ (freshBranchW sch adversary snapshot).support) :
    attemptHistory rw.1 ⊆ rw.2.other.cipherHistory := by
  unfold freshBranchW at h
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at h
  obtain ⟨answer, -, r, hr, checked, hc, rfl⟩ := h
  have ht := finalize_terminal r.1 checked hc
  have hw := runW_attempt sch adversary _ _ _ _ _ _ r hr
  dsimp only [attemptHistory]
  rw [ht]
  cases hr1 : r.1 with
  | attempt a =>
    rw [hr1] at hw
    simp only [withWorld, Terminal.attempt.injEq] at hw
    have hthis : r.2 = a.world := by simpa using congrArg Attempt.world hw
    dsimp only
    rw [← hthis]
    exact fun _ h => h
  | exhausted t => simp
  | aborted t => simp
  | rejected t => simp

variable (project companion : Bits lambda → Bits lambda) (ε : ℝ≥0∞) (B : Nat)
  (Inv : Nat → GW HashInput Digest lambda s wit rnd → Prop)
  (hmono : ∀ (n m : Nat) (world : GW HashInput Digest lambda s wit rnd), n ≤ m → Inv n world → Inv m world)
  (hres : ∀ (n : Nat) (world : GW HashInput Digest lambda s wit rnd), Inv n world →
    ∀ w ∈ (resampleW resample world).support, Inv n w)
  (hquery : ∀ (world : GW HashInput Digest lambda s wit rnd) (input : HashInput) (n : Nat)
    (r : Digest × (HashInput → Option Digest)), Inv n world →
    r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
  (hpres : ∀ (sk : SecretKey) (message : Message) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
    (r : Signature × GW HashInput Digest lambda s wit rnd), Inv n world →
    r ∈ (sch.sign sk message world).support → Inv (n + 1) r.2)
  (hpub : ∀ (query : Query) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
    (r : Answer × GW HashInput Digest lambda s wit rnd),
    Inv n world → r ∈ (sch.publicOracle query world).support → Inv (n + 1) r.2)
  (hprepInv : ∀ (pk : PublicKey) (message : Message) (signature : Signature) (world : GW HashInput Digest lambda s wit rnd)
    (n : Nat) (r : Option HashInput × GW HashInput Digest lambda s wit rnd), Inv n world →
    r ∈ (sch.prepareVerification pk message signature world).support → Inv (n + 1) r.2)
  (hupdate : ∀ (world : GW HashInput Digest lambda s wit rnd) (input : HashInput) (n : Nat) (d : Digest), Inv n world →
    Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) })
  (hrestore : ∀ (n : Nat) (W wL : GW HashInput Digest lambda s wit rnd), Inv n W → Inv n wL → Inv n (restore W wL))
  (hmatch : ∀ (n : Nat) (world : GW HashInput Digest lambda s wit rnd), Inv n world →
    Matches world.other.family world.other.cipherHistory)
  (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw resample (sch.sign sk message))
  (hpubLaw : ∀ query : Query, PostLaw resample (sch.publicOracle query))
  (hprepLaw : ∀ pk m sig, PostLaw resample (sch.prepareVerification pk m sig))
  (hsignF : ∀ sk m, KeepsFamily (sch.sign sk m)) (hpubF : ∀ q, KeepsFamily (sch.publicOracle q))
  (hprepF : ∀ pk m sig, KeepsFamily (sch.prepareVerification pk m sig))
  (hsignG : ∀ sk m, Grows (sch.sign sk m)) (hpubG : ∀ q, Grows (sch.publicOracle q))
  (hprepG : ∀ pk m sig, Grows (sch.prepareVerification pk m sig))
  (hsignS : ∀ sk m, ShiftLaw (sch.sign sk m)) (hpubS : ∀ q, ShiftLaw (sch.publicOracle q))
  (hprepS : ∀ pk m sig, ShiftLaw (sch.prepareVerification pk m sig))
  (hsignP : ∀ (sk : SecretKey) (message : Message) (world : GW HashInput Digest lambda s wit rnd) (n : Nat),
    Inv n world → n ≤ B →
    mean (resampleW resample world) (fun w => mean (sch.sign sk message w) fun r =>
      pairMass project companion r.2.other.cipherHistory) ≤ pairMass project companion world.other.cipherHistory + ε)
  (hpubP : ∀ (query : Query) (world : GW HashInput Digest lambda s wit rnd) (n : Nat), Inv n world → n ≤ B →
    mean (resampleW resample world) (fun w => mean (sch.publicOracle query w) fun r =>
      pairMass project companion r.2.other.cipherHistory) ≤ pairMass project companion world.other.cipherHistory + ε)
  (hprepP : ∀ (pk : PublicKey) (message : Message) (signature : Signature) (world : GW HashInput Digest lambda s wit rnd)
    (n : Nat), Inv n world → n ≤ B →
    mean (resampleW resample world) (fun w => mean (sch.prepareVerification pk message signature w) fun r =>
      pairMass project companion r.2.other.cipherHistory) ≤ pairMass project companion world.other.cipherHistory + ε)
  (E : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) → Bool)
  (hnone : ∀ snapshot', E snapshot' none = false)
  (hE : ∀ snapshot' left right, E snapshot' (some (left, right)) = true →
    ∀ g : Family (Bits lambda) (Bits lambda), Matches g (attemptHistory right ++ attemptHistory left) →
      Witnessed project companion g (attemptHistory right ++ attemptHistory left))

include hmono hquery hpres hpub hprepInv in
/-- The invariant along the run with its final world. -/
theorem runW_inv' : ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (w : GW HashInput Digest lambda s wit rnd)
    (trace : Trace Message HashInput Query) (n : Nat), Inv n w →
    ∀ r ∈ (runW sch adversary fuel pk sk state w trace).support, Inv (n + fuel) r.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state w trace n hn r hr
    simp only [runW, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simpa using hn
  | succ fuel ih =>
    intro pk sk state w trace n hn r hr
    simp only [runW, PMF.mem_support_bind_iff] at hr
    obtain ⟨action, -, hr⟩ := hr
    cases action with
    | abort =>
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hmono _ _ _ (by omega) hn
    | finish message signature =>
      simp only [PMF.support_map, Set.mem_image] at hr
      obtain ⟨result, hres', rfl⟩ := hr
      exact hmono _ _ _ (by omega) (hprepInv pk message signature w n result hn hres')
    | sign message next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres', hr⟩ := hr
      have := ih pk sk (next result.1) result.2 _ (n + 1) (hpres sk message w n result hn hres') r hr
      exact hmono _ _ _ (by omega) this
    | hash input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres', hr⟩ := hr
      have := ih pk sk (next result.1) _ _ (n + 1) (hquery w input n result hn hres') r hr
      exact hmono _ _ _ (by omega) this
    | query input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres', hr⟩ := hr
      have := ih pk sk (next result.1) result.2 _ (n + 1) (hpub input w n result hn hres') r hr
      exact hmono _ _ _ (by omega) this

include hmono hquery hpres hpub hprepInv hupdate in
/-- The invariant along a fresh branch's final world. -/
theorem freshBranchW_inv
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (n : Nat) (hn : Inv n snapshot.world)
    (rw : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) (h : rw ∈ (freshBranchW sch adversary snapshot).support) :
    Inv (n + 1 + snapshot.remaining) rw.2 := by
  unfold freshBranchW at h
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at h
  obtain ⟨answer, -, r, hr, checked, -, rfl⟩ := h
  exact runW_inv' sch adversary Inv hmono hquery hpres hpub hprepInv snapshot.remaining _ _ _ _ _ (n + 1)
    (hupdate snapshot.world snapshot.input n answer hn) r hr

omit [Fintype Digest] [Nonempty Digest] in
theorem attemptHistory_withWorld (a : Digest) (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (w' : GW HashInput Digest lambda s wit rnd)
    (c : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (hc : c.terminal = withWorld t w') :
    attemptHistory (⟨a, c⟩ : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) ⊆
      w'.other.cipherHistory := by
  unfold attemptHistory
  dsimp only
  rw [hc]
  cases t <;> simp [withWorld]

include hmono hquery hpres hpub hprepInv hupdate hrestore hmatch hsignS hpubS hprepS hE in
/-- The pointwise step: the event on the plain second branch is at most
the pair mass of the shifted final world of the restored second branch. -/
theorem event_le_shifted
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (w' : GW HashInput Digest lambda s wit rnd) (m : Nat) (hm : Inv m snapshot.world) (hw' : Inv m w')
    (hsub : snapshot.world.other.cipherHistory ⊆ w'.other.cipherHistory)
    (left : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (hleft : attemptHistory left ⊆ w'.other.cipherHistory)
    (rw : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd)
    (h : rw ∈ (freshBranchW sch adversary { snapshot with world :=
      { snapshot.world with other := { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }).support) :
    indicator (E { snapshot with world := setFamily snapshot.world w'.other.family }
        (some (left, shiftBranch snapshot.world.other.cipherHistory rw.1))) ≤
      pairMass project companion (shiftG w'.other.cipherHistory rw.2).other.cipherHistory := by
  cases hEv : E { snapshot with world := setFamily snapshot.world w'.other.family }
      (some (left, shiftBranch snapshot.world.other.cipherHistory rw.1)) with
  | false => simp [indicator]
  | true =>
    rw [RandomOracleTrap.indicator_true]
    have hatt := freshBranchW_attempt sch adversary _ rw h
    -- the shifted sample is a sample of the restored branch
    have hmem : (shiftBranch w'.other.cipherHistory rw.1, shiftG w'.other.cipherHistory rw.2) ∈
        (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }).support := by
      have hs := freshBranchW_shift sch adversary hsignS hpubS hprepS { snapshot with world :=
        { snapshot.world with other := { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }
        w'.other.cipherHistory
      simp only at hs
      rw [restore_eq_shiftG, hs, PMF.support_map]
      exact ⟨rw, h, rfl⟩
    have hinv := freshBranchW_inv sch adversary Inv hmono hquery hpres hpub hprepInv hupdate _ m
      (hrestore m snapshot.world w' hm hw') _ hmem
    have hpos : ∃ g : Family (Bits lambda) (Bits lambda),
        Matches g (shiftG w'.other.cipherHistory rw.2).other.cipherHistory :=
      ⟨_, hmatch _ _ hinv⟩
    -- the union is contained in the shifted final history
    have hU : attemptHistory (shiftBranch snapshot.world.other.cipherHistory rw.1) ++ attemptHistory left ⊆
        (shiftG w'.other.cipherHistory rw.2).other.cipherHistory := by
      intro e he
      simp only [shiftG, List.mem_append] at he ⊢
      rcases he with he | he
      · rcases List.mem_append.mp (attemptHistory_shift _ _ he) with he | he
        · exact Or.inl (hatt he)
        · exact Or.inr (hsub he)
      · exact Or.inr (hleft he)
    rw [pairMass_eq_one project companion _ hpos]
    intro g hg
    refine witnessed_mono project companion g _ _ hU ?_
    exact hE _ left _ hEv g fun e he => hg e (hU he)

include hmono hres hquery hpres hpub hprepInv hupdate hrestore hmatch hsignLaw hpubLaw hprepLaw hsignF hpubF hprepF
  hsignG hpubG hprepG hsignS hpubS hprepS hsignP hpubP hprepP hnone hE in
/-- The fork bound: from a resampled snapshot world, the event's
probability is at most the snapshot's pair mass and two branches' costs. -/
theorem fork_pair_bound
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (n : Nat) (hn : Inv n snapshot.world) (hB : n + 2 * (snapshot.remaining + 1) ≤ B) :
    mean (resampleW resample snapshot.world) (fun w =>
        ((forkAt sch adversary { snapshot with world := w }).map (E { snapshot with world := w })) true) ≤
      pairMass project companion snapshot.world.other.cipherHistory + ((2 * snapshot.remaining : Nat) : ℝ≥0∞) * ε := by
  cases hlook : snapshot.world.hashTable snapshot.input with
  | some d =>
    refine (mean_le_const _ _ 0 fun w hw => ?_).trans (zero_le _)
    have hl : w.hashTable snapshot.input = some d := by
      rw [hashTable_of_mem resample snapshot.world w hw]
      exact hlook
    simp only [forkAt, hl, PMF.pure_map, hnone, PMF.pure_apply]
    simp
  | none =>
    rw [shared_eq_common sch adversary E hsignLaw hpubLaw hprepLaw hsignF hpubF hprepF snapshot hlook]
    unfold common
    refine mean_le_const _ _ _ fun a _ => ?_
    set Wa : GW HashInput Digest lambda s wit rnd :=
      { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) } with hWa
    have hWaInv : Inv (n + 1) Wa := hupdate snapshot.world snapshot.input n a hn
    have hWahist : Wa.other.cipherHistory = snapshot.world.other.cipherHistory := rfl
    calc mean (resampleW resample Wa) (fun w =>
            mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) w
                { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
              mean (resampleW resample r.2) fun w' =>
                mean (finalize (withWorld r.1 w')) fun c =>
                  mean (freshBranch sch adversary { snapshot with world := setFamily snapshot.world w'.other.family })
                    fun right =>
                      indicator (E { snapshot with world := setFamily snapshot.world w'.other.family } (some (⟨a, c⟩, right))))
        ≤ mean (resampleW resample Wa) (fun w =>
            mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) w
                { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
              pairMass project companion r.2.other.cipherHistory + (snapshot.remaining : ℝ≥0∞) * ε) := by
          refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
          have hwInv : Inv (n + 1) w := hres _ _ hWaInv w hw
          have hr2 : Inv (n + 1 + snapshot.remaining) r.2 :=
            runW_inv' sch adversary Inv hmono hquery hpres hpub hprepInv _ _ _ _ _ _ _ hwInv r hr
          obtain ⟨new, hnew⟩ := runW_history sch adversary hsignG hpubG hprepG _ _ _ _ _ _ r hr
          have hwhist : w.other.cipherHistory = snapshot.world.other.cipherHistory := history_of_mem_resampleW Wa w hw
          calc mean (resampleW resample r.2) (fun w' =>
                  mean (finalize (withWorld r.1 w')) fun c =>
                    mean (freshBranch sch adversary { snapshot with world := setFamily snapshot.world w'.other.family })
                      fun right =>
                        indicator (E { snapshot with world := setFamily snapshot.world w'.other.family }
                          (some (⟨a, c⟩, right))))
              ≤ mean (resampleW resample r.2) (fun w' =>
                  mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
                    pairMass project companion rw.2.other.cipherHistory) := by
                refine mean_le_mean _ _ _ fun w' hw' => ?_
                have hw'Inv : Inv (n + 1 + snapshot.remaining) w' := hres _ _ hr2 w' hw'
                have hw'hist : w'.other.cipherHistory = new ++ snapshot.world.other.cipherHistory := by
                  rw [history_of_mem_resampleW _ _ hw', hnew, hwhist]
                have hsub : snapshot.world.other.cipherHistory ⊆ w'.other.cipherHistory := by
                  rw [hw'hist]
                  exact List.subset_append_right _ _
                refine mean_le_const _ _ _ fun c hc => ?_
                have hL : freshBranch sch adversary { snapshot with world := setFamily snapshot.world w'.other.family } =
                    (freshBranch sch adversary { snapshot with world := { snapshot.world with other :=
                      { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }).map
                      (shiftBranch snapshot.world.other.cipherHistory) := by
                  rw [setFamily_eq_shiftG]
                  have := freshBranch_shift sch adversary hsignS hpubS hprepS { snapshot with world :=
                    { snapshot.world with other := { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }
                    snapshot.world.other.cipherHistory
                  simp only at this
                  exact this
                have hR : freshBranchW sch adversary { snapshot with world := restore snapshot.world w' } =
                    (freshBranchW sch adversary { snapshot with world := { snapshot.world with other :=
                      { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }).map
                      (fun rw => (shiftBranch w'.other.cipherHistory rw.1, shiftG w'.other.cipherHistory rw.2)) := by
                  rw [restore_eq_shiftG]
                  have := freshBranchW_shift sch adversary hsignS hpubS hprepS { snapshot with world :=
                    { snapshot.world with other := { snapshot.world.other with family := w'.other.family, cipherHistory := [] } } }
                    w'.other.cipherHistory
                  simp only at this
                  exact this
                rw [hL, mean_map, ← freshBranchW_fst, mean_map, hR, mean_map]
                refine mean_le_mean _ _ _ fun rw hrw => ?_
                exact event_le_shifted sch adversary project companion Inv hmono hquery hpres hpub hprepInv hupdate hrestore
                  hmatch hsignS hpubS hprepS E hE snapshot w' (n + 1 + snapshot.remaining) (hmono _ _ _ (by omega) hn) hw'Inv
                  hsub ⟨a, c⟩ (attemptHistory_withWorld a r.1 w' c (finalize_terminal _ c hc)) rw hrw
            _ = mean (resampleW resample (restore snapshot.world r.2)) (fun y =>
                  mean (freshBranchW sch adversary { snapshot with world := y }) fun rw =>
                    pairMass project companion rw.2.other.cipherHistory) :=
                mean_resampleW_restore snapshot.world r.2 (fun y =>
                  mean (freshBranchW sch adversary { snapshot with world := y }) fun rw =>
                    pairMass project companion rw.2.other.cipherHistory)
            _ ≤ pairMass project companion (restore snapshot.world r.2).other.cipherHistory +
                  (snapshot.remaining : ℝ≥0∞) * ε :=
                freshBranchW_pair_bound sch adversary project companion ε B Inv hres hquery hpres hpub hupdate hsignLaw hpubLaw
                  hsignP hpubP hprepP { snapshot with world := restore snapshot.world r.2 } (n + 1 + snapshot.remaining)
                  (hrestore _ _ _ (hmono _ _ _ (by omega) hn) hr2) (by simp only; omega)
            _ = pairMass project companion r.2.other.cipherHistory + (snapshot.remaining : ℝ≥0∞) * ε := rfl
      _ = mean (resampleW resample Wa) (fun w =>
            mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) w
                { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
              pairMass project companion r.2.other.cipherHistory) + (snapshot.remaining : ℝ≥0∞) * ε := by
          simp only [mean_add_const]
      _ ≤ pairMass project companion Wa.other.cipherHistory + (snapshot.remaining : ℝ≥0∞) * ε +
            (snapshot.remaining : ℝ≥0∞) * ε :=
          add_le_add (runW_pair_bound sch adversary project companion ε B Inv hres hquery hpres hpub hsignLaw hpubLaw hsignP
            hpubP hprepP _ _ _ _ _ _ (n + 1) hWaInv (by omega)) le_rfl
      _ = _ := by
          rw [hWahist, add_assoc, ← two_mul, ← mul_assoc]
          push_cast
          ring

end
end SDitH.Proofs.PairFork
