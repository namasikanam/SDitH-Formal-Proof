import SDitH.Proofs.MeanCutCompat
import SDitH.Proofs.MeanEventCont

/-! The event branch's compatibility after the cut, and the event
experiment's hybrid for compatible continuations. After a cut, the event
branch is nothing on an ended cut and the end-resampled fork at a saved
snapshot; read on the cut with its world, it is compatible with pruning at
any keys, its touching functional being that of the fork from the
snapshot. The event experiment is then bounded through the cut hybrid for
compatible continuations and the fork hybrid. -/

namespace SDitH.Proofs.EventCutCompat

open Spec.SignatureSecurity Spec.SignatureReplay
open Spec.IdealCipher (Family Entry)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open RunHybrid GameResample ChargeExpect ChargeCutExpect RowStoredPosterior MeanHybrid MeanHybridCont MeanHybridContW RunWorld
open CipherResample SharedPrune HiddenEntries GamePrune GamePruneReverse GamePruneGen PruneCompatClosure ForkPruneCompat
open ForkRestore ForkRestoreLemmas ForkRestoreEnd ForkRestoreEq MeanForkCont MeanForkCont2 HiddenSlice MeanHybridCompat
open CutWorld MeanCutCompat EventRestore MeanEventCont CutHybridGen EventHybrid SharedResample
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (E : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    Option (Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) → Bool)

/-- The event branch's process on a cut with its world: the world itself
on an ended cut; at a saved snapshot, the first branch from the world with
the snapshot's input answered, then the fork's process. -/
def cutProc (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (r : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
      GW HashInput Digest lambda s wit rnd) : PMF (GW HashInput Digest lambda s wit rnd) :=
  match r.1 with
  | .ended _ => PMF.pure r.2
  | .saved sn => (PMF.uniformOfFintype Digest).bind fun a =>
      (runW sch adversary sn.remaining sn.publicKey sn.secretKey (sn.next a)
        { r.2 with hashTable := Function.update r.2.hashTable sn.input (some a) }
        { sn.trace with hashRequests := sn.input :: sn.trace.hashRequests }).bind fun r' =>
      forkProc adversary sch { sn with world := r.2 } r'

/-- The event branch's value on a cut with its world. -/
def branchEval (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (r : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
      GW HashInput Digest lambda s wit rnd) : ℝ≥0∞ :=
  (eventBranch adversary E sch r.1) true

variable (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (hsignLaw : ∀ sk m, PostLaw resample (sch.sign sk m)) (hpubLaw : ∀ q, PostLaw resample (sch.publicOracle q))
  (hprepLaw : ∀ pk m sig, PostLaw resample (sch.prepareVerification pk m sig))
  (hsignP : ∀ K sk m, PruneLaw K (sch.sign sk m)) (hpubP : ∀ K q, PruneLaw K (sch.publicOracle q))
  (hprepP : ∀ K pk m sig, PruneLaw K (sch.prepareVerification pk m sig))
  (hsignG : ∀ sk m, Grows (sch.sign sk m)) (hpubG : ∀ q, Grows (sch.publicOracle q))
  (hprepG : ∀ pk m sig, Grows (sch.prepareVerification pk m sig))
  (hsignK : ∀ sk m, Keeps (sch.sign sk m)) (hpubK : ∀ q, Keeps (sch.publicOracle q))
  (hprepK : ∀ pk m sig, Keeps (sch.prepareVerification pk m sig))
  (hnone : ∀ snapshot', E snapshot' none = false)
  (hEhist : ∀ snapshot' (H : List (Entry (Bits lambda) (Bits lambda))) res,
    E { snapshot' with world := { snapshot'.world with other := { snapshot'.world.other with cipherHistory := H } } } res =
      E snapshot' res)
  (hEleftW : ∀ snapshot' (a : Digest) t w₀ f H b₁ b₂ right,
    E snapshot' (some (⟨a, ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩, right)) =
      E snapshot' (some (⟨a, ⟨withWorld t w₀, b₁, b₂⟩⟩, right)))
  (hErightW : ∀ snapshot' left t w₀ f H b₁ b₂ (a' : Digest),
    E snapshot' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) =
      E snapshot' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩)))
  (hE : ∀ (K : List (Bits lambda)) snapshot' c c' (a a' : Digest),
    PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => rightEval snapshot' E a c c' a' r.2) (fun r => indicator (touchesG K r.2)))

include hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK hprepK hEleftW hErightW hE in
/-- The fork from a snapshot with a given world, as the compatible pair
built from the closure steps: the uniform answer, the hash update, the
first branch's run and the fork continuation. -/
theorem fork_pruneCompat (K : List (Bits lambda))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State) :
    PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (fun r => mean (PMF.uniformOfFintype Digest) fun a =>
        mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a)
          { r.2 with hashTable := Function.update r.2.hashTable snapshot.input (some a) }
          { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })
          (innerEval adversary E sch snapshot a))
      (fun r => mean (PMF.uniformOfFintype Digest) fun a =>
        mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a)
          { r.2 with hashTable := Function.update r.2.hashTable snapshot.input (some a) }
          { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })
          (fun r' => mean (forkProc adversary sch snapshot r') fun w => indicator (touchesG K w))) := by
  refine pruneCompat_sample K (PMF.uniformOfFintype Digest) _ _ fun a => ?_
  refine pruneCompat_update K (fun tbl => Function.update tbl snapshot.input (some a))
    (fun y => mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })
      (innerEval adversary E sch snapshot a))
    (fun y => mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })
      (fun r' => mean (forkProc adversary sch snapshot r') fun w => indicator (touchesG K w))) ?_
  have hinner : PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
      (innerEval adversary E sch snapshot a) (fun r' => mean (forkProc adversary sch snapshot r') fun w => indicator (touchesG K w)) :=
    pruneCompat_congr K _ _ _ _ (fun r => rfl) (fun r => by simp only [forkProc, forkTouch, leftTouch, mean_bind, mean_map])
      (forkCont_pruneCompat K sch adversary snapshot E a (fun _ _ _ w => indicator (touchesG K w)) hsignLaw hpubLaw hprepLaw
        (hsignP K) (hpubP K) (hprepP K) hsignG hpubG hprepG hsignK hpubK hprepK (fun snapshot' => hEleftW snapshot' a)
        hErightW (fun _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ => rfl) (fun c c' a' => hE K snapshot c c' a a'))
  exact runW_pruneCompat K sch adversary hsignLaw hpubLaw hprepLaw (hsignP K) (hpubP K) (hprepP K) hsignG hpubG hprepG hsignK
    hpubK hprepK _ _ hinner snapshot.remaining snapshot.publicKey snapshot.secretKey (fun _ => snapshot.next a) (fun _ _ => rfl)
    (fun _ => { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) (fun _ _ => rfl)

include hEhist in
/-- The inner evaluation ignores the snapshot world's cipher history. -/
theorem innerEval_hist
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (H : List (Entry (Bits lambda) (Bits lambda))) (a : Digest) (r) :
    innerEval adversary E sch
        { snapshot with world := { snapshot.world with other := { snapshot.world.other with cipherHistory := H } } } a r =
      innerEval adversary E sch snapshot a r := by
  unfold innerEval
  refine congrArg _ (funext fun w' => congrArg _ (funext fun c => congrArg _ (funext fun rw => congrArg _ (funext fun w'' =>
    ?_))))
  exact congrArg _ (hEhist { snapshot with world := setFamily snapshot.world w''.other.family } H _)

/-- The fork's process ignores the snapshot world's cipher history. -/
theorem forkProc_hist
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (H : List (Entry (Bits lambda) (Bits lambda))) (r) :
    forkProc adversary sch
        { snapshot with world := { snapshot.world with other := { snapshot.world.other with cipherHistory := H } } } r =
      forkProc adversary sch snapshot r := rfl

include hsignG hpubG hprepG in
/-- Touching persists along the fork's process. -/
theorem forkProc_touches (K : List (Bits lambda))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (r : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) (hr : touchesG K r.2 = true) :
    ∀ w ∈ (forkProc adversary sch snapshot r).support, touchesG K w = true := by
  intro w hw
  simp only [forkProc, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hw
  obtain ⟨w', hw', c, -, rw, hrw, rfl⟩ := hw
  have h1 : touchesG K w' = true := touchesG_of_mem_resampleW K r.2 w' hw' hr
  simp only [freshBranchW, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hrw
  obtain ⟨answer', -, r', hr', checked, -, rfl⟩ := hrw
  exact touchesG_runW K sch adversary hsignG hpubG hprepG _ _ _ _
    { restore snapshot.world w' with hashTable := Function.update (restore snapshot.world w').hashTable snapshot.input (some answer') }
    _ h1 r' hr'

include hsignG hpubG hprepG in
/-- Touching persists along the event branch's process. -/
theorem cutProc_touches (K : List (Bits lambda))
    (r : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
      GW HashInput Digest lambda s wit rnd) (hr : touchesG K r.2 = true) :
    ∀ w ∈ (cutProc adversary sch r).support, touchesG K w = true := by
  intro w hw
  rcases r with ⟨c, w₀⟩
  cases c with
  | ended t =>
    simp only [cutProc, PMF.support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hr
  | saved sn =>
    simp only [cutProc, PMF.mem_support_bind_iff] at hw
    obtain ⟨a, -, r', hr', hw⟩ := hw
    have h1 : touchesG K r'.2 = true := touchesG_runW K sch adversary hsignG hpubG hprepG _ _ _ _
      { w₀ with hashTable := Function.update w₀.hashTable sn.input (some a) } _ hr r' hr'
    exact forkProc_touches adversary sch hsignG hpubG hprepG K _ r' h1 w hw

include hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK hpubK hprepK hnone hEhist hEleftW hErightW hE in
/-- The event branch read on the cut with its world is compatible with
pruning at any keys, with the touching of its process. -/
theorem eventBranch_pruneCompatC (K : List (Bits lambda)) :
    PruneCompatC K (branchEval adversary E sch) (fun r => mean (cutProc adversary sch r) fun w => indicator (touchesG K w)) where
  le_one r := PMF.coe_le_one _ _
  touch_le r := by
    by_cases ht : touchesG K r.2 = true
    · rw [ht]
      calc indicator true = mean (cutProc adversary sch r) (fun _ => (1 : ℝ≥0∞)) := by rw [mean_const]; rfl
        _ ≤ _ := mean_le_mean _ _ _ fun w hw => by
            rw [cutProc_touches adversary sch hsignG hpubG hprepG K r ht w hw]
            rfl
    · rw [Bool.not_eq_true] at ht
      rw [ht]
      exact zero_le _
  forward c world hw := by
    cases c with
    | ended t =>
      have h0 : ∀ w, branchEval adversary E sch (withWorldC (Cut.ended t) w, w) = 0 := fun w => by
        simp only [branchEval, withWorldC, eventBranch, PMF.pure_apply, Bool.true_eq_false, if_false]
      simp only [h0, mean_const]
      exact zero_le _
    | saved sn =>
      cases hlook : world.hashTable sn.input with
      | some d =>
        have h0 : ∀ w ∈ (resampleW resample world).support, branchEval adversary E sch (withWorldC (Cut.saved sn) w, w) = 0 := by
          intro w hw
          obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW world w hw
          have hl : (setFamily world f).hashTable sn.input = some d := hlook
          simp only [branchEval, withWorldC, eventBranch, forkEventE, hl, hnone, PMF.pure_apply, Bool.true_eq_false, if_false]
        rw [mean_congr_support _ _ _ h0, mean_const]
        exact zero_le _
      | none =>
        set sn' : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State :=
          { sn with world := world } with hsn'
        have hlook' : sn'.world.hashTable sn'.input = none := hlook
        have hfork := fork_pruneCompat adversary E sch hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK
          hpubK hprepK hEleftW hErightW hE K sn'
        have hL : mean (resampleW resample world) (fun w => branchEval adversary E sch (withWorldC (Cut.saved sn) w, w)) =
            mean (resampleW resample world) (fun w => mean (PMF.uniformOfFintype Digest) fun a =>
              mean (runW sch adversary sn'.remaining sn'.publicKey sn'.secretKey (sn'.next a)
                { w with hashTable := Function.update w.hashTable sn'.input (some a) }
                { sn'.trace with hashRequests := sn'.input :: sn'.trace.hashRequests })
                (innerEval adversary E sch sn' a)) :=
          mean_congr_support _ _ _ fun w hw => by
            rw [hashTable_of_mem resample world w hw]
            exact forkEventE_mean adversary E sch sn' hlook' w hw
        have hR : mean (resampleW resample (pruneW K world)) (fun w =>
            branchEval adversary E sch (withWorldC (Cut.saved sn) w, w) +
              mean (cutProc adversary sch (withWorldC (Cut.saved sn) w, w)) fun w' => indicator (touchesG K w')) =
            mean (resampleW resample (pruneW K world)) (fun w => (mean (PMF.uniformOfFintype Digest) fun a =>
              mean (runW sch adversary sn'.remaining sn'.publicKey sn'.secretKey (sn'.next a)
                { w with hashTable := Function.update w.hashTable sn'.input (some a) }
                { sn'.trace with hashRequests := sn'.input :: sn'.trace.hashRequests })
                (innerEval adversary E sch sn' a)) +
              mean (PMF.uniformOfFintype Digest) fun a =>
                mean (runW sch adversary sn'.remaining sn'.publicKey sn'.secretKey (sn'.next a)
                  { w with hashTable := Function.update w.hashTable sn'.input (some a) }
                  { sn'.trace with hashRequests := sn'.input :: sn'.trace.hashRequests })
                  (fun r' => mean (forkProc adversary sch sn' r') fun w' => indicator (touchesG K w'))) :=
          mean_congr_support _ _ _ fun w hw => by
            obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW (pruneW K world) w hw
            set sn'' : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query
                State := { sn with world := pruneW K world } with hsn''
            have hlook'' : sn''.world.hashTable sn''.input = none := hlook
            have hmem : setFamily (pruneW K world) f ∈ (resampleW resample sn''.world).support := hw
            have h := forkEventE_mean adversary E sch sn'' hlook'' (setFamily (pruneW K world) f) hmem
            refine congrArg₂ _ ?_ ?_
            · refine h.trans ?_
              refine congrArg _ (funext fun a => congrArg _ (funext fun r => ?_))
              exact innerEval_hist adversary E sch hEhist sn' (pruneAt K world.other.cipherHistory) a r
            · simp only [cutProc, withWorldC, mean_bind]
              rfl
        rw [hL, hR]
        exact hfork.forward (Terminal.exhausted ⟨[], [], []⟩) world hw
  reverse c world hw := by
    cases c with
    | ended t =>
      have h0 : ∀ w, branchEval adversary E sch (withWorldC (Cut.ended t) w, w) = 0 := fun w => by
        simp only [branchEval, withWorldC, eventBranch, PMF.pure_apply, Bool.true_eq_false, if_false]
      simp only [h0, mean_const]
      exact zero_le _
    | saved sn =>
      cases hlook : world.hashTable sn.input with
      | some d =>
        have h0 : ∀ w ∈ (resampleW resample (pruneW K world)).support,
            branchEval adversary E sch (withWorldC (Cut.saved sn) w, w) = 0 := by
          intro w hw
          obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW (pruneW K world) w hw
          have hl : (setFamily (pruneW K world) f).hashTable sn.input = some d := hlook
          simp only [branchEval, withWorldC, eventBranch, forkEventE, hl, hnone, PMF.pure_apply, Bool.true_eq_false, if_false]
        rw [mean_congr_support _ _ _ h0, mean_const]
        exact zero_le _
      | none =>
        set sn' : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State :=
          { sn with world := world } with hsn'
        have hlook' : sn'.world.hashTable sn'.input = none := hlook
        have hfork := fork_pruneCompat adversary E sch hsignLaw hpubLaw hprepLaw hsignP hpubP hprepP hsignG hpubG hprepG hsignK
          hpubK hprepK hEleftW hErightW hE K sn'
        have hL : mean (resampleW resample world) (fun w => branchEval adversary E sch (withWorldC (Cut.saved sn) w, w)) =
            mean (resampleW resample world) (fun w => mean (PMF.uniformOfFintype Digest) fun a =>
              mean (runW sch adversary sn'.remaining sn'.publicKey sn'.secretKey (sn'.next a)
                { w with hashTable := Function.update w.hashTable sn'.input (some a) }
                { sn'.trace with hashRequests := sn'.input :: sn'.trace.hashRequests })
                (innerEval adversary E sch sn' a)) :=
          mean_congr_support _ _ _ fun w hw => by
            rw [hashTable_of_mem resample world w hw]
            exact forkEventE_mean adversary E sch sn' hlook' w hw
        have hP : mean (resampleW resample (pruneW K world)) (fun w =>
            branchEval adversary E sch (withWorldC (Cut.saved sn) w, w)) =
            mean (resampleW resample (pruneW K world)) (fun w => mean (PMF.uniformOfFintype Digest) fun a =>
              mean (runW sch adversary sn'.remaining sn'.publicKey sn'.secretKey (sn'.next a)
                { w with hashTable := Function.update w.hashTable sn'.input (some a) }
                { sn'.trace with hashRequests := sn'.input :: sn'.trace.hashRequests })
                (innerEval adversary E sch sn' a)) :=
          mean_congr_support _ _ _ fun w hw => by
            obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW (pruneW K world) w hw
            set sn'' : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query
                State := { sn with world := pruneW K world } with hsn''
            have hlook'' : sn''.world.hashTable sn''.input = none := hlook
            have hmem : setFamily (pruneW K world) f ∈ (resampleW resample sn''.world).support := hw
            have h := forkEventE_mean adversary E sch sn'' hlook'' (setFamily (pruneW K world) f) hmem
            refine h.trans ?_
            refine congrArg _ (funext fun a => congrArg _ (funext fun r => ?_))
            exact innerEval_hist adversary E sch hEhist sn' (pruneAt K world.other.cipherHistory) a r
        have hT : mean (resampleW resample (pruneW K world)) (fun w =>
            mean (cutProc adversary sch (withWorldC (Cut.saved sn) w, w)) fun w' => indicator (touchesG K w')) =
            mean (resampleW resample (pruneW K world)) (fun w => mean (PMF.uniformOfFintype Digest) fun a =>
              mean (runW sch adversary sn'.remaining sn'.publicKey sn'.secretKey (sn'.next a)
                { w with hashTable := Function.update w.hashTable sn'.input (some a) }
                { sn'.trace with hashRequests := sn'.input :: sn'.trace.hashRequests })
                (fun r' => mean (forkProc adversary sch sn' r') fun w' => indicator (touchesG K w'))) :=
          mean_congr_support _ _ _ fun w hw => by
            obtain ⟨f, rfl⟩ := eq_setFamily_of_mem_resampleW (pruneW K world) w hw
            simp only [cutProc, withWorldC, mean_bind]
            rfl
        rw [hL, hP, hT]
        exact hfork.reverse (Terminal.exhausted ⟨[], [], []⟩) world hw

/-- The event branch's process keeps the invariant within the end budget
on reachable cuts. -/
theorem cutProc_inv (Inv : Nat → GW HashInput Digest lambda s wit rnd → Prop) (B B' : Nat) (hB' : 4 * B + 3 ≤ B')
    (hmono : ∀ (n m : Nat) (world : GW HashInput Digest lambda s wit rnd), n ≤ m → Inv n world → Inv m world)
    (hres : ∀ (n : Nat) (world : GW HashInput Digest lambda s wit rnd), Inv n world →
      ∀ w ∈ (resampleW resample world).support, Inv n w)
    (hquery : ∀ (world : GW HashInput Digest lambda s wit rnd) (input : HashInput) (n : Nat)
      (r : Digest × (HashInput → Option Digest)), Inv n world →
      r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
    (hpresS : ∀ (sk : SecretKey) (message : Message) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
      (r : Signature × GW HashInput Digest lambda s wit rnd), Inv n world →
      r ∈ (sch.sign sk message world).support → Inv (n + 1) r.2)
    (hpubS : ∀ (query : Query) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
      (r : Answer × GW HashInput Digest lambda s wit rnd),
      Inv n world → r ∈ (sch.publicOracle query world).support → Inv (n + 1) r.2)
    (hprepInvS : ∀ (pk : PublicKey) (message : Message) (signature : Signature) (world : GW HashInput Digest lambda s wit rnd)
      (n : Nat) (r : Option HashInput × GW HashInput Digest lambda s wit rnd), Inv n world →
      r ∈ (sch.prepareVerification pk message signature world).support → Inv (n + 1) r.2)
    (hupdate : ∀ (world : GW HashInput Digest lambda s wit rnd) (input : HashInput) (n : Nat) (d : Digest), Inv n world →
      Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) })
    (hrestore : ∀ (n : Nat) (W wL : GW HashInput Digest lambda s wit rnd), Inv n W → Inv n wL → Inv n (restore W wL)) :
    ∀ r, Inv B r.2 → ReachC B r.1 → ∀ w ∈ (cutProc adversary sch r).support, Inv B' w := by
  intro r hr hreach w hw
  rcases r with ⟨c, w₀⟩
  cases c with
  | ended t =>
    simp only [cutProc, PMF.support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hmono _ _ _ (by omega) hr
  | saved sn =>
    have hrem : sn.remaining ≤ B := hreach sn rfl
    simp only [cutProc, PMF.mem_support_bind_iff] at hw
    obtain ⟨a, -, r', hr', hw⟩ := hw
    have h1 : Inv (B + 1) { w₀ with hashTable := Function.update w₀.hashTable sn.input (some a) } :=
      hupdate w₀ sn.input B a hr
    have h2 := runW_inv sch sch adversary ⟨rfl, rfl, rfl, rfl⟩ Inv hmono hquery hpresS hpubS hprepInvS sn.remaining _ _ _ _ _
      (B + 1) h1 r' hr'
    have h3 : Inv (2 * B + 1) r'.2 := hmono _ _ _ (by omega) h2
    exact forkProc_inv sch adversary (2 * B + 1) B' Inv hmono hres hquery hpresS hpubS hprepInvS hupdate hrestore
      { sn with world := w₀ } B hr (by omega) (by show sn.remaining ≤ 2 * B + 1; omega) (by omega) r' h3 w hw

section Experiment

variable (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (ε : ℝ≥0∞) (B B' B'' : Nat)
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
  (hsignLaw₁ : ∀ (sk : SecretKey) (message : Message), PostLaw resample (sch₁.sign sk message))
  (hsignLaw₂ : ∀ (sk : SecretKey) (message : Message), PostLaw resample (sch₂.sign sk message))
  (hpubLaw₂ : ∀ query : Query, PostLaw resample (sch₂.publicOracle query))

include hagree hmono hres hquery hpres hpres₂ hpub hprepInv hupdate hrestore hsignLaw₁ hsignLaw₂ hpubLaw₂ in
/-- The end-resampled event experiment hybrid in mean form for compatible
continuations: the cut's per-call bound for the event branch's process
within the budget four times the fuel plus three, and the fork's for its
process within twice the fuel plus one. -/
theorem eventExpE_le_meanP
    (hkeygen : sch₁.keygen = sch₁.keygen.bind fun g => (resampleW resample g.2.2).map fun w => (g.1, g.2.1, w))
    (hgood : ∀ generated ∈ sch₁.keygen.support, Good generated.2.1)
    (hinit : ∀ generated ∈ sch₁.keygen.support, Inv 0 generated.2.2)
    (hsignCut : SignCutWMeanP sch₁ sch₂ adversary Good ε B B'' Inv) (hB'' : 4 * B + 3 ≤ B'')
    (hsignRunW : SignRunWMeanP sch₁ sch₂ adversary Good ε B B' Inv) (hB' : 2 * B + 1 ≤ B')
    (hprepLaw₂ : ∀ pk m sig, PostLaw resample (sch₂.prepareVerification pk m sig))
    (hsignP₁ : ∀ K sk m, PruneLaw K (sch₁.sign sk m)) (hsignG₁ : ∀ sk m, Grows (sch₁.sign sk m))
    (hsignK₁ : ∀ sk m, Keeps (sch₁.sign sk m))
    (hsignP₂ : ∀ K sk m, PruneLaw K (sch₂.sign sk m)) (hsignG₂ : ∀ sk m, Grows (sch₂.sign sk m))
    (hsignK₂ : ∀ sk m, Keeps (sch₂.sign sk m))
    (hpubP₂ : ∀ K q, PruneLaw K (sch₂.publicOracle q)) (hprepP₂ : ∀ K pk m sig, PruneLaw K (sch₂.prepareVerification pk m sig))
    (hpubG₂ : ∀ q, Grows (sch₂.publicOracle q)) (hprepG₂ : ∀ pk m sig, Grows (sch₂.prepareVerification pk m sig))
    (hpubK₂ : ∀ q, Keeps (sch₂.publicOracle q)) (hprepK₂ : ∀ pk m sig, Keeps (sch₂.prepareVerification pk m sig))
    (hnone : ∀ snapshot', E snapshot' none = false)
    (hEhist : ∀ snapshot' (H : List (Entry (Bits lambda) (Bits lambda))) res,
      E { snapshot' with world := { snapshot'.world with other := { snapshot'.world.other with cipherHistory := H } } } res =
        E snapshot' res)
    (hEleft : ∀ snapshot' left right g, E snapshot' (some (setFamilyBranch g left, right)) = E snapshot' (some (left, right)))
    (hEleftW : ∀ snapshot' (a : Digest) t w₀ f H b₁ b₂ right,
      E snapshot' (some (⟨a, ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩, right)) =
        E snapshot' (some (⟨a, ⟨withWorld t w₀, b₁, b₂⟩⟩, right)))
    (hErightW : ∀ snapshot' left t w₀ f H b₁ b₂ (a' : Digest),
      E snapshot' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) =
        E snapshot' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩)))
    (hE : ∀ (K : List (Bits lambda)) snapshot' c c' (a a' : Digest),
      PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
        (fun r => rightEval snapshot' E a c c' a' r.2) (fun r => indicator (touchesG K r.2)))
    (index fuel : Nat) (hB : 3 * fuel + 2 ≤ B) :
    (eventExpE sch₁ adversary E index fuel) true ≤
      (eventExpE sch₂ adversary E index fuel) true + (fuel * ε + 2 * fuel * ε) := by
  -- the first scheme's public oracle and verification preparation are the second's
  have hpubLaw₁ : ∀ q, PostLaw resample (sch₁.publicOracle q) := fun q => by
    rw [hagree.publicOracle]; exact hpubLaw₂ q
  have hprepLaw₁ : ∀ pk m sig, PostLaw resample (sch₁.prepareVerification pk m sig) := fun pk m sig => by
    rw [hagree.prepareVerification]; exact hprepLaw₂ pk m sig
  have hpubP₁ : ∀ K q, PruneLaw K (sch₁.publicOracle q) := fun K q => by
    rw [hagree.publicOracle]; exact hpubP₂ K q
  have hprepP₁ : ∀ K pk m sig, PruneLaw K (sch₁.prepareVerification pk m sig) := fun K pk m sig => by
    rw [hagree.prepareVerification]; exact hprepP₂ K pk m sig
  have hpubG₁ : ∀ q, Grows (sch₁.publicOracle q) := fun q => by rw [hagree.publicOracle]; exact hpubG₂ q
  have hprepG₁ : ∀ pk m sig, Grows (sch₁.prepareVerification pk m sig) := fun pk m sig => by
    rw [hagree.prepareVerification]; exact hprepG₂ pk m sig
  have hpubK₁ : ∀ q, Keeps (sch₁.publicOracle q) := fun q => by rw [hagree.publicOracle]; exact hpubK₂ q
  have hprepK₁ : ∀ pk m sig, Keeps (sch₁.prepareVerification pk m sig) := fun pk m sig => by
    rw [hagree.prepareVerification]; exact hprepK₂ pk m sig
  have hpub₁ : ∀ (query : Query) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
      (r : Answer × GW HashInput Digest lambda s wit rnd),
      Inv n world → r ∈ (sch₁.publicOracle query world).support → Inv (n + 1) r.2 := fun q w n r h hr =>
    hpub q w n r h (by rwa [hagree.publicOracle] at hr)
  have hprepInv₁ : ∀ (pk : PublicKey) (message : Message) (signature : Signature) (world : GW HashInput Digest lambda s wit rnd)
      (n : Nat) (r : Option HashInput × GW HashInput Digest lambda s wit rnd), Inv n world →
      r ∈ (sch₁.prepareVerification pk message signature world).support → Inv (n + 1) r.2 := fun pk m sig w n r h hr =>
    hprepInv pk m sig w n r h (by rwa [hagree.prepareVerification] at hr)
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
  have hcw : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer) (w : GW HashInput Digest lambda s wit rnd),
      mean (cutW sch adversary index fuel g.1 g.2.1 state w ⟨[], [], []⟩) (fun r => (eventBranch adversary E sch₁ r.1) true) =
        mean (cut sch adversary index fuel g.1 g.2.1 state w ⟨[], [], []⟩) (fun c => (eventBranch adversary E sch₁ c) true) := by
    intro sch w
    rw [← cutW_fst, mean_map]
  have h1 := cutW_le_cutW_mean_contP sch₁ sch₂ adversary hagree Good ε B B'' Inv hres hquery hpres hpub hsignLaw₁ hpubLaw₂
    hsignCut index fuel g.1 g.2.1 (hgood g hg) state g.2.2 ⟨[], [], []⟩ 0 (hinit g hg) (by omega)
    (fun r => eventBranch adversary E sch₁ r.1) true (cutProc adversary sch₁)
    (fun K => eventBranch_pruneCompatC adversary E sch₁ hsignLaw₁ hpubLaw₁ hprepLaw₁ hsignP₁ hpubP₁ hprepP₁ hsignG₁ hpubG₁
      hprepG₁ hsignK₁ hpubK₁ hprepK₁ hnone hEhist hEleftW hErightW hE K)
    (cutProc_inv adversary sch₁ Inv B B'' hB'' hmono hres hquery hpres hpub₁ hprepInv₁ hupdate hrestore)
  simp only [mean_bind_apply, hcw] at h1
  have h2 : mean (resampleW resample g.2.2) (fun w =>
        mean (cut sch₂ adversary index fuel g.1 g.2.1 state w ⟨[], [], []⟩) fun c => (eventBranch adversary E sch₁ c) true) ≤
      mean (resampleW resample g.2.2) (fun w =>
        mean (cut sch₂ adversary index fuel g.1 g.2.1 state w ⟨[], [], []⟩) fun c => (eventBranch adversary E sch₂ c) true) +
        2 * fuel * ε := by
    rw [← mean_bind, cut_postLaw resample resample_idem sch₂ adversary hsignLaw₂ hpubLaw₂]
    conv_rhs => rw [← mean_bind, cut_postLaw resample resample_idem sch₂ adversary hsignLaw₂ hpubLaw₂]
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
      refine (forkEventE_le_meanP sch₁ sch₂ adversary hagree Good ε B B' Inv hmono hres hquery hpres hpres₂ hpub hprepInv hupdate
        hrestore hsignLaw₁ hsignLaw₂ hpubLaw₂ E hsignRunW hB' hprepLaw₂ hsignP₂ hpubP₂ hprepP₂ hsignG₂ hpubG₂ hprepG₂ hsignK₂ hpubK₂
        hprepK₂ hEleft hEleftW hErightW hE snapshot hsk' (0 + fuel) hsup (by omega)).trans ?_
      exact add_le_add le_rfl (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr hrem)) le_rfl)
  calc _ ≤ _ := h1
    _ ≤ _ := add_le_add h2 le_rfl
    _ = _ := by ring

end Experiment

end
end SDitH.Proofs.EventCutCompat
