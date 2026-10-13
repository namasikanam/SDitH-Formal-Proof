import SDitH.Proofs.PairForkFamily
import SDitH.Proofs.SlopeCoverFork
import SDitH.Proofs.SeedCollisionBound

/-! The witnessed pair under the snapshot's family in the union of the two
branches' histories: through the family-dependent fork bound, the event's
probability is at most the restored chain's mean of the pair mass of the
second branch's final history, hence at most the snapshot's pair mass and
two branches' costs; over the random event experiment it is at most three
times the fuel plus one, times one call's pair cost with the identity
projection. -/

namespace SDitH.Proofs.ForkWitnessedBound

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher Spec.IdealCipherPairCollision
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq ForkRestoreEnd SharedResample HiddenSlice MeanHybrid PairMass PairOracles PairRun
open PairFork PairForkFamily SignBridge PruneCompatClosure IdealCipherPairCollision
open scoped Classical ENNReal

noncomputable section

section Generic

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)

/-- A fresh branch's final history extends the snapshot's. -/
theorem freshBranchW_history (hsignG : ∀ sk m, Grows (sch.sign sk m)) (hpubG : ∀ q, Grows (sch.publicOracle q))
    (hprepG : ∀ pk m sig, Grows (sch.prepareVerification pk m sig))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (rw : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) (h : rw ∈ (freshBranchW sch adversary snapshot).support) :
    ∃ new, rw.2.other.cipherHistory = new ++ snapshot.world.other.cipherHistory := by
  unfold freshBranchW at h
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at h
  obtain ⟨answer, -, r, hr, checked, -, rfl⟩ := h
  obtain ⟨new, hnew⟩ := runW_history sch adversary hsignG hpubG hprepG _ _ _ _ _ _ r hr
  exact ⟨new, hnew⟩

omit [Fintype Digest] [Nonempty Digest] in
/-- The attempt history of a checked first branch is the run's final
history or empty. -/
theorem attemptHistory_checked (a : Digest) (t : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (w : GW HashInput Digest lambda s wit rnd) (hw : withWorld t w = t)
    (c : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) (hc : c.terminal = t) :
    attemptHistory (⟨a, c⟩ : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) ⊆
      w.other.cipherHistory := by
  unfold attemptHistory
  dsimp only
  rw [hc]
  cases t with
  | attempt att =>
    simp only [withWorld, Terminal.attempt.injEq] at hw
    have hworld : w = att.world := by simpa using congrArg Attempt.world hw
    show att.world.other.cipherHistory ⊆ w.other.cipherHistory
    rw [← hworld]
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
  (hEleft : ∀ snapshot' left right, E snapshot' (some (left, right)) = true →
    ∃ att, left.checked.terminal = Terminal.attempt att)
  (hEfamL : ∀ snapshot' left right g, E snapshot' (some (setFamilyBranch g left, right)) = E snapshot' (some (left, right)))
  (hE : ∀ (snapshot' : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query
      State) left right (g : Family (Bits lambda) (Bits lambda)),
    E { snapshot' with world := setFamily snapshot'.world g } (some (left, right)) = true →
      Witnessed project companion g (attemptHistory right ++ attemptHistory left))

omit [Fintype Digest] [Nonempty Digest] in
/-- The end-resampled witnessed event on a sub-history is at most the pair
mass of the history. -/
theorem union_le_pairMass (rw : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd)
    (left : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (hU : attemptHistory rw.1 ++ attemptHistory left ⊆ rw.2.other.cipherHistory) :
    mean (resampleW resample rw.2) (fun w'' =>
        indicator (decide (Witnessed project companion w''.other.family (attemptHistory rw.1 ++ attemptHistory left)))) ≤
      pairMass project companion rw.2.other.cipherHistory := by
  unfold pairMass resampleW resample
  rw [mean_map, mean_map]
  refine mean_le_mean _ _ _ fun g _ => ?_
  by_cases hwit : Witnessed project companion g (attemptHistory rw.1 ++ attemptHistory left)
  · rw [decide_eq_true (witnessed_mono project companion g _ _ hU hwit), RandomOracleTrap.indicator_true]
    exact indicator_le_one' _
  · rw [decide_eq_false hwit, RandomOracleTrap.indicator_false]
    exact zero_le _

include hsignG hpubG hprepG in
/-- The union of the attempt histories of the restored second branch and
of the checked first branch is within the second branch's final history. -/
theorem union_subset_final
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (a : Digest) (r : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) (hwa : withWorld r.1 r.2 = r.1)
    (c : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query) (hc : c.terminal = r.1)
    (y : GW HashInput Digest lambda s wit rnd) (hy : y ∈ (resampleW resample (restore snapshot.world r.2)).support)
    (rw : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) (hrw : rw ∈ (freshBranchW sch adversary { snapshot with world := y }).support) :
    attemptHistory rw.1 ++ attemptHistory (⟨a, c⟩ : Branch Message Signature HashInput Digest
      (Spec.SharedScheme.World lambda s wit rnd) Query) ⊆ rw.2.other.cipherHistory := by
  have hatt : attemptHistory rw.1 ⊆ rw.2.other.cipherHistory := freshBranchW_attempt sch adversary _ rw hrw
  obtain ⟨new, hnew⟩ := freshBranchW_history sch adversary hsignG hpubG hprepG _ rw hrw
  have hyhist : y.other.cipherHistory = (restore snapshot.world r.2).other.cipherHistory :=
    history_of_mem_resampleW _ _ hy
  have hleft : attemptHistory (⟨a, c⟩ : Branch Message Signature HashInput Digest
      (Spec.SharedScheme.World lambda s wit rnd) Query) ⊆ r.2.other.cipherHistory :=
    attemptHistory_checked a r.1 r.2 hwa c hc
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hatt hx
  · have h1 : x ∈ r.2.other.cipherHistory := hleft hx
    have h2 : x ∈ y.other.cipherHistory := by
      rw [hyhist]
      exact h1
    have h3 : x ∈ new ++ y.other.cipherHistory := List.mem_append_right _ h2
    rw [hnew]
    exact h3

include hmono hres hquery hpres hpub hprepInv hupdate hrestore hsignLaw hpubLaw hsignP hpubP hprepP in
/-- The restored chain's pair mass is at most the snapshot's and two
branches' costs. -/
theorem restored_chain_le
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (n : Nat) (hn : Inv n snapshot.world) (hB : n + 2 * (snapshot.remaining + 1) ≤ B) (a : Digest) :
    mean (resampleW resample { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) })
        (fun w =>
          mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) w
              { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
            mean (finalize r.1) fun _ =>
              mean (resampleW resample (restore snapshot.world r.2)) fun y =>
                mean (freshBranchW sch adversary { snapshot with world := y }) fun rw =>
                  pairMass project companion rw.2.other.cipherHistory) ≤
      pairMass project companion snapshot.world.other.cipherHistory + ((2 * snapshot.remaining : Nat) : ℝ≥0∞) * ε := by
  set Wa : GW HashInput Digest lambda s wit rnd :=
    { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) } with hWa
  have hWaInv : Inv (n + 1) Wa := hupdate snapshot.world snapshot.input n a hn
  have hWahist : Wa.other.cipherHistory = snapshot.world.other.cipherHistory := rfl
  have hstep : ∀ w ∈ (resampleW resample Wa).support,
      ∀ r ∈ (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) w
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).support,
      (mean (finalize r.1) fun _ =>
        mean (resampleW resample (restore snapshot.world r.2)) fun y =>
          mean (freshBranchW sch adversary { snapshot with world := y }) fun rw =>
            pairMass project companion rw.2.other.cipherHistory) ≤
      pairMass project companion r.2.other.cipherHistory + (snapshot.remaining : ℝ≥0∞) * ε := by
    intro w hw r hr
    have hwInv : Inv (n + 1) w := hres _ _ hWaInv w hw
    have hr2 : Inv (n + 1 + snapshot.remaining) r.2 :=
      runW_inv' sch adversary Inv hmono hquery hpres hpub hprepInv _ _ _ _ _ _ _ hwInv r hr
    rw [mean_const]
    exact freshBranchW_pair_bound sch adversary project companion ε B Inv hres hquery hpres hpub hupdate hsignLaw hpubLaw
      hsignP hpubP hprepP { snapshot with world := restore snapshot.world r.2 } (n + 1 + snapshot.remaining)
      (hrestore _ _ _ (hmono _ _ _ (by omega) hn) hr2) (by simp only; omega)
  calc _ ≤ mean (resampleW resample Wa) (fun w =>
          mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) w
              { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
            pairMass project companion r.2.other.cipherHistory + (snapshot.remaining : ℝ≥0∞) * ε) :=
        mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => hstep w hw r hr
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

include hmono hres hquery hpres hpub hprepInv hupdate hrestore hsignLaw hpubLaw hprepLaw hsignF hpubF hprepF hsignG hpubG
  hprepG hsignS hpubS hprepS hsignP hpubP hprepP hnone hEleft hEfamL hE in
/-- The fork bound for a family-dependent witnessed event. -/
theorem fork_witnessed_bound
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (n : Nat) (hn : Inv n snapshot.world) (hB : n + 2 * (snapshot.remaining + 1) ≤ B) :
    mean (resampleW resample snapshot.world) (fun w =>
        ((forkAt sch adversary { snapshot with world := w }).map (E { snapshot with world := w })) true) ≤
      pairMass project companion snapshot.world.other.cipherHistory + ((2 * snapshot.remaining : Nat) : ℝ≥0∞) * ε := by
  refine (fork_family_bound sch adversary (fun _ _ g U => decide (Witnessed project companion g U))
    (fun _ _ g U U' h => decide_eq_decide.mpr
      ⟨witnessed_mono project companion g U U' fun x hx => (h x).mp hx,
        witnessed_mono project companion g U' U fun x hx => (h x).mpr hx⟩)
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) E hnone hEleft hEfamL
    (fun s' l r g h => decide_eq_true (hE s' l r g h)) hsignLaw hpubLaw hprepLaw hsignF hpubF hprepF hsignG hpubG hprepG
    hsignS hpubS hprepS snapshot).trans ?_
  refine mean_le_const _ _ _ fun a _ => ?_
  refine le_trans ?_ (restored_chain_le sch adversary project companion ε B Inv hmono hres hquery hpres hpub hprepInv hupdate
    hrestore hsignLaw hpubLaw hsignP hpubP hprepP snapshot n hn hB a)
  refine mean_le_mean _ _ _ fun w _ => mean_le_mean _ _ _ fun r hr => mean_le_mean _ _ _ fun c hc =>
    mean_le_mean _ _ _ fun y hy => mean_le_mean _ _ _ fun rw hrw => ?_
  exact union_le_pairMass project companion rw ⟨a, c⟩ (union_subset_final sch adversary hsignG hpubG hprepG snapshot a r
    (runW_attempt sch adversary _ _ _ _ _ _ r hr) c (finalize_terminal r.1 c hc) y hy rw hrw)

end Generic

section Candidate

open Spec.BAVC Spec.DomainSeparation Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.SeedPairing
open CandidateResample CandidatePrepLaw CandidatePrune CipherInvariant InvCExtra CandidateReduction CandidateKeepsFamily
open CandidateShift SimulationGap ChargeCutExpect CutHybridGen ForkEventUnion SlopeCoverFork SeedCollisionBound
open ForgeryReduction SeedPairing

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem witnessedFork_none (snapshot : Snap F lambda s higherCount w widths State) :
    witnessedFork (tau := tau) (kappa := kappa) snapshot none = false := rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem witnessedFork_left (snapshot : Snap F lambda s higherCount w widths State)
    (left right : Br F lambda tau kappa s higherCount w widths)
    (h : witnessedFork (tau := tau) (kappa := kappa) snapshot (some (left, right)) = true) :
    ∃ att, left.checked.terminal = Terminal.attempt att := by
  simp only [witnessedFork, onAttempts] at h
  cases hl : left.checked.terminal with
  | attempt a => exact ⟨a, rfl⟩
  | exhausted t => rw [hl] at h; simp at h
  | aborted t => rw [hl] at h; simp at h
  | rejected t => rw [hl] at h; simp at h

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem witnessedFork_famL (snapshot : Snap F lambda s higherCount w widths State)
    (left right : Br F lambda tau kappa s higherCount w widths) (g : Family (Bits lambda) (Bits lambda)) :
    witnessedFork (tau := tau) (kappa := kappa) snapshot (some (setFamilyBranch g left, right)) =
      witnessedFork (tau := tau) (kappa := kappa) snapshot (some (left, right)) := by
  simp only [witnessedFork, onAttempts, setFamilyBranch, setFamilyT]
  cases left.checked.terminal <;> cases right.checked.terminal <;> rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem witnessedFork_union (snapshot : Snap F lambda s higherCount w widths State)
    (left right : Br F lambda tau kappa s higherCount w widths) (g : Family (Bits lambda) (Bits lambda))
    (h : witnessedFork (tau := tau) (kappa := kappa) { snapshot with world := setFamily snapshot.world g }
      (some (left, right)) = true) :
    Witnessed id companion g (attemptHistory right ++ attemptHistory left) := by
  simp only [witnessedFork, onAttempts] at h
  unfold attemptHistory
  cases hl : left.checked.terminal with
  | attempt a =>
    cases hr : right.checked.terminal with
    | attempt b =>
      rw [hl, hr] at h
      simp only at h ⊢
      rcases hba : a.signature.body with _ | bodyA
      · rw [hba] at h; simp at h
      rcases hbb : b.signature.body with _ | bodyB
      · rw [hba, hbb] at h; simp at h
      rw [hba, hbb] at h
      simp only at h
      have hw := of_decide_eq_true h
      refine witnessed_mono id companion g _ _ (fun x hx => ?_) hw
      rw [List.mem_append] at hx ⊢
      exact hx.symm
    | exhausted t => rw [hl, hr] at h; simp at h
    | aborted t => rw [hl, hr] at h; simp at h
    | rejected t => rw [hl, hr] at h; simp at h
  | exhausted t => rw [hl] at h; simp at h
  | aborted t => rw [hl] at h; simp at h
  | rejected t => rw [hl] at h; simp at h

/-- The witnessed-pair slack: three times the fuel plus one, times one
call's pair cost with the identity projection. -/
def εWitOf (lambda tau kappa fuel : Nat) : ℝ≥0∞ :=
  ((3 * (fuel + 1) : Nat) : ℝ≥0∞) *
    callCost lambda 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) (commitBudget tau kappa)

/-- The witnessed-pair bound in the real experiment. -/
theorem witnessedFork_le (hvc : verifyBudget ≤ commitBudget tau kappa) (hl : 26 ≤ lambda) (fuel : Nat) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => witnessedFork snapshot) fuel)
        true ≤ εWitOf lambda tau kappa fuel := by
  have hlambda : 0 < lambda := by omega
  set B := 3 * (fuel + 1) + 2 with hB
  set ε : ℝ≥0∞ := callCost lambda 1 (commitBudget tau kappa * B) (commitBudget tau kappa) with hε
  have hcap : ∀ target : Bits lambda, Fintype.card {output : Bits lambda // id output = target} ≤ 1 :=
    fun target => by convert IdealCipherUnseenMatch.target_card_one target
  have hpub' : ∀ (query : Query lambda) (world) (n : Nat) (r), InvC (tau := tau) (kappa := kappa) n world →
      r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query
        world).support → InvC (tau := tau) (kappa := kappa) (n + 1) r.2 :=
    fun query world n r h hr => invC_pub S V verifyBudget publicKey sampleWitness query world n r h hr
  have hsignP : ∀ (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) (world) (n : Nat),
      InvC (tau := tau) (kappa := kappa) n world → n ≤ B →
      mean (resampleW resample world) (fun w' =>
        mean ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message w')
          fun r => pairMass id companion r.2.other.cipherHistory) ≤
        pairMass id companion world.other.cipherHistory + ε :=
    fun sk message world n h hn =>
      (honest_pair_bound S V verifyBudget publicKey sampleWitness id companion companion_involutive (companion_ne hlambda)
        1 hcap sk message world n h).trans (add_le_add le_rfl (callCost_mono_len _ _ _ (Nat.mul_le_mul_left _ hn)))
  have hpubP : ∀ (query : Query lambda) (world) (n : Nat), InvC (tau := tau) (kappa := kappa) n world → n ≤ B →
      mean (resampleW resample world) (fun w' =>
        mean ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query w')
          fun r => pairMass id companion r.2.other.cipherHistory) ≤
        pairMass id companion world.other.cipherHistory + ε :=
    fun query world n h hn =>
      (public_pair_bound S V verifyBudget publicKey sampleWitness id companion companion_involutive (companion_ne hlambda)
        1 hcap query world n h).trans (add_le_add le_rfl (callCost_mono_len _ _ _ (Nat.mul_le_mul_left _ hn)))
  have hprepP : ∀ (pk message : List Bool) (signature) (world) (n : Nat), InvC (tau := tau) (kappa := kappa) n world →
      n ≤ B →
      mean (resampleW resample world) (fun w' =>
        mean ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification pk
          message signature w') fun r => pairMass id companion r.2.other.cipherHistory) ≤
        pairMass id companion world.other.cipherHistory + ε :=
    fun pk message signature world n h hn =>
      (prepare_pair_bound S V verifyBudget publicKey sampleWitness id companion companion_involutive (companion_ne hlambda)
        1 hcap hvc pk message signature world n h).trans
        (add_le_add le_rfl (callCost_mono_len _ _ _ (Nat.mul_le_mul_left _ hn)))
  unfold randomEventExperiment
  rw [mean_bind_apply]
  refine mean_le_const _ _ _ fun index _ => ?_
  unfold eventExperiment cutExperiment
  rw [keygen_resampled S V verifyBudget publicKey sampleWitness]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [mean_bind_apply]
  refine mean_le_const _ _ _ fun g hg => ?_
  rw [PMF.bind_comm, mean_bind_apply]
  refine mean_le_const _ _ _ fun state _ => ?_
  rw [← PMF.bind_bind, cut_postLaw resample resample_idem _ adversary (honest_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness), PMF.bind_bind]
  simp only [mean_bind_apply, mean_bind]
  have hinv0 : InvC (tau := tau) (kappa := kappa) 0 g.2.2 := invC_keygen S V verifyBudget publicKey sampleWitness g hg
  have hnil : g.2.2.other.cipherHistory = [] := by
    have hlen := hinv0.2.2
    rw [Nat.mul_zero, Nat.le_zero] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  calc mean (resampleW resample g.2.2) (fun w =>
          mean (cut (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index.val
              (fuel + 1) g.1 g.2.1 state w ⟨[], [], []⟩) fun c =>
            mean (resampleCut resample c) fun c' =>
              (match c' with
                | .ended _ => PMF.pure false
                | .saved snapshot =>
                  (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
                    snapshot).map (witnessedFork snapshot)) true)
      ≤ mean (resampleW resample g.2.2) (fun w =>
          mean (cut (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index.val
              (fuel + 1) g.1 g.2.1 state w ⟨[], [], []⟩) fun c =>
            cutMass id companion c + ((2 * (fuel + 1) : Nat) : ℝ≥0∞) * ε) := by
        refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun c hc => ?_
        cases c with
        | ended t =>
          simp only [resampleCut, mean_pure, cutMass, PMF.pure_apply]
          simp
        | saved sn =>
          simp only [resampleCut, mean_map, cutMass]
          have hsn : InvC (tau := tau) (kappa := kappa) (0 + (fuel + 1)) sn.world :=
            cut_saved_gen (InvC (tau := tau) (kappa := kappa)) invC_mono invC_query _ adversary
              (invC_honest S V verifyBudget publicKey sampleWitness) hpub' index.val (fuel + 1) _ _ state _ _ 0
              (invC_resample 0 g.2.2 hinv0 w hw) _ hc sn rfl
          have hrem := cut_remaining_le _ adversary index.val (fuel + 1) _ _ state _ _ _ hc sn rfl
          refine (fork_witnessed_bound _ adversary id companion ε B (InvC (tau := tau) (kappa := kappa))
            invC_mono invC_resample invC_query (invC_honest S V verifyBudget publicKey sampleWitness) hpub'
            (invC_prep S V verifyBudget publicKey sampleWitness hvc) invC_update invC_restore
            (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
            (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
            (honest_keepsFamily S V verifyBudget publicKey sampleWitness)
            (publicOracle_keepsFamily S V verifyBudget publicKey sampleWitness)
            (prepareVerification_keepsFamily S V verifyBudget publicKey sampleWitness)
            (honest_grows S V verifyBudget publicKey sampleWitness) (publicOracle_grows S V verifyBudget publicKey sampleWitness)
            (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
            (honest_shiftLaw S V verifyBudget publicKey sampleWitness) (publicOracle_shiftLaw S V verifyBudget publicKey sampleWitness)
            (prepareVerification_shiftLaw S V verifyBudget publicKey sampleWitness) hsignP hpubP hprepP
            (fun snapshot => witnessedFork snapshot) (fun s' => witnessedFork_none s') (fun s' l r h => witnessedFork_left s' l r h)
            (fun s' l r g => witnessedFork_famL s' l r g) (fun s' l r g h => witnessedFork_union s' l r g h) sn
            (0 + (fuel + 1)) hsn (by omega)).trans ?_
          exact add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr (by omega)) le_rfl)
    _ = mean (resampleW resample g.2.2) (fun w =>
          mean (cut (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index.val
              (fuel + 1) g.1 g.2.1 state w ⟨[], [], []⟩) (cutMass id companion)) +
          ((2 * (fuel + 1) : Nat) : ℝ≥0∞) * ε := by
        simp only [mean_add_const]
    _ ≤ pairMass id companion g.2.2.other.cipherHistory + ((fuel + 1 : Nat) : ℝ≥0∞) * ε +
          ((2 * (fuel + 1) : Nat) : ℝ≥0∞) * ε :=
        add_le_add (cut_pair_bound _ adversary id companion ε B (InvC (tau := tau) (kappa := kappa))
          invC_resample invC_query (invC_honest S V verifyBudget publicKey sampleWitness) hpub'
          (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
          hsignP hpubP (fuel + 1) index.val _ _ state _ _ 0 hinv0 (by omega)) le_rfl
    _ = εWitOf lambda tau kappa fuel := by
        rw [hnil, pairMass_nil, zero_add, εWitOf, ← add_mul]
        push_cast
        ring

end Candidate

end
end SDitH.Proofs.ForkWitnessedBound
