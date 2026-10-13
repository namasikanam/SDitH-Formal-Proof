import SDitH.Proofs.PairOracles
import SDitH.Proofs.MeanEventCont

/-! The pair mass through the game run, the cut run and a fresh branch: from
a resampled world satisfying the counted invariant, each adversary step
raises the posterior pair mass of the cipher history by at most one call's
cost, so a run of `fuel` steps raises it by at most `fuel` costs. The
oracles' resampling laws insert a fresh resampling after every call, and
the hash queries and table updates leave the history untouched. -/

namespace SDitH.Proofs.PairRun

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq ForkRestoreEnd SharedResample HiddenSlice MeanHybrid PairMass PairOracles
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (project companion : Bits lambda → Bits lambda) (ε : ℝ≥0∞) (B : Nat)
  (Inv : Nat → GW HashInput Digest lambda s wit rnd → Prop)
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
  (hupdate : ∀ (world : GW HashInput Digest lambda s wit rnd) (input : HashInput) (n : Nat) (d : Digest), Inv n world →
    Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) })
  (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw resample (sch.sign sk message))
  (hpubLaw : ∀ query : Query, PostLaw resample (sch.publicOracle query))
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

omit [Fintype Digest] [Nonempty Digest] in
/-- The resampling law in mean form, with a continuation. -/
theorem postLaw_mean {A : Type*} (O : GW HashInput Digest lambda s wit rnd → PMF (A × GW HashInput Digest lambda s wit rnd))
    (h : PostLaw resample O) (world : GW HashInput Digest lambda s wit rnd)
    (Φ : A × GW HashInput Digest lambda s wit rnd → ℝ≥0∞) :
    mean (resampleW resample world) (fun w => mean (O w) Φ) =
      mean (resampleW resample world) (fun w => mean (O w) fun r => mean (resampleW resample r.2) fun w' => Φ (r.1, w')) := by
  have hc := congrArg (fun p => mean p Φ) (h world)
  simpa only [mean_bind, mean_map] using hc

omit [Fintype Digest] [Nonempty Digest] in
theorem step_le (fuel : Nat) : ε + (fuel : ℝ≥0∞) * ε = ((fuel + 1 : Nat) : ℝ≥0∞) * ε := by
  push_cast
  ring

omit [Fintype Digest] [Nonempty Digest] in
theorem le_step (fuel : Nat) (x : ℝ≥0∞) : x + (fuel : ℝ≥0∞) * ε ≤ x + ((fuel + 1 : Nat) : ℝ≥0∞) * ε :=
  add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ fuel)) le_rfl)

include hres hquery hpres hpub hsignLaw hpubLaw hsignP hpubP hprepP in
/-- The game run raises the pair mass by at most one cost per step. -/
theorem runW_pair_bound : ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
    (world : GW HashInput Digest lambda s wit rnd) (trace : Trace Message HashInput Query) (n : Nat),
    Inv n world → n + fuel ≤ B →
    mean (resampleW resample world) (fun w => mean (runW sch adversary fuel pk sk state w trace) fun r =>
        pairMass project companion r.2.other.cipherHistory) ≤
      pairMass project companion world.other.cipherHistory + (fuel : ℝ≥0∞) * ε := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state world trace n _ _
    simp only [runW, mean_pure, Nat.cast_zero, zero_mul, add_zero]
    exact (mean_resampleW_pairMass' project companion world).le
  | succ fuel ih =>
    intro pk sk state world trace n hn hB
    simp only [runW, mean_bind]
    rw [mean_comm]
    refine mean_le_const _ _ _ fun action _ => ?_
    cases action with
    | abort =>
      dsimp only
      simp only [mean_pure]
      rw [mean_resampleW_pairMass']
      exact le_self_add
    | finish message signature =>
      dsimp only
      simp only [mean_map]
      refine (hprepP pk message signature world n hn (by omega)).trans ?_
      refine add_le_add le_rfl ?_
      calc ε = (1 : ℝ≥0∞) * ε := (one_mul ε).symm
        _ ≤ _ := mul_le_mul' (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le fuel)) le_rfl
    | sign message next =>
      dsimp only
      simp only [mean_bind]
      rw [postLaw_mean _ (hsignLaw sk message) world]
      calc mean (resampleW resample world) (fun w => mean (sch.sign sk message w) fun r =>
              mean (resampleW resample r.2) fun w' =>
                mean (runW sch adversary fuel pk sk (next r.1) w'
                  { trace with signingRequests := message :: trace.signingRequests }) fun r' =>
                  pairMass project companion r'.2.other.cipherHistory)
          ≤ mean (resampleW resample world) (fun w => mean (sch.sign sk message w) fun r =>
              pairMass project companion r.2.other.cipherHistory + (fuel : ℝ≥0∞) * ε) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            exact ih pk sk (next r.1) r.2 _ (n + 1) (hpres sk message w n r (hres n world hn w hw) hr) (by omega)
        _ = mean (resampleW resample world) (fun w => mean (sch.sign sk message w) fun r =>
              pairMass project companion r.2.other.cipherHistory) + (fuel : ℝ≥0∞) * ε := by
            simp only [mean_add_const]
        _ ≤ pairMass project companion world.other.cipherHistory + ε + (fuel : ℝ≥0∞) * ε :=
            add_le_add (hsignP sk message world n hn (by omega)) le_rfl
        _ = _ := by rw [add_assoc, step_le]
    | hash input next =>
      dsimp only
      simp only [mean_bind]
      have hT : ∀ w ∈ (resampleW resample world).support,
          (mean (Spec.RandomOracle.query w.hashTable input) fun result =>
            mean (runW sch adversary fuel pk sk (next result.1) { w with hashTable := result.2 }
              { trace with hashRequests := input :: trace.hashRequests }) fun r =>
              pairMass project companion r.2.other.cipherHistory) =
          mean (Spec.RandomOracle.query world.hashTable input) fun result =>
            mean (runW sch adversary fuel pk sk (next result.1) { w with hashTable := result.2 }
              { trace with hashRequests := input :: trace.hashRequests }) fun r =>
              pairMass project companion r.2.other.cipherHistory := by
        intro w hw
        rw [hashTable_of_mem resample world w hw]
      rw [mean_congr_support _ _ _ hT, mean_comm]
      refine mean_le_const _ _ _ fun result hresult => ?_
      refine (le_of_eq (mean_resampleW_update' world (fun _ => result.2) fun y =>
        mean (runW sch adversary fuel pk sk (next result.1) y { trace with hashRequests := input :: trace.hashRequests })
          fun r => pairMass project companion r.2.other.cipherHistory)).trans ?_
      refine (ih pk sk (next result.1) _ _ (n + 1) (hquery world input n result hn hresult) (by omega)).trans ?_
      exact le_step ε fuel _
    | query input next =>
      dsimp only
      simp only [mean_bind]
      rw [postLaw_mean _ (hpubLaw input) world]
      calc mean (resampleW resample world) (fun w => mean (sch.publicOracle input w) fun r =>
              mean (resampleW resample r.2) fun w' =>
                mean (runW sch adversary fuel pk sk (next r.1) w'
                  { trace with publicRequests := input :: trace.publicRequests }) fun r' =>
                  pairMass project companion r'.2.other.cipherHistory)
          ≤ mean (resampleW resample world) (fun w => mean (sch.publicOracle input w) fun r =>
              pairMass project companion r.2.other.cipherHistory + (fuel : ℝ≥0∞) * ε) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            exact ih pk sk (next r.1) r.2 _ (n + 1) (hpub input w n r (hres n world hn w hw) hr) (by omega)
        _ = mean (resampleW resample world) (fun w => mean (sch.publicOracle input w) fun r =>
              pairMass project companion r.2.other.cipherHistory) + (fuel : ℝ≥0∞) * ε := by
            simp only [mean_add_const]
        _ ≤ pairMass project companion world.other.cipherHistory + ε + (fuel : ℝ≥0∞) * ε :=
            add_le_add (hpubP input world n hn (by omega)) le_rfl
        _ = _ := by rw [add_assoc, step_le]

/-- The pair mass of a cut: the saved snapshot's world, nothing on an ended run. -/
def cutMass : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State →
    ℝ≥0∞
  | .ended _ => 0
  | .saved snapshot => pairMass project companion snapshot.world.other.cipherHistory

include hres hquery hpres hpub hsignLaw hpubLaw hsignP hpubP in
/-- The cut run raises the pair mass of the saved world by at most one cost
per step. -/
theorem cut_pair_bound : ∀ (fuel index : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
    (world : GW HashInput Digest lambda s wit rnd) (trace : Trace Message HashInput Query) (n : Nat),
    Inv n world → n + fuel ≤ B →
    mean (resampleW resample world) (fun w => mean (cut sch adversary index fuel pk sk state w trace)
        (cutMass project companion)) ≤
      pairMass project companion world.other.cipherHistory + (fuel : ℝ≥0∞) * ε := by
  intro fuel
  induction fuel with
  | zero =>
    intro index pk sk state world trace n _ _
    simp only [cut, mean_pure, cutMass]
    rw [mean_const]
    exact zero_le _
  | succ fuel ih =>
    intro index pk sk state world trace n hn hB
    simp only [cut, mean_bind]
    rw [mean_comm]
    refine mean_le_const _ _ _ fun action _ => ?_
    cases action with
    | abort =>
      dsimp only
      simp only [mean_pure, cutMass]
      rw [mean_const]
      exact zero_le _
    | finish message signature =>
      dsimp only
      simp only [mean_map, cutMass, mean_const]
      exact zero_le _
    | sign message next =>
      dsimp only
      simp only [mean_bind]
      rw [postLaw_mean _ (hsignLaw sk message) world]
      calc mean (resampleW resample world) (fun w => mean (sch.sign sk message w) fun r =>
              mean (resampleW resample r.2) fun w' =>
                mean (cut sch adversary index fuel pk sk (next r.1) w'
                  { trace with signingRequests := message :: trace.signingRequests }) (cutMass project companion))
          ≤ mean (resampleW resample world) (fun w => mean (sch.sign sk message w) fun r =>
              pairMass project companion r.2.other.cipherHistory + (fuel : ℝ≥0∞) * ε) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            exact ih index pk sk (next r.1) r.2 _ (n + 1) (hpres sk message w n r (hres n world hn w hw) hr) (by omega)
        _ = mean (resampleW resample world) (fun w => mean (sch.sign sk message w) fun r =>
              pairMass project companion r.2.other.cipherHistory) + (fuel : ℝ≥0∞) * ε := by
            simp only [mean_add_const]
        _ ≤ pairMass project companion world.other.cipherHistory + ε + (fuel : ℝ≥0∞) * ε :=
            add_le_add (hsignP sk message world n hn (by omega)) le_rfl
        _ = _ := by rw [add_assoc, step_le]
    | hash input next =>
      dsimp only
      cases index with
      | zero =>
        simp only [mean_pure, cutMass]
        rw [mean_resampleW_pairMass']
        exact le_self_add
      | succ index =>
        simp only [mean_bind]
        have hT : ∀ w ∈ (resampleW resample world).support,
            (mean (Spec.RandomOracle.query w.hashTable input) fun result =>
              mean (cut sch adversary index fuel pk sk (next result.1) { w with hashTable := result.2 }
                { trace with hashRequests := input :: trace.hashRequests }) (cutMass project companion)) =
            mean (Spec.RandomOracle.query world.hashTable input) fun result =>
              mean (cut sch adversary index fuel pk sk (next result.1) { w with hashTable := result.2 }
                { trace with hashRequests := input :: trace.hashRequests }) (cutMass project companion) := by
          intro w hw
          rw [hashTable_of_mem resample world w hw]
        rw [mean_congr_support _ _ _ hT, mean_comm]
        refine mean_le_const _ _ _ fun result hresult => ?_
        refine (le_of_eq (mean_resampleW_update' world (fun _ => result.2) fun y =>
          mean (cut sch adversary index fuel pk sk (next result.1) y { trace with hashRequests := input :: trace.hashRequests })
            (cutMass project companion))).trans ?_
        refine (ih index pk sk (next result.1) _ _ (n + 1) (hquery world input n result hn hresult) (by omega)).trans ?_
        exact le_step ε fuel _
    | query input next =>
      dsimp only
      simp only [mean_bind]
      rw [postLaw_mean _ (hpubLaw input) world]
      calc mean (resampleW resample world) (fun w => mean (sch.publicOracle input w) fun r =>
              mean (resampleW resample r.2) fun w' =>
                mean (cut sch adversary index fuel pk sk (next r.1) w'
                  { trace with publicRequests := input :: trace.publicRequests }) (cutMass project companion))
          ≤ mean (resampleW resample world) (fun w => mean (sch.publicOracle input w) fun r =>
              pairMass project companion r.2.other.cipherHistory + (fuel : ℝ≥0∞) * ε) := by
            refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr => ?_
            exact ih index pk sk (next r.1) r.2 _ (n + 1) (hpub input w n r (hres n world hn w hw) hr) (by omega)
        _ = mean (resampleW resample world) (fun w => mean (sch.publicOracle input w) fun r =>
              pairMass project companion r.2.other.cipherHistory) + (fuel : ℝ≥0∞) * ε := by
            simp only [mean_add_const]
        _ ≤ pairMass project companion world.other.cipherHistory + ε + (fuel : ℝ≥0∞) * ε :=
            add_le_add (hpubP input world n hn (by omega)) le_rfl
        _ = _ := by rw [add_assoc, step_le]

include hres hquery hpres hpub hupdate hsignLaw hpubLaw hsignP hpubP hprepP in
/-- A fresh branch with its final world raises the pair mass by at most one
cost per remaining step. -/
theorem freshBranchW_pair_bound
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (n : Nat) (hn : Inv n snapshot.world) (hB : n + 1 + snapshot.remaining ≤ B) :
    mean (resampleW resample snapshot.world) (fun y =>
        mean (freshBranchW sch adversary { snapshot with world := y }) fun rw =>
          pairMass project companion rw.2.other.cipherHistory) ≤
      pairMass project companion snapshot.world.other.cipherHistory + (snapshot.remaining : ℝ≥0∞) * ε := by
  simp only [freshBranchW, mean_bind, mean_map, mean_const]
  rw [mean_comm]
  refine mean_le_const _ _ _ fun answer _ => ?_
  have hT : ∀ y ∈ (resampleW resample snapshot.world).support,
      (mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
        { y with hashTable := Function.update y.hashTable snapshot.input (some answer) }
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        pairMass project companion r.2.other.cipherHistory) =
      mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
        { y with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        pairMass project companion r.2.other.cipherHistory := by
    intro y hy
    rw [hashTable_of_mem resample snapshot.world y hy]
  rw [mean_congr_support _ _ _ hT]
  refine (le_of_eq (mean_resampleW_update' snapshot.world
    (fun _ => Function.update snapshot.world.hashTable snapshot.input (some answer)) fun y =>
      mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        pairMass project companion r.2.other.cipherHistory)).trans ?_
  exact runW_pair_bound sch adversary project companion ε B Inv hres hquery hpres hpub hsignLaw hpubLaw hsignP hpubP hprepP
    snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) _ _ (n + 1)
    (hupdate snapshot.world snapshot.input n answer hn) (by omega)

end
end SDitH.Proofs.PairRun
