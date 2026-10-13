import SDitH.Proofs.MeanHybridContW
import SDitH.Proofs.MeanForkCont2
import SDitH.Proofs.ForkPruneCompat

/-! The mean-form hybrid chain with the per-call bound restricted to
prune-compatible continuations. The per-call bound is taken for
continuations compatible with pruning at every key list, whose touching
functional is the touching probability of a process on the run's result
keeping the invariant within an end budget; the run hybrid passes its
continuation down unchanged, the fresh branch's continuation is its
finalization followed by the event, and the fork continuation's process is
the second branch's final world. -/

namespace SDitH.Proofs.MeanHybridCompat

open Spec.SignatureSecurity Spec.SignatureReplay
open Spec.IdealCipher (Family)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open RunHybrid GameResample ChargeExpect ChargeCutExpect RowStoredPosterior MeanHybrid MeanHybridCont MeanHybridContW RunWorld
open CipherResample SharedPrune HiddenEntries GamePrune GamePruneReverse GamePruneGen PruneCompatClosure ForkPruneCompat
open ForkRestore ForkRestoreLemmas ForkRestoreEnd ForkRestoreEq MeanForkCont MeanForkCont2 HiddenSlice
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (ε : ℝ≥0∞) (B B' : Nat)
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

/-- The per-call bound in mean form for compatible continuations of the run
with its final world: compatible with pruning at every key list, with the
touching functional of a process on the result keeping the invariant within
the end budget. -/
def SignRunWMeanP : Prop :=
  ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (m : Nat) (world : GW HashInput Digest lambda s wit rnd), Inv m world →
    ∀ (fuel : Nat) (pk : PublicKey) (next : Signature → State) (trace : Trace Message HashInput Query), m + fuel + 1 ≤ B →
    ∀ (h : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
        GW HashInput Digest lambda s wit rnd → PMF Bool) (c : Bool)
      (Cp : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
        GW HashInput Digest lambda s wit rnd → PMF (GW HashInput Digest lambda s wit rnd)),
      (∀ K, PruneCompat K (fun t => (h t) c) (fun r => mean (Cp r) fun w => indicator (touchesG K w))) →
      (∀ r, Inv B r.2 → ∀ w ∈ (Cp r).support, Inv B' w) →
    mean (resampleW resample world) (fun w => ((sch₁.sign sk message w).bind fun r =>
        (runW sch₂ adversary fuel pk sk (next r.1) r.2 trace).bind h) c) ≤
      mean (resampleW resample world) (fun w => ((sch₂.sign sk message w).bind fun r =>
        (runW sch₂ adversary fuel pk sk (next r.1) r.2 trace).bind h) c) + ε

include hagree hres hquery hpres hpub hsignLaw hpubLaw in
/-- The hybrid in mean form of the run with its final world, for a
compatible continuation. -/
theorem runW_le_runW_mean_contP (hsign : SignRunWMeanP sch₁ sch₂ adversary Good ε B B' Inv)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State) (world : GW HashInput Digest lambda s wit rnd)
    (trace : Trace Message HashInput Query) (m : Nat) (hm : Inv m world) (hB : m + fuel ≤ B)
    (h : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → PMF Bool) (c : Bool)
    (Cp : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → PMF (GW HashInput Digest lambda s wit rnd))
    (hc : ∀ K, PruneCompat K (fun t => (h t) c) (fun r => mean (Cp r) fun w => indicator (touchesG K w)))
    (hCp : ∀ r, Inv B r.2 → ∀ w ∈ (Cp r).support, Inv B' w) :
    mean (resampleW resample world) (fun w => ((runW sch₁ adversary fuel pk sk state w trace).bind h) c) ≤
      mean (resampleW resample world) (fun w => ((runW sch₂ adversary fuel pk sk state w trace).bind h) c) + fuel * ε := by
  induction fuel generalizing state world trace m with
  | zero =>
    simp only [runW, Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  | succ fuel ih =>
    have hstep : (fuel : ℝ≥0∞) * ε ≤ ((fuel + 1 : Nat) : ℝ≥0∞) * ε :=
      mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ fuel)) le_rfl
    simp only [runW, PMF.bind_bind, mean_bind_apply (adversary.step pk state)]
    rw [mean_comm]
    conv_rhs => rw [mean_comm, ← mean_add_const]
    refine mean_le_mean _ _ _ fun action _ => ?_
    cases action with
    | abort =>
      dsimp only
      exact le_self_add
    | finish message signature =>
      dsimp only
      rw [hagree.prepareVerification, hagree.signatureDigest]
      exact le_self_add
    | sign message next =>
      dsimp only
      simp only [PMF.bind_bind]
      calc mean (resampleW resample world) (fun w => ((sch₁.sign sk message w).bind fun r =>
              (runW sch₁ adversary fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c)
          = mean (resampleW resample world) (fun w => mean (sch₁.sign sk message w) fun r =>
              mean (resampleW resample r.2) fun w' => ((runW sch₁ adversary fuel pk sk (next r.1) w'
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) := by
            simp only [mean_bind_apply]
            exact postLaw_mean (hsignLaw sk message) world _
        _ ≤ mean (resampleW resample world) (fun w => mean (sch₁.sign sk message w) fun r =>
              mean (resampleW resample r.2) (fun w' => ((runW sch₂ adversary fuel pk sk (next r.1) w'
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + fuel * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih (next r.1) r.2 _ (m + 1) (hpres sk message w m r (hres m world hm w hw) hr) (by omega)
        _ = mean (resampleW resample world) (fun w => ((sch₁.sign sk message w).bind fun r =>
              (runW sch₂ adversary fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + fuel * ε := by
            simp only [mean_add_const, mean_bind_apply]
            congr 1
            exact (postLaw_mean (hsignLaw sk message) world (fun r => mean (runW sch₂ adversary fuel pk sk (next r.1) r.2
              { trace with signingRequests := message :: trace.signingRequests }) fun a => (h a) c)).symm
        _ ≤ (mean (resampleW resample world) (fun w => ((sch₂.sign sk message w).bind fun r =>
              (runW sch₂ adversary fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + ε) + fuel * ε :=
            add_le_add (hsign sk hsk message m world hm fuel pk next _ (by omega) h c Cp hc hCp) le_rfl
        _ = _ := by push_cast; ring
    | hash input next =>
      dsimp only
      simp only [PMF.bind_bind]
      have hform : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query Answer),
          mean (resampleW resample world) (fun w => ((Spec.RandomOracle.query w.hashTable input).bind fun r =>
            (runW sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
              { trace with hashRequests := input :: trace.hashRequests }).bind h) c) =
          mean (Spec.RandomOracle.query world.hashTable input) fun r =>
            mean (resampleW resample { world with hashTable := r.2 }) fun w' =>
              ((runW sch adversary fuel pk sk (next r.1) w'
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c := by
        intro sch
        calc _ = mean (resampleW resample world) (fun w => ((Spec.RandomOracle.query world.hashTable input).bind fun r =>
              (runW sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c) := by
              unfold mean
              refine tsum_congr fun w => ?_
              by_cases hw : w ∈ (resampleW resample world).support
              · simp only [hashTable_of_mem resample world w hw]
              · rw [PMF.mem_support_iff, not_not] at hw
                simp [hw]
          _ = mean (Spec.RandomOracle.query world.hashTable input) fun r =>
              mean (resampleW resample world) fun w => ((runW sch adversary fuel pk sk (next r.1) { w with hashTable := r.2 }
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c := by
              simp only [mean_bind_apply]
              exact mean_comm _ _ _
          _ = _ := by
              refine congrArg _ (funext fun r => ?_)
              exact (mean_resampleW_update resample world r.2 (fun w' => ((runW sch adversary fuel pk sk (next r.1) w'
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c)).symm
      rw [hform sch₁, hform sch₂]
      refine (mean_le_mean _ _ _ fun r hr =>
        ih (next r.1) _ _ (m + 1) (hquery world input m r hm hr) (by omega)).trans ?_
      rw [mean_add_const]
      exact add_le_add le_rfl hstep
    | query input next =>
      dsimp only
      simp only [PMF.bind_bind, hagree.publicOracle]
      calc mean (resampleW resample world) (fun w => ((sch₂.publicOracle input w).bind fun r =>
              (runW sch₁ adversary fuel pk sk (next r.1) r.2
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c)
          = mean (resampleW resample world) (fun w => mean (sch₂.publicOracle input w) fun r =>
              mean (resampleW resample r.2) fun w' => ((runW sch₁ adversary fuel pk sk (next r.1) w'
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) := by
            simp only [mean_bind_apply]
            exact postLaw_mean (hpubLaw input) world _
        _ ≤ mean (resampleW resample world) (fun w => mean (sch₂.publicOracle input w) fun r =>
              mean (resampleW resample r.2) (fun w' => ((runW sch₂ adversary fuel pk sk (next r.1) w'
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) + fuel * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih (next r.1) r.2 _ (m + 1) (hpub input w m r (hres m world hm w hw) hr) (by omega)
        _ = mean (resampleW resample world) (fun w => ((sch₂.publicOracle input w).bind fun r =>
              (runW sch₂ adversary fuel pk sk (next r.1) r.2
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) + fuel * ε := by
            simp only [mean_add_const, mean_bind_apply]
            congr 1
            exact (postLaw_mean (hpubLaw input) world (fun r => mean (runW sch₂ adversary fuel pk sk (next r.1) r.2
              { trace with publicRequests := input :: trace.publicRequests }) fun a => (h a) c)).symm
        _ ≤ _ := add_le_add le_rfl hstep

include hagree hmono hres hquery hpres hpub hupdate hsignLaw hpubLaw in
/-- The fresh branch with its final world, from a resampled snapshot world,
is within the remaining fuel times the per-call bound. -/
theorem freshBranchW_le_meanP (hsign : SignRunWMeanP sch₁ sch₂ adversary Good ε B B' Inv) (hBB' : B ≤ B')
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world) (hB : m + 1 + snapshot.remaining ≤ B)
    (Kc : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → PMF Bool)
    (hKc : ∀ (answer : Digest) (Kk : List (Bits lambda)), PruneCompat Kk
      (fun t => (((finalize t.1).bind fun c => Kc (⟨answer, c⟩, t.2)) true))
      (fun r => mean (PMF.pure r.2) fun w => indicator (touchesG Kk w))) :
    mean (resampleW resample snapshot.world) (fun y =>
        mean (freshBranchW sch₁ adversary { snapshot with world := y }) fun rw => (Kc rw) true) ≤
      mean (resampleW resample snapshot.world) (fun y =>
        mean (freshBranchW sch₂ adversary { snapshot with world := y }) fun rw => (Kc rw) true) +
        snapshot.remaining * ε := by
  simp only [freshBranchW, mean_bind, mean_map]
  rw [mean_comm]
  conv_rhs => rw [mean_comm, ← mean_add_const]
  refine mean_le_mean _ _ _ fun answer _ => ?_
  dsimp only
  rw [mean_resampleW_update' snapshot.world (fun t => Function.update t snapshot.input (some answer))
    (fun y => mean (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        mean (finalize r.1) fun c => (Kc (⟨answer, c⟩, r.2)) true),
    mean_resampleW_update' snapshot.world (fun t => Function.update t snapshot.input (some answer))
    (fun y => mean (runW sch₂ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        mean (finalize r.1) fun c => (Kc (⟨answer, c⟩, r.2)) true)]
  have hF : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer) (y : GW HashInput Digest lambda s wit rnd),
      mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })
        (fun r => mean (finalize r.1) fun c => (Kc (⟨answer, c⟩, r.2)) true) =
      ((runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).bind fun r =>
          (finalize r.1).bind fun c => Kc (⟨answer, c⟩, r.2)) true := by
    intro sch y
    simp only [mean_bind_apply]
  simp only [hF]
  exact runW_le_runW_mean_contP sch₁ sch₂ adversary hagree Good ε B B' Inv hres hquery hpres hpub hsignLaw hpubLaw
    hsign snapshot.remaining _ _ hsk _ _ _ (m + 1) (hupdate snapshot.world snapshot.input m answer hm) (by omega) _ true
    (fun r => PMF.pure r.2) (hKc answer) (fun r hr w hw => by
      rw [PMF.support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact hmono B B' r.2 hBB' hr)

/-- The second branch's continuation after the first branch's checked
result, finalization then the end-resampled event, is compatible, with the
touching indicator of its own world. -/
theorem rightCont_pruneCompat
    (hErightW : ∀ snapshot' left t w₀ f H b₁ b₂ (a' : Digest),
      E snapshot' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) =
        E snapshot' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩)))
    (hE : ∀ (K : List (Bits lambda)) snapshot' c c' (a a' : Digest),
      PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
        (fun r => rightEval snapshot' E a c c' a' r.2) (fun r => indicator (touchesG K r.2)))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (a : Digest) (c : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (answer' : Digest) (Kk : List (Bits lambda)) :
    PruneCompat Kk
      (fun t => (((finalize t.1).bind fun c' =>
        (fun rw : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
            GW HashInput Digest lambda s wit rnd => (resampleW resample rw.2).map fun w'' =>
          E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1)))
          (⟨answer', c'⟩, t.2)) true))
      (fun r => mean (PMF.pure r.2) fun w => indicator (touchesG Kk w)) :=
  pruneCompat_congr Kk _ _ _ _ (fun t => by simp only [mean_bind_apply, map_true, rightEval])
    (fun r => by simp only [mean_const, mean_pure])
    (pruneCompat_finalize Kk (fun c' w => rightEval snapshot E a c c' answer' w) (fun _ w => indicator (touchesG Kk w))
      (fun t w₀ f H b₁ b₂ w => by simp only [rightEval, hErightW]) (fun _ _ _ _ _ _ _ => rfl)
      (fun c' => hE Kk snapshot c c' a answer'))

/-- The fork continuation's process: the second branch's final world. -/
def forkProc (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (r : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) : PMF (GW HashInput Digest lambda s wit rnd) :=
  (resampleW resample r.2).bind fun w' => (finalize (withWorld r.1 w')).bind fun _ =>
    (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }).map fun rw => rw.2

/-- The fork continuation, in the hybrid's form, is compatible with the
touching of its process. -/
theorem forkCont_pruneCompat'
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query Answer)
    (hsignLaw : ∀ sk m, PostLaw resample (sch.sign sk m)) (hpubLaw : ∀ q, PostLaw resample (sch.publicOracle q))
    (hprepLaw : ∀ pk m sig, PostLaw resample (sch.prepareVerification pk m sig))
    (hsignP : ∀ K sk m, PruneLaw K (sch.sign sk m)) (hpubP : ∀ K q, PruneLaw K (sch.publicOracle q))
    (hprepP : ∀ K pk m sig, PruneLaw K (sch.prepareVerification pk m sig))
    (hsignG : ∀ sk m, Grows (sch.sign sk m)) (hpubG : ∀ q, Grows (sch.publicOracle q))
    (hprepG : ∀ pk m sig, Grows (sch.prepareVerification pk m sig))
    (hsignK : ∀ sk m, Keeps (sch.sign sk m)) (hpubK : ∀ q, Keeps (sch.publicOracle q))
    (hprepK : ∀ pk m sig, Keeps (sch.prepareVerification pk m sig))
    (hEleftW : ∀ snapshot' (a : Digest) t w₀ f H b₁ b₂ right,
      E snapshot' (some (⟨a, ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩, right)) =
        E snapshot' (some (⟨a, ⟨withWorld t w₀, b₁, b₂⟩⟩, right)))
    (hErightW : ∀ snapshot' left t w₀ f H b₁ b₂ (a' : Digest),
      E snapshot' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) =
        E snapshot' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩)))
    (hE : ∀ (K : List (Bits lambda)) snapshot' c c' (a a' : Digest),
      PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
        (fun r => rightEval snapshot' E a c c' a' r.2) (fun r => indicator (touchesG K r.2)))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (a : Digest) (Kk : List (Bits lambda)) :
    PruneCompat Kk
      (fun t => (((fun r => (resampleW resample r.2).bind fun w' => (finalize (withWorld r.1 w')).bind fun c =>
        (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }).bind fun rw =>
          (resampleW resample rw.2).map fun w'' =>
            E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) t) true))
      (fun r => mean (forkProc adversary sch snapshot r) fun w => indicator (touchesG Kk w)) :=
  pruneCompat_congr Kk _ _ _ _ (fun r => by simp only [forkCont, leftEval, mean_bind_apply, map_true])
    (fun r => by simp only [forkProc, forkTouch, leftTouch, mean_bind, mean_map])
    (forkCont_pruneCompat Kk sch adversary snapshot E a (fun _ _ _ w => indicator (touchesG Kk w)) hsignLaw hpubLaw hprepLaw
      (hsignP Kk) (hpubP Kk) (hprepP Kk) hsignG hpubG hprepG hsignK hpubK hprepK (fun snapshot' => hEleftW snapshot' a)
      hErightW (fun _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ => rfl) (fun c c' a' => hE Kk snapshot c c' a a'))

include hmono hres hquery hpres₂ hpub hprepInv hupdate hrestore in
/-- The fork continuation's process keeps the invariant within the end
budget. -/
theorem forkProc_inv
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (m : Nat) (hm : Inv m snapshot.world) (hmB : m ≤ B) (hrem : snapshot.remaining ≤ B) (hB' : 2 * B + 1 ≤ B') :
    ∀ r, Inv B r.2 → ∀ w ∈ (forkProc adversary sch₂ snapshot r).support, Inv B' w := by
  intro r hr w hw
  simp only [forkProc, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hw
  obtain ⟨w', hw', c, -, rw, hrw, rfl⟩ := hw
  have hY : Inv B (restore snapshot.world w') := hrestore B _ _ (hmono m B snapshot.world hmB hm) (hres B r.2 hr w' hw')
  simp only [freshBranchW, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hrw
  obtain ⟨answer', -, r', hr', checked, -, rfl⟩ := hrw
  have h := runW_inv sch₂ sch₂ adversary ⟨rfl, rfl, rfl, rfl⟩ Inv hmono hquery hpres₂ hpub hprepInv snapshot.remaining _ _ _ _ _
    (B + 1) (hupdate _ snapshot.input B answer' hY) r' hr'
  exact hmono _ _ _ (by omega) h

/-- The inner evaluation after the first branch: the resampling, the
finalization, the second branch from the restored snapshot and the event at
an end-resampled family. -/
def innerEval (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (a : Digest) (r : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) : ℝ≥0∞ :=
  mean (resampleW resample r.2) fun w' =>
    mean (finalize (withWorld r.1 w')) fun c =>
      mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
        mean (resampleW resample rw.2) fun w'' =>
          indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1)))

include hagree hmono hres hquery hpres hpub hupdate hsignLaw hpubLaw in
/-- The core of step A: the second branch from the restored world, with the
end-resampled event, is replaced within the remaining fuel times the
per-call bound. -/
theorem stepA_core (hsign : SignRunWMeanP sch₁ sch₂ adversary Good ε B B' Inv) (hB' : 2 * B + 1 ≤ B')
    (hErightW : ∀ snapshot' left t w₀ f H b₁ b₂ (a' : Digest),
      E snapshot' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) =
        E snapshot' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩)))
    (hE : ∀ (K : List (Bits lambda)) snapshot' c c' (a a' : Digest),
      PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
        (fun r => rightEval snapshot' E a c c' a' r.2) (fun r => indicator (touchesG K r.2)))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hB : m + 2 * snapshot.remaining + 2 ≤ B) (a : Digest)
    (c : Checked Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (r : Terminal Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd)
    (hInvY : Inv (m + 1 + snapshot.remaining) (restore snapshot.world r.2)) :
    mean (resampleW resample (restore snapshot.world r.2)) (fun y' =>
        mean (freshBranchW sch₁ adversary { snapshot with world := y' }) fun rw =>
          (((resampleW resample rw.2).map fun w'' =>
            E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) true)) ≤
      mean (resampleW resample (restore snapshot.world r.2)) (fun y' =>
        mean (freshBranchW sch₂ adversary { snapshot with world := y' }) fun rw =>
          (((resampleW resample rw.2).map fun w'' =>
            E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) true)) +
        snapshot.remaining * ε := by
  have h := freshBranchW_le_meanP sch₁ sch₂ adversary hagree Good ε B B' Inv hmono hres hquery hpres hpub hupdate hsignLaw
    hpubLaw hsign (by omega) { snapshot with world := restore snapshot.world r.2 } hsk (m + 1 + snapshot.remaining) hInvY
    (by show m + 1 + snapshot.remaining + 1 + snapshot.remaining ≤ B; omega)
    (fun rw => (resampleW resample rw.2).map fun w'' =>
      E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1)))
    (fun answer' Kk => rightCont_pruneCompat E hErightW hE snapshot a c answer' Kk)
  exact h

include hagree hmono hres hquery hpres hpub hprepInv hupdate hrestore hsignLaw hpubLaw in
/-- Step A of the fork hybrid for compatible continuations: the second
branch is replaced, for every output of the first. -/
theorem stepA (hsign : SignRunWMeanP sch₁ sch₂ adversary Good ε B B' Inv) (hB' : 2 * B + 1 ≤ B')
    (hEleft : ∀ snapshot' left right g, E snapshot' (some (setFamilyBranch g left, right)) = E snapshot' (some (left, right)))
    (hErightW : ∀ snapshot' left t w₀ f H b₁ b₂ (a' : Digest),
      E snapshot' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) =
        E snapshot' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩)))
    (hE : ∀ (K : List (Bits lambda)) snapshot' c c' (a a' : Digest),
      PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
        (fun r => rightEval snapshot' E a c c' a' r.2) (fun r => indicator (touchesG K r.2)))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world) (hB : m + 2 * snapshot.remaining + 2 ≤ B) (a : Digest) :
    ∀ y ∈ (resampleW resample
        { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) }).support,
      ∀ r ∈ (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).support,
      innerEval adversary E sch₁ snapshot a r ≤ innerEval adversary E sch₂ snapshot a r + snapshot.remaining * ε := by
    intro y hy r hr
    have hInvr : Inv (m + 1 + snapshot.remaining) r.2 :=
      runW_inv sch₁ sch₂ adversary hagree Inv hmono hquery hpres hpub hprepInv _ _ _ _ _ _ (m + 1) (hres _ _ (hupdate snapshot.world snapshot.input m a hm) y hy) r hr
    -- the first branch's checked terminal carries the resampled family, which the event ignores
    have hleft : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest
        (Spec.SharedScheme.World lambda s wit rnd) Query Answer),
        innerEval adversary E sch snapshot a r = mean (finalize r.1) fun c => mean (resampleW resample r.2) fun w' =>
          mean (freshBranchW sch adversary { snapshot with world := restore snapshot.world w' }) fun rw =>
            mean (resampleW resample rw.2) fun w'' =>
              indicator (E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) := by
      intro sch
      simp only [innerEval]
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
    exact stepA_core sch₁ sch₂ adversary hagree Good ε B B' Inv hmono hres hquery hpres hpub hupdate hsignLaw hpubLaw E hsign hB'
      hErightW hE snapshot hsk m hB a c r hInvY

include hagree hmono hres hquery hpres hpres₂ hpub hprepInv hupdate hrestore hsignLaw hsignLaw₂ hpubLaw in
/-- Step B of the fork hybrid for compatible continuations: the first
branch is replaced, with the second scheme's second branch. -/
theorem stepB (hsign : SignRunWMeanP sch₁ sch₂ adversary Good ε B B' Inv) (hB' : 2 * B + 1 ≤ B')
    (hprepLaw₂ : ∀ pk m sig, PostLaw resample (sch₂.prepareVerification pk m sig))
    (hsignP₂ : ∀ K sk m, PruneLaw K (sch₂.sign sk m)) (hpubP₂ : ∀ K q, PruneLaw K (sch₂.publicOracle q))
    (hprepP₂ : ∀ K pk m sig, PruneLaw K (sch₂.prepareVerification pk m sig))
    (hsignG₂ : ∀ sk m, Grows (sch₂.sign sk m)) (hpubG₂ : ∀ q, Grows (sch₂.publicOracle q))
    (hprepG₂ : ∀ pk m sig, Grows (sch₂.prepareVerification pk m sig))
    (hsignK₂ : ∀ sk m, Keeps (sch₂.sign sk m)) (hpubK₂ : ∀ q, Keeps (sch₂.publicOracle q))
    (hprepK₂ : ∀ pk m sig, Keeps (sch₂.prepareVerification pk m sig))
    (hEleftW : ∀ snapshot' (a : Digest) t w₀ f H b₁ b₂ right,
      E snapshot' (some (⟨a, ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩, right)) =
        E snapshot' (some (⟨a, ⟨withWorld t w₀, b₁, b₂⟩⟩, right)))
    (hErightW : ∀ snapshot' left t w₀ f H b₁ b₂ (a' : Digest),
      E snapshot' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) =
        E snapshot' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩)))
    (hE : ∀ (K : List (Bits lambda)) snapshot' c c' (a a' : Digest),
      PruneCompat (Message := Message) (Signature := Signature) (Query := Query) K
        (fun r => rightEval snapshot' E a c c' a' r.2) (fun r => indicator (touchesG K r.2)))
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world) (hB : m + 2 * snapshot.remaining + 2 ≤ B) (a : Digest) :
    mean (resampleW resample
        { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) }) (fun y =>
      mean (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })
        (innerEval adversary E sch₂ snapshot a)) ≤
    mean (resampleW resample
        { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) }) (fun y =>
      mean (runW sch₂ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })
        (innerEval adversary E sch₂ snapshot a)) + snapshot.remaining * ε := by
    have hF : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest
        (Spec.SharedScheme.World lambda s wit rnd) Query Answer) (y : GW HashInput Digest lambda s wit rnd),
        mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y
              { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })
          (innerEval adversary E sch₂ snapshot a) =
        ((runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y
              { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).bind fun r =>
          (resampleW resample r.2).bind fun w' =>
            (finalize (withWorld r.1 w')).bind fun c =>
              (freshBranchW sch₂ adversary { snapshot with world := restore snapshot.world w' }).bind fun rw =>
                (resampleW resample rw.2).map fun w'' =>
                  E { snapshot with world := setFamily snapshot.world w''.other.family } (some (⟨a, c⟩, rw.1))) true := by
      intro sch y
      unfold innerEval
      simp only [mean_bind_apply, map_true]
    simp only [hF]
    exact runW_le_runW_mean_contP sch₁ sch₂ adversary hagree Good ε B B' Inv hres hquery hpres hpub hsignLaw hpubLaw
      hsign snapshot.remaining _ _ hsk _ _ _ (m + 1) (hupdate snapshot.world snapshot.input m a hm) (by omega) _ true (forkProc adversary sch₂ snapshot)
      (forkCont_pruneCompat' adversary E sch₂ hsignLaw₂ hpubLaw hprepLaw₂ hsignP₂ hpubP₂ hprepP₂ hsignG₂ hpubG₂ hprepG₂ hsignK₂
        hpubK₂ hprepK₂ hEleftW hErightW hE snapshot a)
      (forkProc_inv sch₂ adversary B B' Inv hmono hres hquery hpres₂ hpub hprepInv hupdate hrestore snapshot m hm (by omega)
        (by omega) hB')

include hagree hmono hres hquery hpres hpres₂ hpub hprepInv hupdate hrestore hsignLaw hsignLaw₂ hpubLaw in
/-- The end-resampled event fork hybrid for compatible continuations:
within twice the remaining fuel times the per-call bound. -/
theorem forkEventE_le_meanP (hsign : SignRunWMeanP sch₁ sch₂ adversary Good ε B B' Inv) (hB' : 2 * B + 1 ≤ B')
    (hprepLaw₂ : ∀ pk m sig, PostLaw resample (sch₂.prepareVerification pk m sig))
    (hsignP₂ : ∀ K sk m, PruneLaw K (sch₂.sign sk m)) (hpubP₂ : ∀ K q, PruneLaw K (sch₂.publicOracle q))
    (hprepP₂ : ∀ K pk m sig, PruneLaw K (sch₂.prepareVerification pk m sig))
    (hsignG₂ : ∀ sk m, Grows (sch₂.sign sk m)) (hpubG₂ : ∀ q, Grows (sch₂.publicOracle q))
    (hprepG₂ : ∀ pk m sig, Grows (sch₂.prepareVerification pk m sig))
    (hsignK₂ : ∀ sk m, Keeps (sch₂.sign sk m)) (hpubK₂ : ∀ q, Keeps (sch₂.publicOracle q))
    (hprepK₂ : ∀ pk m sig, Keeps (sch₂.prepareVerification pk m sig))
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
    -- step A: the second branch, for every output of the first
    have hA : ∀ y ∈ (resampleW resample { snapshot.world with hashTable := T }).support,
        ∀ r ∈ (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr).support,
        inner sch₁ r ≤ inner sch₂ r + snapshot.remaining * ε :=
      stepA sch₁ sch₂ adversary hagree Good ε B B' Inv hmono hres hquery hpres hpub hprepInv hupdate hrestore hsignLaw hpubLaw E
        hsign hB' hEleft hErightW hE snapshot hsk m hm hB a
    -- step B: the first branch, with the second scheme's second branch
    have hB' : mean (resampleW resample { snapshot.world with hashTable := T }) (fun y =>
        mean (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
          (inner sch₂)) ≤
        mean (resampleW resample { snapshot.world with hashTable := T }) (fun y =>
          mean (runW sch₂ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next a) y tr)
            (inner sch₂)) + snapshot.remaining * ε :=
      stepB sch₁ sch₂ adversary hagree Good ε B B' Inv hmono hres hquery hpres hpres₂ hpub hprepInv hupdate hrestore hsignLaw
        hsignLaw₂ hpubLaw E hsign hB' hprepLaw₂ hsignP₂ hpubP₂ hprepP₂ hsignG₂ hpubG₂ hprepG₂ hsignK₂ hpubK₂ hprepK₂ hEleftW
        hErightW hE snapshot hsk m hm hB a
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
end SDitH.Proofs.MeanHybridCompat
