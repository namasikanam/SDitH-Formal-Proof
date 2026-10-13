import SDitH.Proofs.MeanHybridCompat
import SDitH.Proofs.CutWorld

/-! The cut hybrid in mean form for compatible continuations, over the cut
with its final world. The per-call bound is taken for continuations of the
cut with its world that are compatible with pruning at every key list, with
the touching functional of a process on the result keeping the invariant
within an end budget. -/

namespace SDitH.Proofs.MeanCutCompat

open Spec.SignatureSecurity Spec.SignatureReplay
open Spec.IdealCipher (Family)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open RunHybrid GameResample ChargeExpect ChargeCutExpect RowStoredPosterior MeanHybrid MeanHybridCont MeanHybridContW RunWorld
open CipherResample SharedPrune HiddenEntries GamePrune GamePruneReverse GamePruneGen PruneCompatClosure ForkPruneCompat
open ForkRestore ForkRestoreLemmas ForkRestoreEnd ForkRestoreEq MeanForkCont MeanForkCont2 HiddenSlice MeanHybridCompat
open CutWorld
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
  (hpub : ∀ (query : Query) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
    (r : Answer × GW HashInput Digest lambda s wit rnd),
    Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
  (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw resample (sch₁.sign sk message))
  (hpubLaw : ∀ query : Query, PostLaw resample (sch₂.publicOracle query))

/-- A cut reachable within a budget: a saved snapshot's remaining fuel is
at most the budget. -/
def ReachC (B : Nat)
    (c : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State) :
    Prop :=
  ∀ sn, c = .saved sn → sn.remaining ≤ B

/-- The per-call bound in mean form for compatible continuations of the cut
with its final world, for cuts within the budget: the touching functional
is that of a process keeping the invariant within the end budget on
reachable cuts. -/
def SignCutWMeanP : Prop :=
  ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (m : Nat) (world : GW HashInput Digest lambda s wit rnd), Inv m world →
    ∀ (index fuel : Nat), m + fuel + 1 ≤ B → ∀ (pk : PublicKey) (next : Signature → State) (trace : Trace Message HashInput Query)
      (h : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
        GW HashInput Digest lambda s wit rnd → PMF Bool) (c : Bool)
      (Cp : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
        GW HashInput Digest lambda s wit rnd → PMF (GW HashInput Digest lambda s wit rnd)),
      (∀ K, PruneCompatC K (fun t => (h t) c) (fun r => mean (Cp r) fun w => indicator (touchesG K w))) →
      (∀ r, Inv B r.2 → ReachC B r.1 → ∀ w ∈ (Cp r).support, Inv B' w) →
    mean (resampleW resample world) (fun w => ((sch₁.sign sk message w).bind fun r =>
        (cutW sch₂ adversary index fuel pk sk (next r.1) r.2 trace).bind h) c) ≤
      mean (resampleW resample world) (fun w => ((sch₂.sign sk message w).bind fun r =>
        (cutW sch₂ adversary index fuel pk sk (next r.1) r.2 trace).bind h) c) + ε

include hagree hres hquery hpres hpub hsignLaw hpubLaw in
/-- The cut hybrid in mean form, with its final world, for a compatible
continuation. -/
theorem cutW_le_cutW_mean_contP (hsign : SignCutWMeanP sch₁ sch₂ adversary Good ε B B' Inv)
    (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State)
    (world : GW HashInput Digest lambda s wit rnd) (trace : Trace Message HashInput Query) (m : Nat) (hm : Inv m world)
    (hB : m + fuel ≤ B)
    (h : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
      GW HashInput Digest lambda s wit rnd → PMF Bool) (c : Bool)
    (Cp : Cut PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State ×
      GW HashInput Digest lambda s wit rnd → PMF (GW HashInput Digest lambda s wit rnd))
    (hc : ∀ K, PruneCompatC K (fun t => (h t) c) (fun r => mean (Cp r) fun w => indicator (touchesG K w)))
    (hCp : ∀ r, Inv B r.2 → ReachC B r.1 → ∀ w ∈ (Cp r).support, Inv B' w) :
    mean (resampleW resample world) (fun w => ((cutW sch₁ adversary index fuel pk sk state w trace).bind h) c) ≤
      mean (resampleW resample world) (fun w => ((cutW sch₂ adversary index fuel pk sk state w trace).bind h) c) + fuel * ε := by
  induction fuel generalizing index state world trace m with
  | zero =>
    simp only [cutW, Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  | succ fuel ih =>
    have hstep : (fuel : ℝ≥0∞) * ε ≤ ((fuel + 1 : Nat) : ℝ≥0∞) * ε :=
      mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ fuel)) le_rfl
    simp only [cutW, PMF.bind_bind, mean_bind_apply (adversary.step pk state)]
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
              (cutW sch₁ adversary index fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c)
          = mean (resampleW resample world) (fun w => mean (sch₁.sign sk message w) fun r =>
              mean (resampleW resample r.2) fun w' => ((cutW sch₁ adversary index fuel pk sk (next r.1) w'
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) := by
            simp only [mean_bind_apply]
            exact postLaw_mean (hsignLaw sk message) world _
        _ ≤ mean (resampleW resample world) (fun w => mean (sch₁.sign sk message w) fun r =>
              mean (resampleW resample r.2) (fun w' => ((cutW sch₂ adversary index fuel pk sk (next r.1) w'
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + fuel * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih index (next r.1) r.2 _ (m + 1) (hpres sk message w m r (hres m world hm w hw) hr) (by omega)
        _ = mean (resampleW resample world) (fun w => ((sch₁.sign sk message w).bind fun r =>
              (cutW sch₂ adversary index fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + fuel * ε := by
            simp only [mean_add_const, mean_bind_apply]
            congr 1
            exact (postLaw_mean (hsignLaw sk message) world (fun r => mean (cutW sch₂ adversary index fuel pk sk (next r.1) r.2
              { trace with signingRequests := message :: trace.signingRequests }) fun a => (h a) c)).symm
        _ ≤ (mean (resampleW resample world) (fun w => ((sch₂.sign sk message w).bind fun r =>
              (cutW sch₂ adversary index fuel pk sk (next r.1) r.2
                { trace with signingRequests := message :: trace.signingRequests }).bind h) c) + ε) + fuel * ε :=
            add_le_add (hsign sk hsk message m world hm index fuel (by omega) pk next _ h c Cp hc hCp) le_rfl
        _ = _ := by push_cast; ring
    | hash input next =>
      dsimp only
      cases index with
      | zero =>
        dsimp only
        exact le_self_add
      | succ index =>
        dsimp only
        simp only [PMF.bind_bind]
        have hform : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query Answer),
            mean (resampleW resample world) (fun w => ((Spec.RandomOracle.query w.hashTable input).bind fun r =>
              (cutW sch adversary index fuel pk sk (next r.1) { w with hashTable := r.2 }
                { trace with hashRequests := input :: trace.hashRequests }).bind h) c) =
            mean (Spec.RandomOracle.query world.hashTable input) fun r =>
              mean (resampleW resample { world with hashTable := r.2 }) fun w' =>
                ((cutW sch adversary index fuel pk sk (next r.1) w'
                  { trace with hashRequests := input :: trace.hashRequests }).bind h) c := by
          intro sch
          calc _ = mean (resampleW resample world) (fun w => ((Spec.RandomOracle.query world.hashTable input).bind fun r =>
                (cutW sch adversary index fuel pk sk (next r.1) { w with hashTable := r.2 }
                  { trace with hashRequests := input :: trace.hashRequests }).bind h) c) := by
                unfold mean
                refine tsum_congr fun w => ?_
                by_cases hw : w ∈ (resampleW resample world).support
                · simp only [hashTable_of_mem resample world w hw]
                · rw [PMF.mem_support_iff, not_not] at hw
                  simp [hw]
            _ = mean (Spec.RandomOracle.query world.hashTable input) fun r =>
                mean (resampleW resample world) fun w => ((cutW sch adversary index fuel pk sk (next r.1) { w with hashTable := r.2 }
                  { trace with hashRequests := input :: trace.hashRequests }).bind h) c := by
                simp only [mean_bind_apply]
                exact mean_comm _ _ _
            _ = _ := by
                refine congrArg _ (funext fun r => ?_)
                exact (mean_resampleW_update resample world r.2 (fun w' => ((cutW sch adversary index fuel pk sk (next r.1) w'
                  { trace with hashRequests := input :: trace.hashRequests }).bind h) c)).symm
        rw [hform sch₁, hform sch₂]
        refine (mean_le_mean _ _ _ fun r hr =>
          ih index (next r.1) _ _ (m + 1) (hquery world input m r hm hr) (by omega)).trans ?_
        rw [mean_add_const]
        exact add_le_add le_rfl hstep
    | query input next =>
      dsimp only
      simp only [PMF.bind_bind, hagree.publicOracle]
      calc mean (resampleW resample world) (fun w => ((sch₂.publicOracle input w).bind fun r =>
              (cutW sch₁ adversary index fuel pk sk (next r.1) r.2
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c)
          = mean (resampleW resample world) (fun w => mean (sch₂.publicOracle input w) fun r =>
              mean (resampleW resample r.2) fun w' => ((cutW sch₁ adversary index fuel pk sk (next r.1) w'
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) := by
            simp only [mean_bind_apply]
            exact postLaw_mean (hpubLaw input) world _
        _ ≤ mean (resampleW resample world) (fun w => mean (sch₂.publicOracle input w) fun r =>
              mean (resampleW resample r.2) (fun w' => ((cutW sch₂ adversary index fuel pk sk (next r.1) w'
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) + fuel * ε) :=
            mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun r hr =>
              ih index (next r.1) r.2 _ (m + 1) (hpub input w m r (hres m world hm w hw) hr) (by omega)
        _ = mean (resampleW resample world) (fun w => ((sch₂.publicOracle input w).bind fun r =>
              (cutW sch₂ adversary index fuel pk sk (next r.1) r.2
                { trace with publicRequests := input :: trace.publicRequests }).bind h) c) + fuel * ε := by
            simp only [mean_add_const, mean_bind_apply]
            congr 1
            exact (postLaw_mean (hpubLaw input) world (fun r => mean (cutW sch₂ adversary index fuel pk sk (next r.1) r.2
              { trace with publicRequests := input :: trace.publicRequests }) fun a => (h a) c)).symm
        _ ≤ _ := add_le_add le_rfl hstep

end
end SDitH.Proofs.MeanCutCompat
