import SDitH.Proofs.EventRequirements

/-! The pruned equality of the two signings restated as a closeness. The
exact equality cannot hold for every world satisfying the counted
invariant: the pre-call cipher history may already record an entry at a
key of the hidden path, and the signature's data is then correlated with
a value a functional of the signature and the pruned world can know, so
the honest and the fake signings differ by the probability of such a hit.
For the same reason the closeness is stated over the uniform salt, root
and digest rather than at fixed ones (a fixed root whose key is recorded
is hit with certainty). The corrected named target `PrunedClose` allows
an explicit slack for bounded functionals; the swap's core, the two
per-call bounds, the per-event gap and the composed forgery bound are
restated under it, the slack entering the per-call constant beside the two
touching terms. -/

namespace SDitH.Proofs.SwapClose

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier Spec.CandidateSimulator Spec.BLC
open Spec.SharedSigner (commitBudget)
open CommitSplitRun (prefixBudget)
open Spec.BAVC (Digest)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open CandidateReduction ForgeryReduction ExtractionSplit SimulatedSolver CandidateSimulator SimulationGap
open SimulatedWith SignCompare DigestFirstVsSimulated SignComparePost SimulationGapTrace InputPresentBound TraceLength
open PrefixMentionBound (mentionStep)
open RunHybrid EventHybrid CipherResample GameResample ChargeRun ChargeExpect ChargeCut ChargeCutExpect SharedResample
open CandidateResample SimulationGapMean CipherInvariant PayloadConsistent RowBoundExplicit RowStoredPosterior
open HeadCommitSplit SimulationGapCipher
open GamePrune RunWorld ForkRestore ForkRestoreLemmas ForkRestoreEnd EventRestore MeanHybridCont MeanHybridContW
open MeanEventCont CandidatePrune CandidatePrepLaw CandidateShift CandidateKeepsFamily InvCExtra HistoryShiftGame
open ForgeryEvents MeanHybrid SimulationGapMean2 SwapDischarge MeanHybridCompat MeanCutCompat EventCutCompat ForkPruneCompat
open GamePruneGen GamePrune RunWorld CutWorld SignBridge PruneLawRun HiddenEntries HiddenTuple
open Spec.IdealCipher (Entry)
open Spec.RandomOracleTrap (indicator)
open scoped Classical ENNReal
open TouchBound SimulationGapCompat ForgeryFinal PruneCompatClosure EventRequirements

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The pruned closeness of the two signings: for every functional bounded
by one, over the uniform salt, root and digest, the pruned mean with the
honest witness is within the slack of the pruned mean with a fake
witness. -/
def PrunedClose (B : Nat) (ε : ℝ≥0∞) : Prop :=
  ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))), InvC (tau := tau) (kappa := kappa) B world →
    ∀ Ψ, (∀ x, Ψ x ≤ 1) →
    (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMean S publicKey (sigHidden S) witness message salt root digest world Ψ) ≤
    (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMean S publicKey (sigHidden S) fake message salt root digest world Ψ) + ε

/-- The pruned equality is the closeness with no slack. -/
theorem prunedClose_of_equal (B : Nat) (h : PrunedEqual S publicKey B) : PrunedClose S publicKey B 0 :=
  fun witness fake message world hw Ψ _ => by
    have hfun : ∀ (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda),
        prunedMean S publicKey (sigHidden S) witness message salt root digest world Ψ =
          prunedMean S publicKey (sigHidden S) fake message salt root digest world Ψ :=
      fun salt root digest => h witness fake message salt root digest world hw Ψ
    simp only [hfun, add_zero, le_refl]

variable (hidden : Signature (Digest lambda)
    (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) →
  Fin tau → Fin (2 ^ kappa))

/-- The swap's core: with the forward and reverse agreements for the
continuation at any keys and the pruned equality of the two signings, the
call with the honest witness followed by the continuation is within the two
touching terms of the call with a fake witness. -/
theorem swap_core_close (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1))) (hcons : GamePrune.Consistent world)
    (Ψ : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1)) → ℝ≥0∞)
    (TΨ : List (Bits lambda) → Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1)) → ℝ≥0∞)
    (hfwd : ∀ (K : List (Bits lambda)) sig (X : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1))), GamePrune.Consistent X →
      mean (resampleW resample X) (fun w'' => Ψ (sig, w'')) ≤
        mean (resampleW resample (pruneW K X)) (fun w'' => Ψ (sig, w'') + TΨ K (sig, w'')))
    (hrev : ∀ (K : List (Bits lambda)) sig (X : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1))), GamePrune.Consistent X →
      mean (resampleW resample (pruneW K X)) (fun w'' => Ψ (sig, w'')) ≤
        mean (resampleW resample X) (fun w'' => Ψ (sig, w'')) +
          mean (resampleW resample (pruneW K X)) (fun w'' => TΨ K (sig, w'')))
    (ε : ℝ≥0∞) (hclose :
      (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
        mean (PMF.uniformOfFintype (Digest lambda)) fun digest =>
          prunedMean S publicKey hidden witness message salt root digest world Ψ) ≤
      (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
        mean (PMF.uniformOfFintype (Digest lambda)) fun digest =>
          prunedMean S publicKey hidden fake message salt root digest world Ψ) + ε) :
    mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey witness message w') Ψ) ≤
      mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey fake message w') Ψ) +
        (touchMean S publicKey hidden witness message world TΨ + (touchMean S publicKey hidden fake message world TΨ + ε)) := by
  have hsw : ∀ wsign, mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey wsign message w') Ψ) =
      mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
        mean (PMF.uniformOfFintype (Digest lambda)) fun digest => mean (resampleW resample world) fun w' =>
          mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w') Ψ := by
    intro wsign
    simp only [simulatedSignWith_eq, mean_bind]
    simp only [mean_comm (resampleW resample world)]
  have hcw : ∀ (salt root : Bits lambda) (digest : Digest lambda) wsign w', w' ∈ (resampleW resample world).support → ∀ r,
      r ∈ (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w').support →
      GamePrune.Consistent r.2 :=
    fun salt root digest wsign w' hw' r hr => commitOracle_consistent S.signer salt wsign root _ w'
      (consistent_of_mem_resampleW _ _ hw' (possible_of_consistent _ hcons)) r hr
  have hfwd' : ∀ (salt root : Bits lambda) (digest : Digest lambda),
      mean (resampleW resample world) (fun w' =>
        mean (commitOracle S.signer salt witness root (simPost S publicKey message salt digest) w') Ψ) ≤
      prunedMean S publicKey hidden witness message salt root digest world Ψ +
        touchInner S publicKey hidden witness message salt root digest world TΨ := by
    intro salt root digest
    calc mean (resampleW resample world) (fun w' =>
            mean (commitOracle S.signer salt witness root (simPost S publicKey message salt digest) w') Ψ)
        = mean (resampleW resample world) (fun w' =>
            mean (commitOracle S.signer salt witness root (simPost S publicKey message salt digest) w') fun r =>
              mean (resampleW resample r.2) fun w'' => Ψ (r.1, w'')) :=
          postLaw_mean (commitOracle_postLaw S.signer salt witness root _) world Ψ
      _ ≤ mean (resampleW resample world) (fun w' =>
            mean (commitOracle S.signer salt witness root (simPost S publicKey message salt digest) w') fun r =>
              mean (resampleW resample (pruneW (outKeys S.signer salt root hidden r) r.2)) fun w'' =>
                Ψ (r.1, w'') + TΨ (outKeys S.signer salt root hidden r) (r.1, w'')) :=
          mean_le_mean _ _ _ fun w' hw' => mean_le_mean _ _ _ fun r hr => hfwd _ r.1 r.2 (hcw salt root digest witness w' hw' r hr)
      _ = _ := by simp only [prunedMean, touchInner, mean_add]
  have hrev' : ∀ (salt root : Bits lambda) (digest : Digest lambda),
      prunedMean S publicKey hidden fake message salt root digest world Ψ ≤
      mean (resampleW resample world) (fun w' =>
        mean (commitOracle S.signer salt fake root (simPost S publicKey message salt digest) w') Ψ) +
        touchInner S publicKey hidden fake message salt root digest world TΨ := by
    intro salt root digest
    calc prunedMean S publicKey hidden fake message salt root digest world Ψ
        ≤ mean (resampleW resample world) (fun w' =>
            mean (commitOracle S.signer salt fake root (simPost S publicKey message salt digest) w') fun r =>
              mean (resampleW resample r.2) fun w'' => Ψ (r.1, w'')) +
            touchInner S publicKey hidden fake message salt root digest world TΨ := by
          unfold prunedMean touchInner
          simp only [← mean_add]
          exact mean_le_mean _ _ _ fun w' hw' => mean_le_mean _ _ _ fun r hr => hrev _ r.1 r.2 (hcw salt root digest fake w' hw' r hr)
      _ = _ := by rw [← postLaw_mean (commitOracle_postLaw S.signer salt fake root _) world Ψ]
  rw [hsw witness, hsw fake]
  unfold touchMean
  calc _ ≤ mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
        mean (PMF.uniformOfFintype (Digest lambda)) fun digest =>
          prunedMean S publicKey hidden witness message salt root digest world Ψ +
            touchInner S publicKey hidden witness message salt root digest world TΨ :=
        mean_le_mean _ _ _ fun salt _ => mean_le_mean _ _ _ fun root _ => mean_le_mean _ _ _ fun digest _ => hfwd' salt root digest
    _ = (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
          mean (PMF.uniformOfFintype (Digest lambda)) fun digest =>
            prunedMean S publicKey hidden witness message salt root digest world Ψ) +
        (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
          mean (PMF.uniformOfFintype (Digest lambda)) fun digest =>
            touchInner S publicKey hidden witness message salt root digest world TΨ) := by simp only [mean_add]
    _ ≤ ((mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
          mean (PMF.uniformOfFintype (Digest lambda)) fun digest =>
            prunedMean S publicKey hidden fake message salt root digest world Ψ) + ε) +
        (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
          mean (PMF.uniformOfFintype (Digest lambda)) fun digest =>
            touchInner S publicKey hidden witness message salt root digest world TΨ) := add_le_add hclose le_rfl
    _ ≤ ((mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
          mean (PMF.uniformOfFintype (Digest lambda)) fun digest =>
            mean (resampleW resample world) (fun w' =>
              mean (commitOracle S.signer salt fake root (simPost S publicKey message salt digest) w') Ψ) +
              touchInner S publicKey hidden fake message salt root digest world TΨ) + ε) +
        (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
          mean (PMF.uniformOfFintype (Digest lambda)) fun digest =>
            touchInner S publicKey hidden witness message salt root digest world TΨ) :=
        add_le_add (add_le_add (mean_le_mean _ _ _ fun salt _ => mean_le_mean _ _ _ fun root _ =>
          mean_le_mean _ _ _ fun digest _ => hrev' salt root digest) le_rfl) le_rfl
    _ = _ := by
        simp only [mean_add]
        ring

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The per-call bound for compatible continuations of the run, from the
input-present and retry bounds, the pruned closeness of the two signings
and the touching bound. -/
theorem signRunW_meanP_close (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S) (εRow εR εT : ℝ≥0∞) (B B' : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) B world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) B world → (retryEvent S publicKey witness message world) true ≤ εR)
    (εPre : ℝ≥0∞) (hclose : PrunedClose S publicKey B εPre)
    (htouch : ∀ (wsign witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (m : Nat)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) m world →
      ∀ (fuel' : Nat), m + fuel' + 1 ≤ B → ∀ (pk : List Bool) (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (Cp : Terminal (List Bool) (Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF (Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))),
        (∀ r, InvC (tau := tau) (kappa := kappa) B r.2 → ∀ w ∈ (Cp r).support, InvC (tau := tau) (kappa := kappa) B' w) →
        touchMean S publicKey (sigHidden S) wsign message world (fun K r =>
          mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1)
            r.2 trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) ≤ εT) :
    SignRunWMeanP (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (GoodKey S publicKey)
      (εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR (2 * εT + εPre) B) B B' (InvC (tau := tau) (kappa := kappa)) := by
  intro sk hsk message m world hm fuel' pk next trace hfuel h c Cp hc hCp
  have hw : InvC (tau := tau) (kappa := kappa) B world := invC_mono m B world (by omega) hm
  obtain ⟨hpk, hsol⟩ := hsk
  rcases sk with ⟨pk', witness⟩
  dsimp only at hpk hsol
  rw [hpk]
  refine call_mean S V verifyBudget publicKey sampleWitness hl htau hpc εRow εR (2 * εT + εPre) B hrow hretry witness hsol message world hw
    (fun r => (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1)
      r.2 trace).bind h) c fun fake => ?_
  have hfwd : ∀ (K : List (Bits lambda)) sig (X : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))), GamePrune.Consistent X →
      mean (resampleW resample X) (fun w'' =>
        ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next sig) w''
          trace).bind h) c) ≤
      mean (resampleW resample (pruneW K X)) (fun w'' =>
        ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next sig) w''
          trace).bind h) c +
        mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next sig) w''
          trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) := by
    intro K sig X hX
    have := runW_le_prune_gen K (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary
        (simulated_postLaw S V verifyBudget publicKey sampleWitness)
        (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
        (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
        (simulated_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (publicOracle_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (prepareVerification_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (simulated_grows S V verifyBudget publicKey sampleWitness)
        (publicOracle_grows S V verifyBudget publicKey sampleWitness)
        (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
        (simulated_keeps S V verifyBudget publicKey sampleWitness)
        (publicOracle_keeps S V verifyBudget publicKey sampleWitness)
        (prepareVerification_keeps S V verifyBudget publicKey sampleWitness)
        (fun t => (h t) c) (fun t => mean (Cp t) fun y => indicator (touchesG K y)) (hc K) fuel' pk (publicKey, witness) (next sig)
        X trace hX
    simpa only [mean_bind_apply, mean_add] using this
  have hrev : ∀ (K : List (Bits lambda)) sig (X : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))), GamePrune.Consistent X →
      mean (resampleW resample (pruneW K X)) (fun w'' =>
        ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next sig) w''
          trace).bind h) c) ≤
      mean (resampleW resample X) (fun w'' =>
        ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next sig) w''
          trace).bind h) c) +
      mean (resampleW resample (pruneW K X)) (fun w'' =>
        mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next sig) w''
          trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) := by
    intro K sig X hX
    have := prune_le_runW_gen K (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary
        (simulated_postLaw S V verifyBudget publicKey sampleWitness)
        (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
        (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
        (simulated_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (publicOracle_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (prepareVerification_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (simulated_grows S V verifyBudget publicKey sampleWitness)
        (publicOracle_grows S V verifyBudget publicKey sampleWitness)
        (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
        (simulated_keeps S V verifyBudget publicKey sampleWitness)
        (publicOracle_keeps S V verifyBudget publicKey sampleWitness)
        (prepareVerification_keeps S V verifyBudget publicKey sampleWitness)
        (fun t => (h t) c) (fun t => mean (Cp t) fun y => indicator (touchesG K y)) (hc K) fuel' pk (publicKey, witness) (next sig)
        X trace hX
    simpa only [mean_bind_apply] using this
  have hcore := swap_core_close S publicKey (sigHidden S) witness fake message world hw.2.1
    (fun r => ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1)
      r.2 trace).bind h) c)
    (fun K r => mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness)
      (next r.1) r.2 trace) fun t => mean (Cp t) fun y => indicator (touchesG K y))
    hfwd hrev εPre (hclose witness fake message world hw _ fun _ => PMF.coe_le_one _ _)
  have ht₁ := htouch witness witness message m world hm fuel' hfuel pk next trace Cp hCp
  have ht₂ := htouch fake witness message m world hm fuel' hfuel pk next trace Cp hCp
  calc _ = mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey witness message w') fun r =>
          ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) := by simp only [mean_bind_apply]
    _ ≤ _ := hcore
    _ ≤ mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey fake message w') fun r =>
          ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) + (εT + (εT + εPre)) := add_le_add le_rfl (add_le_add ht₁ (add_le_add ht₂ le_rfl))
    _ = _ := by
        simp only [mean_bind_apply]
        ring

/-- The per-call bound for compatible continuations of the cut with its
world, from the input-present and retry bounds, the pruned closeness of the
two signings and the touching bound. -/
theorem signCutW_meanP_close (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S) (εRow εR εT : ℝ≥0∞) (B B' : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) B world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) B world → (retryEvent S publicKey witness message world) true ≤ εR)
    (εPre : ℝ≥0∞) (hclose : PrunedClose S publicKey B εPre)
    (htouch : ∀ (wsign witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (m : Nat)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) m world →
      ∀ (index fuel' : Nat), m + fuel' + 1 ≤ B → ∀ (pk : List Bool) (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (Cp : Cut (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool) (Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) →
          PMF (Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))),
        (∀ r, InvC (tau := tau) (kappa := kappa) B r.2 → ReachC B r.1 → ∀ w ∈ (Cp r).support,
          InvC (tau := tau) (kappa := kappa) B' w) →
        touchMean S publicKey (sigHidden S) wsign message world (fun K r =>
          mean (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
            (next r.1) r.2 trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) ≤ εT) :
    SignCutWMeanP (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (GoodKey S publicKey)
      (εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR (2 * εT + εPre) B) B B' (InvC (tau := tau) (kappa := kappa)) := by
  intro sk hsk message m world hm index fuel' hfuel pk next trace h c Cp hc hCp
  have hw : InvC (tau := tau) (kappa := kappa) B world := invC_mono m B world (by omega) hm
  obtain ⟨hpk, hsol⟩ := hsk
  rcases sk with ⟨pk', witness⟩
  dsimp only at hpk hsol
  rw [hpk]
  refine call_mean S V verifyBudget publicKey sampleWitness hl htau hpc εRow εR (2 * εT + εPre) B hrow hretry witness hsol message world hw
    (fun r => (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
      (next r.1) r.2 trace).bind h) c fun fake => ?_
  have hfwd : ∀ (K : List (Bits lambda)) sig (X : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))), GamePrune.Consistent X →
      mean (resampleW resample X) (fun w'' =>
        ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next sig)
          w'' trace).bind h) c) ≤
      mean (resampleW resample (pruneW K X)) (fun w'' =>
        ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next sig)
          w'' trace).bind h) c +
        mean (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
          (next sig) w'' trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) := by
    intro K sig X hX
    have := cutW_le_prune_gen K (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary
        (simulated_postLaw S V verifyBudget publicKey sampleWitness)
        (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
        (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
        (simulated_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (publicOracle_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (prepareVerification_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (simulated_grows S V verifyBudget publicKey sampleWitness)
        (publicOracle_grows S V verifyBudget publicKey sampleWitness)
        (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
        (simulated_keeps S V verifyBudget publicKey sampleWitness)
        (publicOracle_keeps S V verifyBudget publicKey sampleWitness)
        (prepareVerification_keeps S V verifyBudget publicKey sampleWitness)
        (fun t => (h t) c) (fun t => mean (Cp t) fun y => indicator (touchesG K y)) (hc K) index fuel' pk (publicKey, witness)
        (next sig) X trace hX
    simpa only [mean_bind_apply, mean_add] using this
  have hrev : ∀ (K : List (Bits lambda)) sig (X : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))), GamePrune.Consistent X →
      mean (resampleW resample (pruneW K X)) (fun w'' =>
        ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next sig)
          w'' trace).bind h) c) ≤
      mean (resampleW resample X) (fun w'' =>
        ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next sig)
          w'' trace).bind h) c) +
      mean (resampleW resample (pruneW K X)) (fun w'' =>
        mean (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
          (next sig) w'' trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) := by
    intro K sig X hX
    have := prune_le_cutW_gen K (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary
        (simulated_postLaw S V verifyBudget publicKey sampleWitness)
        (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
        (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
        (simulated_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (publicOracle_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (prepareVerification_pruneLaw S V verifyBudget publicKey sampleWitness K)
        (simulated_grows S V verifyBudget publicKey sampleWitness)
        (publicOracle_grows S V verifyBudget publicKey sampleWitness)
        (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
        (simulated_keeps S V verifyBudget publicKey sampleWitness)
        (publicOracle_keeps S V verifyBudget publicKey sampleWitness)
        (prepareVerification_keeps S V verifyBudget publicKey sampleWitness)
        (fun t => (h t) c) (fun t => mean (Cp t) fun y => indicator (touchesG K y)) (hc K) index fuel' pk (publicKey, witness)
        (next sig) X trace hX
    simpa only [mean_bind_apply] using this
  have hcore := swap_core_close S publicKey (sigHidden S) witness fake message world hw.2.1
    (fun r => ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
      (next r.1) r.2 trace).bind h) c)
    (fun K r => mean (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
      (next r.1) r.2 trace) fun t => mean (Cp t) fun y => indicator (touchesG K y))
    hfwd hrev εPre (hclose witness fake message world hw _ fun _ => PMF.coe_le_one _ _)
  have ht₁ := htouch witness witness message m world hm index fuel' hfuel pk next trace Cp hCp
  have ht₂ := htouch fake witness message m world hm index fuel' hfuel pk next trace Cp hCp
  calc _ = mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey witness message w') fun r =>
          ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
            (next r.1) r.2 trace).bind h) c) := by simp only [mean_bind_apply]
    _ ≤ _ := hcore
    _ ≤ mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey fake message w') fun r =>
          ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
            (next r.1) r.2 trace).bind h) c) + (εT + (εT + εPre)) := add_le_add le_rfl (add_le_add ht₁ (add_le_add ht₂ le_rfl))
    _ = _ := by
        simp only [mean_bind_apply]
        ring


/-- The simulation gap for one event with the per-call swaps discharged, at
the budget three times the fuel plus two. -/
theorem hgap_meanP_close (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S)
    (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) (hvc : verifyBudget ≤ commitBudget tau kappa)
    (εRow εR εT : ℝ≥0∞) (fuel : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (εPre : ℝ≥0∞) (hclose : PrunedClose S publicKey (3 * (fuel + 1) + 2) εPre)
    (htouchR : TouchR S V verifyBudget publicKey sampleWitness adversary εT (3 * (fuel + 1) + 2) (2 * (3 * (fuel + 1) + 2) + 1))
    (htouchC : TouchC S V verifyBudget publicKey sampleWitness adversary εT (3 * (fuel + 1) + 2) (4 * (3 * (fuel + 1) + 2) + 3))
    (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hE : EventOKP E) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true +
        3 * ((fuel : ℝ≥0∞) + 1) *
          εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR (2 * εT + εPre) (3 * (fuel + 1) + 2) := by
  have hsignRunW := signRunW_meanP_close S V verifyBudget publicKey sampleWitness adversary hl htau hpc εRow εR εT (3 * (fuel + 1) + 2)
    (2 * (3 * (fuel + 1) + 2) + 1) hrow hretry εPre hclose htouchR
  have hsignCut := signCutW_meanP_close S V verifyBudget publicKey sampleWitness adversary hl htau hpc εRow εR εT (3 * (fuel + 1) + 2)
    (4 * (3 * (fuel + 1) + 2) + 3) hrow hretry εPre hclose htouchC
  unfold randomEventExperiment simEventExperiment
  refine bind_le_bind_add_const' _ _ _ _ true (fun index _ => ?_)
  have heq₁ : eventExperiment S V verifyBudget publicKey sampleWitness adversary E index.val (fuel + 1) =
      eventExp (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary E index.val
        (fuel + 1) := by
    unfold eventExperiment eventExp
    first
      | rfl
      | (congr 1; funext c; cases c <;> rfl)
  rw [heq₁, eventExp_eq_E _ adversary E (keygen_resampled S V verifyBudget publicKey sampleWitness)
    (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
    (honest_keepsFamily S V verifyBudget publicKey sampleWitness) (publicOracle_keepsFamily S V verifyBudget publicKey sampleWitness)
    (prepareVerification_keepsFamily S V verifyBudget publicKey sampleWitness)
    (honest_grows S V verifyBudget publicKey sampleWitness) (publicOracle_grows S V verifyBudget publicKey sampleWitness)
    (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
    (honest_shiftLaw S V verifyBudget publicKey sampleWitness) (publicOracle_shiftLaw S V verifyBudget publicKey sampleWitness)
    (prepareVerification_shiftLaw S V verifyBudget publicKey sampleWitness) (eventOK_shift E hE) (eventOK_left E hE) (eventOK_right E hE)]
  refine (eventExpE_le_meanP adversary E (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) (agree S V verifyBudget publicKey sampleWitness)
    (GoodKey S publicKey) _ (3 * (fuel + 1) + 2) (2 * (3 * (fuel + 1) + 2) + 1) (4 * (3 * (fuel + 1) + 2) + 3)
    (InvC (tau := tau) (kappa := kappa)) invC_mono invC_resample invC_query
    (invC_honest S V verifyBudget publicKey sampleWitness) (invC_simulated S V verifyBudget publicKey sampleWitness)
    (invC_pub S V verifyBudget publicKey sampleWitness) (invC_prep S V verifyBudget publicKey sampleWitness hvc) invC_update
    invC_restore (honest_postLaw S V verifyBudget publicKey sampleWitness) (simulated_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness) (keygen_resampled S V verifyBudget publicKey sampleWitness)
    (keygen_good S V verifyBudget publicKey sampleWitness hsample) (invC_keygen S V verifyBudget publicKey sampleWitness)
    hsignCut (by omega) hsignRunW (by omega) (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
    (fun K => honest_pruneLaw S V verifyBudget publicKey sampleWitness K) (honest_grows S V verifyBudget publicKey sampleWitness)
    (honest_keeps S V verifyBudget publicKey sampleWitness)
    (fun K => simulated_pruneLaw S V verifyBudget publicKey sampleWitness K) (simulated_grows S V verifyBudget publicKey sampleWitness)
    (simulated_keeps S V verifyBudget publicKey sampleWitness)
    (fun K => publicOracle_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (fun K => prepareVerification_pruneLaw S V verifyBudget publicKey sampleWitness K)
    (publicOracle_grows S V verifyBudget publicKey sampleWitness) (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
    (publicOracle_keeps S V verifyBudget publicKey sampleWitness) (prepareVerification_keeps S V verifyBudget publicKey sampleWitness)
    hE.none hE.hist (eventOK_left E hE) hE.leftW hE.rightW hE.compat index.val (fuel + 1) (by omega)).trans ?_
  rw [← eventExp_eq_E _ adversary E (simulated_keygen_resampled S V verifyBudget publicKey sampleWitness)
    (simulated_postLaw S V verifyBudget publicKey sampleWitness)
    (fun q => publicOracle_postLaw S V verifyBudget publicKey sampleWitness q)
    (fun pk m sig => prepareVerification_postLaw S V verifyBudget publicKey sampleWitness pk m sig)
    (simulated_keepsFamily S V verifyBudget publicKey sampleWitness)
    (fun q => publicOracle_keepsFamily S V verifyBudget publicKey sampleWitness q)
    (fun pk m sig => prepareVerification_keepsFamily S V verifyBudget publicKey sampleWitness pk m sig)
    (simulated_grows S V verifyBudget publicKey sampleWitness)
    (fun q => publicOracle_grows S V verifyBudget publicKey sampleWitness q)
    (fun pk m sig => prepareVerification_grows S V verifyBudget publicKey sampleWitness pk m sig)
    (simulated_shiftLaw S V verifyBudget publicKey sampleWitness)
    (fun q => publicOracle_shiftLaw S V verifyBudget publicKey sampleWitness q)
    (fun pk m sig => prepareVerification_shiftLaw S V verifyBudget publicKey sampleWitness pk m sig) (eventOK_shift E hE) (eventOK_left E hE)
    (eventOK_right E hE)]
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · first
      | rfl
      | (unfold eventExp; congr 1; congr 1; funext c; cases c <;> rfl)
  · push_cast
    ring

/-- The composed simulation term under the pruned closeness: as `εSimP`,
with the closeness slack added to the two touching terms. -/
def εSimP' (c cKey cOut q : Nat) (εR εT εPre : ℝ≥0∞) (fuel : Nat) : ℝ≥0∞ :=
  3 * ((fuel : ℝ≥0∞) + 1) * εCall (lambda := lambda) (tau := tau) (kappa := kappa)
    (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (3 * (fuel + 1) + 2)) q
      (commitBudget tau kappa * (3 * (fuel + 1) + 2))) εR (2 * εT + εPre) (3 * (fuel + 1) + 2)

/-- The simulation gap for one event, with the touching bounds instantiated,
under the final hypotheses. -/
theorem hgap_final_close (hlambda : 0 < lambda) (htau : 0 < tau) (fuel : Nat)
    (hSencode : S.encode = fun hidden => psi S.signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hhigher : 1 ≤ higherCount) (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR : ℝ≥0∞)
    (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ b, Fintype.card {r : Bits lambda // S.signer.layout.output r = b} ≤ cOut)
    (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (εPre : ℝ≥0∞) (hclose : PrunedClose S publicKey (3 * (fuel + 1) + 2) εPre)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (εLeaf : ℝ≥0∞)
    (hleafR : LeafR S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (hleafC : LeafC S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (εColl : ℝ≥0∞)
    (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hE : EventOKP E) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true +
        (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
          (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
            (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl) := by
  have h := hgap_meanP_close S V verifyBudget publicKey sampleWitness adversary hlambda (Nat.pos_iff_ne_zero.mp htau)
    (payload_consistent S hSencode hhigher) hsample hvc _ εR _ fuel
    (fun world hw => rowTerm_mean_le_explicit S (Nat.pos_iff_ne_zero.mp htau) world _ hw.1 (invC_game _ world hw).1
      hin hl hL c hfiber cKey hkey cOut hout _ (invC_game _ world hw).2 q hq)
    hretry εPre hclose
    (touchR_mono S V verifyBudget publicKey sampleWitness adversary _ _ _ _
      (touchR_of S V verifyBudget publicKey sampleWitness adversary hL2 hin hl hL c hfiber cKey hkey hvc _ _ hNb hNR εLeaf hleafR)
      (εTouch_mono c cKey _ _ _ εLeaf (by omega)))
    (touchC_of S V verifyBudget publicKey sampleWitness adversary hL2 hin hl hL c hfiber cKey hkey hvc _ _ hNb hNR εLeaf hleafC)
    E hE
  refine h.trans (add_le_add le_rfl ?_)
  unfold εSimP'
  exact le_self_add

/-- The composed forgery bound under the pruned closeness of the two
signings in place of their pruned equality: the closeness slack enters the
per-call constant beside the two touching terms. -/
theorem forgery_le_final_close (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat)
    (hSencode : S.encode = fun hidden => psi S.signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hhigher : 1 ≤ higherCount) (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR : ℝ≥0∞)
    (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ b, Fintype.card {r : Bits lambda // S.signer.layout.output r = b} ≤ cOut)
    (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (εPre : ℝ≥0∞) (hclose : PrunedClose S publicKey (3 * (fuel + 1) + 2) εPre)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (εLeaf : ℝ≥0∞)
    (hleafR : LeafR S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (hleafC : LeafC S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (εColl : ℝ≥0∞)
    (hcoll : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true ≤ εColl) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => notSeparated V)
            fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (seedCollision V) fuel)
            true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => slopeWin S V)
            fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (fun _ => zeroChallenge V encode) fuel) true +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (schwartzZippel S V encode) fuel) true +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl)) +
         (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (batchingBad S V) fuel)
            true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl)) +
          (solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl))) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_simulated_events S V verifyBudget publicKey sampleWitness adversary
    (simulatedScheme S V verifyBudget publicKey sampleWitness) hlambda htau encode hmid hencoding hlinesEnc hencode bound hcommit
    hverify hone fuel
    (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
      (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
        (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) εPre fuel + εColl)
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ eventOKP_maskAfter)
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_notSeparated V))
    (hcoll.trans (le_add_self.trans le_add_self))
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_slopeWin S V))
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_zeroChallenge V encode))
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_schwartzZippel S V encode))
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_batchingBad S V))
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_rsdSolved S V))

end
end SDitH.Proofs.SwapClose
