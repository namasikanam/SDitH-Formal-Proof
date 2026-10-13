import SDitH.Proofs.SimulationGapMean2
import SDitH.Proofs.SignBridge
import SDitH.Proofs.EventCutCompat
import SDitH.Proofs.CandidateGamePruneReverse

/-! The discharge of the per-call witness swap. The fixed-witness simulated
signing is a uniform salt, root and digest followed by the signing-shaped
oracle with the simulated post-processing; from a resampled start, the call
followed by a continuation compatible with pruning is, by the generalised
agreement, within the touching functional's mean of the call followed by
the continuation from the resampled world pruned at the output's hidden
keys; the law of the signature with that pruned resampled world is the
named pruned-equality hypothesis between the honest and a fake witness;
and the reverse agreement returns to the fake call. -/

namespace SDitH.Proofs.SwapDischarge

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier Spec.CandidateSimulator Spec.BLC
open Spec.SharedSigner (commitBudget)
open Spec.BAVC (Digest)
open Spec.PIOPArithmetic (selectorCount)
open Spec.IdealCipher (Family Entry)
open Spec.RandomOracleTrap (indicator)
open ExtractionSplit (IsSolution)
open CandidateReduction ForgeryReduction ExtractionSplit SimulatedSolver CandidateSimulator SimulationGap
open SimulatedWith SignCompare SignComparePost DigestFirstVsSimulated InputPresentBound TraceLength
open RunHybrid EventHybrid CipherResample GameResample ChargeRun ChargeExpect ChargeCut ChargeCutExpect SharedResample
open CandidateResample CipherInvariant PayloadConsistent HiddenEntries HiddenTuple
open GamePrune RunWorld GamePruneGen CutWorld SignBridge PruneLawRun CandidatePrune CandidatePrepLaw
open MeanHybrid MeanHybridCompat MeanCutCompat SimulationGapMean2 HiddenSlice
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The verification preparation keeps consistency. -/
theorem prepareVerification_keeps (pk message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))) :
    Keeps ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification
      pk message signature) := by
  rcases signature with ⟨piop, _ | body⟩
  · rw [prepareVerification_none_eq]; exact keeps_pure _
  · rw [prepareVerification_some_eq]; exact keeps_run _ _ _

/-- The hidden tuple of a signature: from its digest and its body's counter,
or the first leaf without a body. -/
def sigHidden (sig : Signature (Digest lambda)
    (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))) :
    Fin tau → Fin (2 ^ kappa) :=
  match sig.body with
  | some (_, _, (ctr, _), _) => (S.expandEvaluation sig.piop ctr).hidden
  | none => fun _ => ⟨0, Nat.two_pow_pos kappa⟩

/-- The fixed-witness simulated signing is a uniform salt, root and digest
followed by the signing-shaped oracle with the simulated post-processing. -/
theorem simulatedSignWith_eq (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    simulatedSignWith S publicKey witness message world =
      (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
        (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
          (PMF.uniformOfFintype (Digest lambda)).bind fun digest =>
            commitOracle S.signer salt witness root (simPost S publicKey message salt digest) world := by
  unfold simulatedSignWith commitOracle
  simp only [simPost, PMF.map, Function.comp_def, PMF.pure_bind]
  congr 1
  funext salt
  congr 1
  funext root
  congr 1
  funext digest
  congr 1
  funext r
  rcases r with ⟨a, o⟩
  rcases a with committed | ⟨input, next⟩ | ⟨request, next⟩
  · dsimp only
    generalize Spec.BLCRetry.observe (attempt (stateOf S salt committed).2.key (S.expandEvaluation digest) S.encode)
      S.fuel 0 = obs
    rcases obs with ⟨c⟩ | ⟨ctr, opening⟩ | ⟨f⟩
    · rfl
    · dsimp only
      split <;> rename_i heq <;> simp only [heq]
    · rfl
  · rfl
  · rfl

variable (hidden : Signature (Digest lambda)
    (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) →
    Fin tau → Fin (2 ^ kappa))

/-- The call followed by a function of the signature and the resampled
world pruned at the output's hidden keys. -/
def prunedMean (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt root : Bits lambda)
    (digest : Digest lambda)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (G : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1)) → ℝ≥0∞) : ℝ≥0∞ :=
  mean (resampleW resample world) fun w' =>
    mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w') fun r =>
      mean (resampleW resample (pruneW (outKeys S.signer salt root hidden r) r.2)) fun w'' => G (r.1, w'')

/-- The call followed by the touching functional at the output's hidden keys
from the resampled pruned world. -/
def touchInner (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt root : Bits lambda)
    (digest : Digest lambda)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (TΨ : List (Bits lambda) → Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1)) → ℝ≥0∞) : ℝ≥0∞ :=
  mean (resampleW resample world) fun w' =>
    mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w') fun r =>
      mean (resampleW resample (pruneW (outKeys S.signer salt root hidden r) r.2)) fun w'' =>
        TΨ (outKeys S.signer salt root hidden r) (r.1, w'')

/-- The touching term of a signing call: over the uniform salt, root and
digest. -/
def touchMean (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (TΨ : List (Bits lambda) → Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1)) → ℝ≥0∞) : ℝ≥0∞ :=
  mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
    mean (PMF.uniformOfFintype (Digest lambda)) fun digest => touchInner S publicKey hidden wsign message salt root digest world TΨ

/-- The swap's core: with the forward and reverse agreements for the
continuation at any keys and the pruned equality of the two signings, the
call with the honest witness followed by the continuation is within the two
touching terms of the call with a fake witness. -/
theorem swap_core (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
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
    (hequal : ∀ (salt root : Bits lambda) (digest : Digest lambda),
      prunedMean S publicKey hidden witness message salt root digest world Ψ =
        prunedMean S publicKey hidden fake message salt root digest world Ψ) :
    mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey witness message w') Ψ) ≤
      mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey fake message w') Ψ) +
        (touchMean S publicKey hidden witness message world TΨ + touchMean S publicKey hidden fake message world TΨ) := by
  have hsw : ∀ wsign, mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey wsign message w') Ψ) =
      mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
        mean (PMF.uniformOfFintype (Digest lambda)) fun digest => mean (resampleW resample world) fun w' =>
          mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w') Ψ := by
    intro wsign
    simp only [simulatedSignWith_eq, mean_bind]
    simp only [mean_comm (resampleW resample world)]
  have hstep : ∀ (salt root : Bits lambda) (digest : Digest lambda),
      mean (resampleW resample world) (fun w' =>
        mean (commitOracle S.signer salt witness root (simPost S publicKey message salt digest) w') Ψ) ≤
      mean (resampleW resample world) (fun w' =>
        mean (commitOracle S.signer salt fake root (simPost S publicKey message salt digest) w') Ψ) +
        (touchInner S publicKey hidden witness message salt root digest world TΨ +
          touchInner S publicKey hidden fake message salt root digest world TΨ) := by
    intro salt root digest
    have hcw : ∀ wsign w', w' ∈ (resampleW resample world).support → ∀ r,
        r ∈ (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w').support →
        GamePrune.Consistent r.2 :=
      fun wsign w' hw' r hr => commitOracle_consistent S.signer salt wsign root _ w'
        (consistent_of_mem_resampleW _ _ hw' (possible_of_consistent _ hcons)) r hr
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
          mean_le_mean _ _ _ fun w' hw' => mean_le_mean _ _ _ fun r hr => hfwd _ r.1 r.2 (hcw witness w' hw' r hr)
      _ = prunedMean S publicKey hidden witness message salt root digest world Ψ +
            touchInner S publicKey hidden witness message salt root digest world TΨ := by
          simp only [prunedMean, touchInner, mean_add]
      _ = prunedMean S publicKey hidden fake message salt root digest world Ψ +
            touchInner S publicKey hidden witness message salt root digest world TΨ := by rw [hequal]
      _ ≤ (mean (resampleW resample world) (fun w' =>
            mean (commitOracle S.signer salt fake root (simPost S publicKey message salt digest) w') fun r =>
              mean (resampleW resample r.2) fun w'' => Ψ (r.1, w'')) +
            touchInner S publicKey hidden fake message salt root digest world TΨ) +
            touchInner S publicKey hidden witness message salt root digest world TΨ := by
          refine add_le_add ?_ le_rfl
          unfold prunedMean touchInner
          simp only [← mean_add]
          exact mean_le_mean _ _ _ fun w' hw' => mean_le_mean _ _ _ fun r hr => hrev _ r.1 r.2 (hcw fake w' hw' r hr)
      _ = _ := by
          rw [← postLaw_mean (commitOracle_postLaw S.signer salt fake root _) world Ψ]
          ring
  rw [hsw witness, hsw fake]
  unfold touchMean
  simp only [← mean_add]
  exact mean_le_mean _ _ _ fun salt _ => mean_le_mean _ _ _ fun root _ => mean_le_mean _ _ _ fun digest _ => hstep salt root digest

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The per-call bound for compatible continuations of the run, from the
input-present and retry bounds, the pruned equality of the two signings
and the touching bound. -/
theorem signRunW_meanP (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S) (εRow εR εT : ℝ≥0∞) (B B' : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) B world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) B world → (retryEvent S publicKey witness message world) true ≤ εR)
    (hequal : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt root : Bits lambda)
      (digest : Spec.BAVC.Digest lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))), InvC (tau := tau) (kappa := kappa) B world →
      ∀ Ψ, prunedMean S publicKey (sigHidden S) witness message salt root digest world Ψ =
        prunedMean S publicKey (sigHidden S) fake message salt root digest world Ψ)
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
      (εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR (2 * εT) B) B B' (InvC (tau := tau) (kappa := kappa)) := by
  intro sk hsk message m world hm fuel' pk next trace hfuel h c Cp hc hCp
  have hw : InvC (tau := tau) (kappa := kappa) B world := invC_mono m B world (by omega) hm
  obtain ⟨hpk, hsol⟩ := hsk
  rcases sk with ⟨pk', witness⟩
  dsimp only at hpk hsol
  rw [hpk]
  refine call_mean S V verifyBudget publicKey sampleWitness hl htau hpc εRow εR (2 * εT) B hrow hretry witness hsol message world hw
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
  have hcore := swap_core S publicKey (sigHidden S) witness fake message world hw.2.1
    (fun r => ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1)
      r.2 trace).bind h) c)
    (fun K r => mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness)
      (next r.1) r.2 trace) fun t => mean (Cp t) fun y => indicator (touchesG K y))
    hfwd hrev (fun salt root digest => hequal witness fake message salt root digest world hw _)
  have ht₁ := htouch witness witness message m world hm fuel' hfuel pk next trace Cp hCp
  have ht₂ := htouch fake witness message m world hm fuel' hfuel pk next trace Cp hCp
  calc _ = mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey witness message w') fun r =>
          ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) := by simp only [mean_bind_apply]
    _ ≤ _ := hcore
    _ ≤ mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey fake message w') fun r =>
          ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) + (εT + εT) := add_le_add le_rfl (add_le_add ht₁ ht₂)
    _ = _ := by
        simp only [mean_bind_apply]
        ring

/-- The per-call bound for compatible continuations of the cut with its
world, from the input-present and retry bounds, the pruned equality of the
two signings and the touching bound. -/
theorem signCutW_meanP (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S) (εRow εR εT : ℝ≥0∞) (B B' : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) B world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) B world → (retryEvent S publicKey witness message world) true ≤ εR)
    (hequal : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt root : Bits lambda)
      (digest : Spec.BAVC.Digest lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))), InvC (tau := tau) (kappa := kappa) B world →
      ∀ Ψ, prunedMean S publicKey (sigHidden S) witness message salt root digest world Ψ =
        prunedMean S publicKey (sigHidden S) fake message salt root digest world Ψ)
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
      (εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR (2 * εT) B) B B' (InvC (tau := tau) (kappa := kappa)) := by
  intro sk hsk message m world hm index fuel' hfuel pk next trace h c Cp hc hCp
  have hw : InvC (tau := tau) (kappa := kappa) B world := invC_mono m B world (by omega) hm
  obtain ⟨hpk, hsol⟩ := hsk
  rcases sk with ⟨pk', witness⟩
  dsimp only at hpk hsol
  rw [hpk]
  refine call_mean S V verifyBudget publicKey sampleWitness hl htau hpc εRow εR (2 * εT) B hrow hretry witness hsol message world hw
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
  have hcore := swap_core S publicKey (sigHidden S) witness fake message world hw.2.1
    (fun r => ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
      (next r.1) r.2 trace).bind h) c)
    (fun K r => mean (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
      (next r.1) r.2 trace) fun t => mean (Cp t) fun y => indicator (touchesG K y))
    hfwd hrev (fun salt root digest => hequal witness fake message salt root digest world hw _)
  have ht₁ := htouch witness witness message m world hm index fuel' hfuel pk next trace Cp hCp
  have ht₂ := htouch fake witness message m world hm index fuel' hfuel pk next trace Cp hCp
  calc _ = mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey witness message w') fun r =>
          ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
            (next r.1) r.2 trace).bind h) c) := by simp only [mean_bind_apply]
    _ ≤ _ := hcore
    _ ≤ mean (resampleW resample world) (fun w' => mean (simulatedSignWith S publicKey fake message w') fun r =>
          ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
            (next r.1) r.2 trace).bind h) c) + (εT + εT) := add_le_add le_rfl (add_le_add ht₁ ht₂)
    _ = _ := by
        simp only [mean_bind_apply]
        ring

end
end SDitH.Proofs.SwapDischarge
