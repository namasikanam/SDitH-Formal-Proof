import SDitH.Proofs.SimulationGapCipher
import SDitH.Proofs.MeanEventCont
import SDitH.Proofs.CandidateShift
import SDitH.Proofs.CandidateKeepsFamily
import SDitH.Proofs.InvCExtra
import SDitH.Proofs.ForgeryEvents
import SDitH.Proofs.SwapDischarge

/-! The simulation gap and the composed forgery bound with the per-call
witness swaps discharged: the hybrid chain for compatible continuations,
the pruned equality of the two signings and the touching bounds replace
the per-call swap hypotheses; the events carry their compatibility and
insensitivity requirements. -/

namespace SDitH.Proofs.SimulationGapCompat

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
open GamePruneGen GamePrune RunWorld CutWorld PruneCompatClosure
open Spec.IdealCipher (Entry)
open Spec.RandomOracleTrap (indicator)
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- An event's requirements for the chain: false without a fork result,
insensitive to the snapshot world's cipher history, to the first branch's
embedded family and to the checked terminals' embedded worlds, and
compatible with pruning at the end for the touching indicator. -/
structure EventOKP (E : Snap F lambda s higherCount w widths State →
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool) : Prop where
  none : ∀ snapshot', E snapshot' none = false
  hist : ∀ snapshot' (H : List (Entry (Bits lambda) (Bits lambda))) res,
    E { snapshot' with world := { snapshot'.world with other := { snapshot'.world.other with cipherHistory := H } } } res =
      E snapshot' res
  leftW : ∀ snapshot' (a : Spec.BAVC.Digest lambda) t w₀ f H b₁ b₂ right,
    E snapshot' (some (⟨a, ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩, right)) =
      E snapshot' (some (⟨a, ⟨withWorld t w₀, b₁, b₂⟩⟩, right))
  rightW : ∀ snapshot' left t w₀ f H b₁ b₂ (a' : Spec.BAVC.Digest lambda),
    E snapshot' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) =
      E snapshot' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩))
  compat : ∀ (K : List (Bits lambda)) snapshot' c c' (a a' : Spec.BAVC.Digest lambda),
    PruneCompat (Message := List Bool) (Signature := Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))) (Query := Query lambda) K
      (fun r => rightEval snapshot' E a c c' a' r.2) (fun r => indicator (touchesG K r.2))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- An event's insensitivity to the first branch's embedded family. -/
theorem eventOK_left (E : Snap F lambda s higherCount w widths State →
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hE : EventOKP E) : ∀ snapshot' left right g,
    E snapshot' (some (setFamilyBranch g left, right)) = E snapshot' (some (left, right)) := by
  intro snapshot' left right g
  rcases left with ⟨a, ⟨t, b₁, b₂⟩⟩
  cases t with
  | attempt a' => exact hE.leftW snapshot' a (.attempt a') a'.world g a'.world.other.cipherHistory b₁ b₂ right
  | exhausted tr => rfl
  | aborted tr => rfl
  | rejected tr => rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- An event's insensitivity to the second branch's embedded family. -/
theorem eventOK_right (E : Snap F lambda s higherCount w widths State →
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hE : EventOKP E) : ∀ snapshot' left right g,
    E snapshot' (some (left, setFamilyBranch g right)) = E snapshot' (some (left, right)) := by
  intro snapshot' left right g
  rcases right with ⟨a, ⟨t, b₁, b₂⟩⟩
  cases t with
  | attempt a' => exact hE.rightW snapshot' left (.attempt a') a'.world g a'.world.other.cipherHistory b₁ b₂ a
  | exhausted tr => rfl
  | aborted tr => rfl
  | rejected tr => rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- An event's insensitivity to the second branch's history suffix. -/
theorem eventOK_shift (E : Snap F lambda s higherCount w widths State →
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hE : EventOKP E) : ∀ snapshot' left right H,
    E snapshot' (some (left, shiftBranch H right)) = E snapshot' (some (left, right)) := by
  intro snapshot' left right H
  rcases right with ⟨a, ⟨t, b₁, b₂⟩⟩
  cases t with
  | attempt a' => exact hE.rightW snapshot' left (.attempt a') a'.world a'.world.other.family (a'.world.other.cipherHistory ++ H) b₁ b₂ a
  | exhausted tr => rfl
  | aborted tr => rfl
  | rejected tr => rfl

/-- The touching bound for the run's continuations at a budget and an end
budget. -/
def TouchR (εT : ℝ≥0∞) (B B' : Nat) : Prop :=
  ∀ (wsign witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (m : Nat)
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
          r.2 trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) ≤ εT

/-- The touching bound for the cut's continuations at a budget and an end
budget. -/
def TouchC (εT : ℝ≥0∞) (B B' : Nat) : Prop :=
  ∀ (wsign witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (m : Nat)
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
          (next r.1) r.2 trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) ≤ εT

/-- The pruned equality of the two signings at a budget. -/
def PrunedEqual (B : Nat) : Prop :=
  ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt root : Bits lambda)
    (digest : Spec.BAVC.Digest lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))), InvC (tau := tau) (kappa := kappa) B world →
    ∀ Ψ, prunedMean S publicKey (sigHidden S) witness message salt root digest world Ψ =
      prunedMean S publicKey (sigHidden S) fake message salt root digest world Ψ

/-- The simulation gap for one event with the per-call swaps discharged, at
the budget three times the fuel plus two. -/
theorem hgap_meanP (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S)
    (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) (hvc : verifyBudget ≤ commitBudget tau kappa)
    (εRow εR εT : ℝ≥0∞) (fuel : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (hequal : PrunedEqual S publicKey (3 * (fuel + 1) + 2))
    (htouchR : TouchR S V verifyBudget publicKey sampleWitness adversary εT (3 * (fuel + 1) + 2) (2 * (3 * (fuel + 1) + 2) + 1))
    (htouchC : TouchC S V verifyBudget publicKey sampleWitness adversary εT (3 * (fuel + 1) + 2) (4 * (3 * (fuel + 1) + 2) + 3))
    (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hE : EventOKP E) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true +
        3 * ((fuel : ℝ≥0∞) + 1) *
          εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR (2 * εT) (3 * (fuel + 1) + 2) := by
  have hsignRunW := signRunW_meanP S V verifyBudget publicKey sampleWitness adversary hl htau hpc εRow εR εT (3 * (fuel + 1) + 2)
    (2 * (3 * (fuel + 1) + 2) + 1) hrow hretry hequal htouchR
  have hsignCut := signCutW_meanP S V verifyBudget publicKey sampleWitness adversary hl htau hpc εRow εR εT (3 * (fuel + 1) + 2)
    (4 * (3 * (fuel + 1) + 2) + 3) hrow hretry hequal htouchC
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

/-- The composed simulation term: three times the fuel plus one, times the
per-call constant at the budget three times the fuel plus two with the
explicit row-stored bound. -/
def εSimP (c cKey cOut q : Nat) (εR εT : ℝ≥0∞) (fuel : Nat) : ℝ≥0∞ :=
  3 * ((fuel : ℝ≥0∞) + 1) * εCall (lambda := lambda) (tau := tau) (kappa := kappa)
    (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (3 * (fuel + 1) + 2)) q
      (commitBudget tau kappa * (3 * (fuel + 1) + 2))) εR (2 * εT) (3 * (fuel + 1) + 2)

/-- The composed forgery bound with the per-call swaps discharged: the
pruned equality of the two signings, the touching bounds, the retry bound,
and the eight events' requirements. -/
theorem forgery_le_meanP (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR εT : ℝ≥0∞)
    (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ b, Fintype.card {r : Bits lambda // S.signer.layout.output r = b} ≤ cOut)
    (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (hequal : PrunedEqual S publicKey (3 * (fuel + 1) + 2))
    (htouchR : TouchR S V verifyBudget publicKey sampleWitness adversary εT (3 * (fuel + 1) + 2) (2 * (3 * (fuel + 1) + 2) + 1))
    (htouchC : TouchC S V verifyBudget publicKey sampleWitness adversary εT (3 * (fuel + 1) + 2) (4 * (3 * (fuel + 1) + 2) + 3))
    (hok1 : EventOKP (maskAfter (F := F) (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) (higherCount := higherCount)
      (w := w) (widths := widths) (State := State)))
    (hok2 : EventOKP (fun (_ : Snap F lambda s higherCount w widths State) => notSeparated V))
    (hok3 : EventOKP (higherCount := higherCount) (w := w) (widths := widths) (State := State) (seedCollision V))
    (hok4 : EventOKP (fun (_ : Snap F lambda s higherCount w widths State) => slopeWin S V))
    (hok5 : EventOKP (fun (_ : Snap F lambda s higherCount w widths State) => zeroChallenge V encode))
    (hok6 : EventOKP (higherCount := higherCount) (w := w) (widths := widths) (State := State) (schwartzZippel S V encode))
    (hok7 : EventOKP (higherCount := higherCount) (w := w) (widths := widths) (State := State) (batchingBad S V))
    (hok8 : EventOKP (higherCount := higherCount) (w := w) (widths := widths) (State := State) (rsdSolved S V)) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true +
            εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εT fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => notSeparated V)
            fuel) true + εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εT fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (seedCollision V) fuel)
            true + εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εT fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => slopeWin S V)
            fuel) true + εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εT fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (fun _ => zeroChallenge V encode) fuel) true +
            εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εT fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (schwartzZippel S V encode) fuel) true +
            εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εT fuel) +
         (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (batchingBad S V) fuel)
            true + εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εT fuel) +
          (solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel +
            εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εT fuel)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  have hgap := hgap_meanP S V verifyBudget publicKey sampleWitness adversary hlambda (Nat.pos_iff_ne_zero.mp htau)
    (payload_consistent S hSencode hhigher) hsample hvc _ εR εT fuel
    (fun world hw => rowTerm_mean_le_explicit S (Nat.pos_iff_ne_zero.mp htau) world _ hw.1 (invC_game _ world hw).1
      hin hl hL c hfiber cKey hkey cOut hout _ (invC_game _ world hw).2 q hq)
    hretry hequal htouchR htouchC
  exact forgery_le_simulated_events S V verifyBudget publicKey sampleWitness adversary
    (simulatedScheme S V verifyBudget publicKey sampleWitness) hlambda htau encode hmid hencoding hlinesEnc hencode bound
    hcommit hverify hone fuel (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εT fuel)
    (hgap _ hok1) (hgap _ hok2) (hgap _ hok3) (hgap _ hok4) (hgap _ hok5) (hgap _ hok6) (hgap _ hok7) (hgap _ hok8)

end
end SDitH.Proofs.SimulationGapCompat
