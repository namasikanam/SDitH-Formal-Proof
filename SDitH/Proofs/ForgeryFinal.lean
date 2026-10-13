import SDitH.Proofs.TouchBound

/-! The composed forgery bound with the touching bounds instantiated from
the touching total. The squared advantage is bounded by the simulator's
event probabilities, the solver's success and explicit terms, under the
pruned equality of the two signings, the leaf-term bounds, the retry
bound, the layout's fiber bounds and size conditions, and the eight
events' requirements. -/

namespace SDitH.Proofs.ForgeryFinal

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
open GamePruneGen GamePrune RunWorld CutWorld
open Spec.IdealCipher (Entry)
open Spec.RandomOracleTrap (indicator)
open scoped Classical ENNReal
open TouchBound SimulationGapCompat

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

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The uniform touching bound is monotone in the end budget. -/
theorem εTouch_mono (c cKey M B' B'' : Nat) (εLeaf : ℝ≥0∞) (h : B' ≤ B'') :
    εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey M B' εLeaf ≤
      εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey M B'' εLeaf := by
  unfold εTouch
  exact add_le_add le_rfl (add_le_add (mul_le_mul' le_rfl (Nat.cast_le.mpr (Nat.mul_le_mul_left _ h))) le_rfl)

/-- The run's touching bound is monotone in the bound. -/
theorem touchR_mono (εT εT' : ℝ≥0∞) (B B' : Nat) (h : TouchR S V verifyBudget publicKey sampleWitness adversary εT B B')
    (hle : εT ≤ εT') : TouchR S V verifyBudget publicKey sampleWitness adversary εT' B B' :=
  fun wsign witness message m world hw fuel' hfuel pk next trace Cp hCp =>
    (h wsign witness message m world hw fuel' hfuel pk next trace Cp hCp).trans hle

/-- The composed forgery bound with the touching bounds instantiated: the
pruned equality of the two signings, the leaf-term bounds, the retry
bound, the layout's fiber bounds and size conditions, and the eight events'
requirements. -/
theorem forgery_le_final (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
    (hequal : PrunedEqual S publicKey (3 * (fuel + 1) + 2))
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (εLeaf : ℝ≥0∞)
    (hleafR : LeafR S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (hleafC : LeafC S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
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
            εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => notSeparated V)
            fuel) true + εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (seedCollision V) fuel)
            true + εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => slopeWin S V)
            fuel) true + εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (fun _ => zeroChallenge V encode) fuel) true +
            εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (schwartzZippel S V encode) fuel) true +
            εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel) +
         (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (batchingBad S V) fuel)
            true + εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel) +
          (solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel +
            εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_meanP S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc hencode bound hcommit
    hverify hone fuel hSencode hhigher hsample hvc εR _ hin hl hL c hfiber cKey hkey cOut hout q hq hretry hequal
    (touchR_mono S V verifyBudget publicKey sampleWitness adversary _ _ _ _
      (touchR_of S V verifyBudget publicKey sampleWitness adversary hL2 hin hl hL c hfiber cKey hkey hvc _ _ hNb hNR εLeaf hleafR)
      (εTouch_mono c cKey _ _ _ εLeaf (by omega)))
    (touchC_of S V verifyBudget publicKey sampleWitness adversary hL2 hin hl hL c hfiber cKey hkey hvc _ _ hNb hNR εLeaf hleafC)
    hok1 hok2 hok3 hok4 hok5 hok6 hok7 hok8

end
end SDitH.Proofs.ForgeryFinal
