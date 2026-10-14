import SDitH.Proofs.ForgerySlope
import SDitH.Proofs.ForgeryRSD
import SDitH.Proofs.NamedSimulatorTerms
import SDitH.Proofs.InstanceHardness
import SDitH.Proofs.SlopeChainReduction
import SDitH.Proofs.SlopeTrapBound
import SDitH.Proofs.ForkWitnessedBound
import SDitH.Proofs.ForkUnseenBound
import SDitH.Proofs.SepEvents
import SDitH.Proofs.CandidateSerialization

/-! The composed forgery bound with the single-execution extraction: the
chain from the per-event simulation gaps to the final statement for the
events of `SepEvents`. The transferred events are the mask after the fork,
the full agreement of the hidden tuples, the zero challenge and the
solution event; the seed collision, the mask trap, the witnessed pair and
the unseen match keep their real-experiment bounds; the Schwartz–Zippel
and batching events stay in the real experiment as named constants. -/

namespace SDitH.Proofs.SepChain

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

universe u
open TouchBound SimulationGapCompat ForgeryFinal PruneCompatClosure EventRequirements

open SwapClose ForgeryHide SeedCollisionBound ForgeryColl ForgeryData SlopeChainReduction SlopeTrapBound ForkWitnessedBound
open ForkUnseenBound SlopeCoverFork SharedSlopeBound

open SwapClose SwapCloseSplit PhaseViewLeaf CommitPhaseLeaf CommitRunLeaf CommitRunExchange TailRun PrefixOrMention HiddenTuple
open RunBind RunHistoryShift CommitPhaseExchange SharedPrune
open NodeTouchBound (sum_mean)
open HiddenSlice (mean_congr_support)
open Spec.SharedSigner (commitProgram commitBudget)
open Spec.SlopeConsistencyGame (Out)
open Spec.HashCipherTrace (runFixed Result)
open Spec.HashCipherProgram (procedure Program)
open Spec.IdealCipher (Family)

open SigningData LeafJointBound LeafBlockBound LeafMixture LeafExchangeDistinct PhaseViewLeafAll HonestLeafBound
open HiddenKeysAllExchange TreeHistoryExchange TreeExchange NodeExchange PosteriorNodeBound TreeDistinct TreeStepFresh
open SharedPrune HiddenLeafNode
open Spec.SlopeConsistencyGame (Out)
open Spec.HashCipherTrace (runFixed Result)
open Spec.HashCipherProgram (procedure Program)
open Spec.IdealCipher (Family)
open Spec.SeedTree (leafAddress node)

open SlicedInvariance LeafMixtureGen HitTerm TouchTotal TouchAssembly RootPosteriorBound TreeDistinct
open Spec.SlopeConsistencyGame (Out)
open Spec.HashCipherTrace (runFixed Result)
open Spec.HashCipherProgram (procedure Program)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)

open OffHitSetup
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)

open OffHitChain TupleOfDigest
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)

open OffHitAssembly
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)

open OffHitClose ForgeryData LeafTermBound
open ForgerySlope ForgeryRSD NamedSimulatorTerms InstanceHardness SeedTermDischarge FullLayoutFinal

noncomputable section


variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type u}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

variable (sim : Scheme (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
    (Signature (Spec.BAVC.Digest lambda) (Option (Bod F lambda tau kappa s higherCount w widths)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
    (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))

/-- The forgery reduction with the simulation gap taken for the four
transferred events. -/
theorem forgery_le_simulated_events (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) (epsSim εSeedR : ℝ≥0∞)
    (hgap1 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter fuel) true ≤ (simEventExperiment adversary sim maskAfter fuel) true + epsSim)
    (hgap2 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => SepEvents.allAgree V) fuel) true ≤ (simEventExperiment adversary sim (fun _ => SepEvents.allAgree V) fuel) true + epsSim)
    (hgap3 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true ≤ εSeedR)
    (hgap5 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) fuel) true ≤ (simEventExperiment adversary sim (fun _ => zeroChallenge V encode) fuel) true + epsSim)
    (hgap8 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.rsdSolvedPlus S V encode htau) fuel) true ≤
      (simEventExperiment adversary sim (SepEvents.rsdSolvedPlus S V encode htau) fuel) true + epsSim) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary sim maskAfter fuel) true + epsSim) +
         ((simEventExperiment adversary sim (fun _ => SepEvents.allAgree V) fuel) true + epsSim) +
         εSeedR +
         ((randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot _ => slopeTrap S V snapshot) fuel) true +
          (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => witnessedFork snapshot) fuel) true +
          (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => unseenFork V snapshot) fuel) true) +
         ((simEventExperiment adversary sim (fun _ => zeroChallenge V encode) fuel) true + epsSim) +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.szPlus S V encode htau) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.batchingPlus S V encode htau) fuel) true +
         (SepEvents.solverSuccess S V adversary sim htau fuel + epsSim) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  refine (SepEvents.forgery_le_events S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc
    bound hcommit hverify hone fuel).trans (mul_le_mul_right ?_ _)
  refine add_le_add_left (add_le_add_left ?_ _) _
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hgap1 hgap2) hgap3) le_rfl) hgap5)
    le_rfl) le_rfl) (hgap8.trans (add_le_add_left (SepEvents.solverSuccess_ge S V adversary sim encode htau fuel) _))

/-- The composed forgery bound under the pruned closeness. -/
theorem forgery_le_final_close (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
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
    (hL2 : 2 ≤ tau * 2 ^ kappa)
    (εLeaf : ℝ≥0∞) (hleafR : LeafR S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (hleafC : LeafC S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (εColl : ℝ≥0∞)
    (hcoll : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true ≤ εColl) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf)
              εPre fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => SepEvents.allAgree V) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf)
              εPre fuel + εColl)) +
         εColl +
         (((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
          εWitOf lambda tau kappa fuel +
          unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => zeroChallenge V encode) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf)
              εPre fuel + εColl)) +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.szPlus S V encode htau) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.batchingPlus S V encode htau) fuel) true +
         (SepEvents.solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf)
              εPre fuel + εColl)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  (forgery_le_simulated_events S V verifyBudget publicKey sampleWitness adversary
    (simulatedScheme S V verifyBudget publicKey sampleWitness) hlambda htau encode hmid hencoding hlinesEnc bound hcommit hverify
    hone fuel (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf)
              εPre fuel + εColl) εColl
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ eventOKP_maskAfter)
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ (SepEvents.eventOKP_allAgree V))
    hcoll
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_zeroChallenge V encode))
    (hgap_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry εPre hclose hNb hNR hL2 εLeaf hleafR hleafC εColl _ (SepEvents.eventOKP_rsdSolvedPlus S V encode htau))).trans
    (mul_le_mul_right (add_le_add_left (add_le_add_left (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add (add_le_add le_rfl le_rfl) le_rfl)
      (add_le_add (add_le_add (slopeTrap_le S V verifyBudget publicKey sampleWitness adversary bound hcommit hverify hone fuel)
        (witnessedFork_le S V verifyBudget publicKey sampleWitness adversary hvc hl fuel))
        (unseenFork_le S V verifyBudget publicKey sampleWitness adversary hvc hl fuel))) le_rfl) le_rfl) le_rfl) le_rfl) _) _) _)

/-- The composed forgery bound under the data-level closeness. -/
theorem forgery_le_final_data (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
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
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa)
    (εLeaf : ℝ≥0∞) (hleafR : LeafR S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (hleafC : LeafC S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (εColl : ℝ≥0∞)
    (hcoll : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true ≤ εColl) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf)
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => SepEvents.allAgree V) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf)
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εColl)) +
         εColl +
         (((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
          εWitOf lambda tau kappa fuel +
          unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => zeroChallenge V encode) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf)
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εColl)) +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.szPlus S V encode htau) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.batchingPlus S V encode htau) fuel) true +
         (SepEvents.solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf)
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εColl)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_final_close S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc bound
    hcommit hverify hone fuel hSencode hhigher hsample hvc εR hin hl hL c hfiber cKey hkey cOut hout q hq hretry _
    (prunedClose_of_dataClose S publicKey hL2 hin hl hL c hfiber cKey hkey (3 * (fuel + 1) + 2) hNb δ hdata) hNb hNR hL2 εLeaf
    hleafR hleafC εColl hcoll

/-- The composed forgery bound under the leaf hiding. -/
theorem forgery_le_final_hide (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
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
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa)
    (δLeaf : ℝ≥0∞) (hhide : LeafHide S publicKey (3 * (fuel + 1) + 2) δLeaf)
    (εColl : ℝ≥0∞)
    (hcoll : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true ≤ εColl) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => SepEvents.allAgree V) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εColl)) +
         εColl +
         (((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
          εWitOf lambda tau kappa fuel +
          unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => zeroChallenge V encode) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εColl)) +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.szPlus S V encode htau) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.batchingPlus S V encode htau) fuel) true +
         (SepEvents.solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εColl)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_final_data S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc bound
    hcommit hverify hone fuel hSencode hhigher hsample hvc εR hin hl hL c hfiber cKey hkey cOut hout q hq hretry δ hdata hNb hNR
    hL2 _
    (leafR_of_leafHide S publicKey hL2 hin hl hL c hfiber (3 * (fuel + 1) + 2) hNb V verifyBudget sampleWitness adversary δLeaf hhide)
    (leafC_of_leafHide S publicKey hL2 hin hl hL c hfiber (3 * (fuel + 1) + 2) hNb V verifyBudget sampleWitness adversary δLeaf hhide)
    εColl hcoll

/-- The composed forgery bound with the seed-collision term explicit. -/
theorem forgery_le_final_coll (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
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
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa)
    (δLeaf : ℝ≥0∞) (hhide : LeafHide S publicKey (3 * (fuel + 1) + 2) δLeaf)
    (hinV : Function.Injective V.layout.input) (hkeyV : Function.Injective V.layout.key)
    (cOutV : Nat) (houtV : ∀ b, Fintype.card {r : Bits lambda // V.layout.output r = b} ≤ cOutV) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => SepEvents.allAgree V) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         εCollOf lambda tau kappa cOutV fuel +
         (((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
          εWitOf lambda tau kappa fuel +
          unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => zeroChallenge V encode) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.szPlus S V encode htau) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.batchingPlus S V encode htau) fuel) true +
         (SepEvents.solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_final_hide S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc bound
    hcommit hverify hone fuel hSencode hhigher hsample hvc εR hin hl hL c hfiber cKey hkey cOut hout q hq hretry δ hdata hNb hNR
    hL2 δLeaf hhide (εCollOf lambda tau kappa cOutV fuel)
    (seedCollision_le S V verifyBudget publicKey sampleWitness adversary hvc hinV hkeyV hl hL cOutV houtV fuel)

/-- The composed forgery bound with the hardness term as the
syndrome-decoding success. -/
theorem forgery_le_final_rsd (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
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
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa)
    (δLeaf : ℝ≥0∞) (hhide : LeafHide S publicKey (3 * (fuel + 1) + 2) δLeaf)
    (hinV : Function.Injective V.layout.input) (hkeyV : Function.Injective V.layout.key)
    (cOutV : Nat) (houtV : ∀ b, Fintype.card {r : Bits lambda // V.layout.output r = b} ≤ cOutV) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => SepEvents.allAgree V) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         εCollOf lambda tau kappa cOutV fuel +
         (((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
          εWitOf lambda tau kappa fuel +
          unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => zeroChallenge V encode) fuel) true + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.szPlus S V encode htau) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.batchingPlus S V encode htau) fuel) true +
         (SepEvents.rsdSuccess S V verifyBudget publicKey sampleWitness adversary htau fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  (forgery_le_final_coll S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc bound
    hcommit hverify hone fuel hSencode hhigher hsample hvc εR hin hl hL c hfiber cKey hkey cOut hout q hq hretry δ hdata hNb hNR
    hL2 δLeaf hhide hinV hkeyV cOutV houtV).trans
    (mul_le_mul_right (add_le_add_left (add_le_add_left (add_le_add_right (add_le_add_left
      (SepEvents.solverSuccess_le_rsd S V verifyBudget publicKey sampleWitness adversary htau fuel) _) _) _) _) _)

/-- The three transferred simulator terms, each bounded by a named constant. -/
def SimulatorTermBounds3 (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat) (εMask εSep εZero : ℝ≥0∞) : Prop :=
  (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true ≤ εMask ∧
  (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => SepEvents.allAgree V) fuel) true ≤ εSep ∧
  (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => zeroChallenge V encode) fuel) true ≤ εZero

/-- The two real-experiment terms, each bounded by a named constant. -/
def RealTermBounds (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau) (fuel : Nat) (εSZ εBatch : ℝ≥0∞) : Prop :=
  (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.szPlus S V encode htau) fuel) true ≤ εSZ ∧
  (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (SepEvents.batchingPlus S V encode htau) fuel) true ≤ εBatch

/-- The composed forgery bound with the simulator and real-experiment terms
as named constants. -/
theorem forgery_le_final_named (εMask εSep εZero εSZ εBatch : ℝ≥0∞)
    (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
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
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa)
    (δLeaf : ℝ≥0∞) (hhide : LeafHide S publicKey (3 * (fuel + 1) + 2) δLeaf)
    (hinV : Function.Injective V.layout.input) (hkeyV : Function.Injective V.layout.key)
    (cOutV : Nat) (houtV : ∀ b, Fintype.card {r : Bits lambda // V.layout.output r = b} ≤ cOutV)
    (hsim : SimulatorTermBounds3 S V verifyBudget publicKey sampleWitness adversary encode fuel εMask εSep εZero)
    (hreal : RealTermBounds S V verifyBudget publicKey sampleWitness adversary encode htau fuel εSZ εBatch) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        ((εMask + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         (εSep + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         εCollOf lambda tau kappa cOutV fuel +
         (((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
          εWitOf lambda tau kappa fuel +
          unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2))) +
         (εZero + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         εSZ +
         εBatch +
         (SepEvents.rsdSuccess S V verifyBudget publicKey sampleWitness adversary htau fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  obtain ⟨hmask, hsep, hzero⟩ := hsim
  obtain ⟨hsz, hbatch⟩ := hreal
  refine (forgery_le_final_rsd S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc
    bound hcommit hverify hone fuel hSencode hhigher hsample hvc εR hin hl hL c hfiber cKey hkey cOut hout q hq hretry δ hdata
    hNb hNR hL2 δLeaf hhide hinV hkeyV cOutV houtV).trans ?_
  gcongr

/-- The hardness assumption on the key generation's instance, for the
single-execution solver. -/
def InstanceHard (εSD : ℕ → ℝ≥0∞) : Prop :=
  ∀ {State : Type u} (adversary : Adversary (List Bool) (List Bool)
      (Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
      (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)
    (htau : 0 < tau) (fuel : Nat),
    SepEvents.rsdSuccess S V verifyBudget publicKey sampleWitness adversary htau fuel ≤ εSD fuel

/-- The composed forgery bound under the named hardness assumption. -/
theorem forgery_le_final_hard (εSD : ℕ → ℝ≥0∞) (hhard : InstanceHard.{u} S V verifyBudget publicKey sampleWitness εSD)
    (εMask εSep εZero εSZ εBatch : ℝ≥0∞)
    (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
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
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa)
    (δLeaf : ℝ≥0∞) (hhide : LeafHide S publicKey (3 * (fuel + 1) + 2) δLeaf)
    (hinV : Function.Injective V.layout.input) (hkeyV : Function.Injective V.layout.key)
    (cOutV : Nat) (houtV : ∀ b, Fintype.card {r : Bits lambda // V.layout.output r = b} ≤ cOutV)
    (hsim : SimulatorTermBounds3 S V verifyBudget publicKey sampleWitness adversary encode fuel εMask εSep εZero)
    (hreal : RealTermBounds S V verifyBudget publicKey sampleWitness adversary encode htau fuel εSZ εBatch) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        ((εMask + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         (εSep + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         εCollOf lambda tau kappa cOutV fuel +
         (((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
          εWitOf lambda tau kappa fuel +
          unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2))) +
         (εZero + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         εSZ +
         εBatch +
         (εSD fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  have hrsd := hhard adversary htau fuel
  refine (forgery_le_final_named S V verifyBudget publicKey sampleWitness adversary εMask εSep εZero εSZ εBatch hlambda htau encode
    hmid hencoding hlinesEnc bound hcommit hverify hone fuel hSencode hhigher hsample hvc εR hin hl hL c hfiber cKey hkey cOut hout
    q hq hretry δ hdata hNb hNR hL2 δLeaf hhide hinV hkeyV cOutV houtV hsim hreal).trans ?_
  gcongr

/-- The composed forgery bound at the full layout and the candidate encoding. -/
theorem forgery_le_final_full_enc (εSD : ℕ → ℝ≥0∞) (hhard : InstanceHard.{u} S V verifyBudget publicKey sampleWitness εSD)
    (εMask εSep εZero εSZ εBatch : ℝ≥0∞)
    (hlambda : 0 < lambda) (hlayoutS : S.signer.layout = Spec.BAVCCipherProgram.fullLayout lambda)
    (hlayoutV : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hV : V.encoding = CandidateSerialization.candidateSerialization tau kappa s)
    (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat)
    (hSencode : S.encode = fun hidden => psi S.signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hhigher : 1 ≤ higherCount) (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR : ℝ≥0∞)
    (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : 1 * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : 1 * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa)
    (δLeaf : ℝ≥0∞) (hhide : LeafHide S publicKey (3 * (fuel + 1) + 2) δLeaf)
    (hsim : SimulatorTermBounds3 S V verifyBudget publicKey sampleWitness adversary encode fuel εMask εSep εZero)
    (hreal : RealTermBounds S V verifyBudget publicKey sampleWitness adversary encode htau fuel εSZ εBatch) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        ((εMask + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         (εSep + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         εCollOf lambda tau kappa 1 fuel +
         (((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
          εWitOf lambda tau kappa fuel +
          unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2))) +
         (εZero + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         εSZ +
         εBatch +
         (εSD fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_final_hard S V verifyBudget publicKey sampleWitness adversary εSD hhard εMask εSep εZero εSZ εBatch hlambda htau encode
    hmid (by rw [hV]; exact CandidateSerialization.sourceTail_injective) (by rw [hV]; exact CandidateSerialization.lines_injective)
    bound hcommit hverify hone fuel hSencode hhigher hsample hvc εR (input_injective_of_eq _ hlayoutS) hl hL
    1 (keyOutput_fiber_le_one_of_eq _ hlayoutS) 1 (key_fiber_le_one_of_eq _ hlayoutS) 1 (output_fiber_le_one_of_eq _ hlayoutS)
    q hq hretry δ hdata hNb hNR hL2 δLeaf hhide (input_injective_of_eq _ hlayoutV) (key_injective_of_eq _ hlayoutV)
    1 (output_fiber_le_one_of_eq _ hlayoutV) hsim hreal

end
end SDitH.Proofs.SepChain
