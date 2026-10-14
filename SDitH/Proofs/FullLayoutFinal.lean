import SDitH.Proofs.SeedTermDischarge
import SDitH.Proofs.SlopeChainReduction
import SDitH.Proofs.SlopeTrapBound
import SDitH.Proofs.ForkWitnessedBound
import SDitH.Proofs.ForkUnseenBound

/-! The composed forgery bound at the submitted full layout: with both the
signer's and the verifier's cipher layouts the identity layout, the input
and key maps are injective and every fiber of the key and output maps has
one element, so the layout hypotheses are discharged and the fiber
constants are one. -/

namespace SDitH.Proofs.FullLayoutFinal

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
open ForgerySlope ForgeryRSD NamedSimulatorTerms InstanceHardness SeedTermDischarge

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

/-- At the full layout the input map is injective. -/
theorem input_injective_of_eq (L : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (h : L = Spec.BAVCCipherProgram.fullLayout lambda) : Function.Injective L.input := by
  subst h; exact fun _ _ h => h

/-- At the full layout the key map is injective. -/
theorem key_injective_of_eq (L : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (h : L = Spec.BAVCCipherProgram.fullLayout lambda) : Function.Injective L.key := by
  subst h; exact fun _ _ h => h

/-- At the full layout every fiber of the key-of-output map has one element. -/
theorem keyOutput_fiber_le_one_of_eq (L : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (h : L = Spec.BAVCCipherProgram.fullLayout lambda) :
    ∀ κ, Fintype.card {r : Bits lambda // L.key (L.output r) = κ} ≤ 1 := by
  subst h
  exact fun κ => Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩

/-- At the full layout every fiber of the key map has one element. -/
theorem key_fiber_le_one_of_eq (L : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (h : L = Spec.BAVCCipherProgram.fullLayout lambda) :
    ∀ κ, Fintype.card {r : Bits lambda // L.key r = κ} ≤ 1 := by
  subst h
  exact fun κ => Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩

/-- At the full layout every fiber of the output map has one element. -/
theorem output_fiber_le_one_of_eq (L : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (h : L = Spec.BAVCCipherProgram.fullLayout lambda) :
    ∀ b, Fintype.card {r : Bits lambda // L.output r = b} ≤ 1 := by
  subst h
  exact fun b => Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩

/-- The composed forgery bound at the full layout. -/
theorem forgery_le_final_full (εSD : ℕ → ℝ≥0∞) (hhard : InstanceHard.{u} S V verifyBudget publicKey sampleWitness εSD)
    (εMask εSep εZero εSZ εBatch : ℝ≥0∞) (hlambda : 0 < lambda) (hlayoutS : S.signer.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hlayoutV : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
    (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
                (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : 1 * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : 1 * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (δLeaf : ℝ≥0∞) (hhide : LeafHide S publicKey (3 * (fuel + 1) + 2) δLeaf)
            (hsim : SimulatorTermBounds5 S V verifyBudget publicKey sampleWitness adversary encode fuel εMask εSep εZero εSZ εBatch) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        ((εMask +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
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
         ((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
         εWitOf lambda tau kappa fuel +
         unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
         (εZero +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         (εSZ +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         ((εBatch + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
          (εSD fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel))) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_final_hard_C S V verifyBudget publicKey sampleWitness adversary εSD hhard εMask εSep εZero εSZ εBatch hlambda
    hlayoutV htau encode hmid hencoding hlinesEnc hencode bound hcommit hverify hone fuel hSencode hhigher hsample hvc εR
    (input_injective_of_eq _ hlayoutS) hl hL 1 (keyOutput_fiber_le_one_of_eq _ hlayoutS) 1 (key_fiber_le_one_of_eq _ hlayoutS)
    1 (output_fiber_le_one_of_eq _ hlayoutS) q hq hretry δ hdata hNb hNR hL2 δLeaf hhide (input_injective_of_eq _ hlayoutV)
    (key_injective_of_eq _ hlayoutV) 1 (output_fiber_le_one_of_eq _ hlayoutV) hsim

end
end SDitH.Proofs.FullLayoutFinal
