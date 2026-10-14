import SDitH.Proofs.NamedSimulatorTerms
import SDitH.Proofs.SlopeChainReduction
import SDitH.Proofs.SlopeTrapBound
import SDitH.Proofs.ForkWitnessedBound
import SDitH.Proofs.ForkUnseenBound

/-! The hardness assumption on the key generation's instance: for every
budgeted adversary, the witness-free solver's probability of returning a
weight-`w` solution of the public instance is at most a named function of
the budget. With it, the composed forgery bound is stated with named
constants and proved slacks only. The assumption is on the fixed instance of
the signing setting; relating that instance to a hardness distribution over
instances is a separate, recorded decision. -/

namespace SDitH.Proofs.InstanceHardness

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
open ForkUnseenBound SlopeCoverFork SharedSlopeBound ForgerySlope SolutionRegular ForgeryRSD NamedSimulatorTerms

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

/-- The hardness assumption on the key generation's instance: every budgeted
adversary's solver returns a weight-`w` solution of the public instance with
probability at most `εSD` of the budget. -/
def InstanceHard (εSD : ℕ → ℝ≥0∞) : Prop :=
  ∀ {State : Type u} (adversary : Adversary (List Bool) (List Bool)
      (Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
      (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)
    (htau : 0 < tau) (fuel : Nat),
    rsdSuccess S V verifyBudget publicKey sampleWitness adversary htau fuel ≤ εSD fuel

/-- The composed forgery bound under the named hardness assumption: the
right-hand side is explicit in the named constants and the proved slacks. -/
theorem forgery_le_final_hard (εSD : ℕ → ℝ≥0∞) (hhard : InstanceHard.{u} S V verifyBudget publicKey sampleWitness εSD)
    (εMask εSep εSeed εZero εSZ εBatch : ℝ≥0∞) (hlambda : 0 < lambda) (hlayoutV : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (δLeaf : ℝ≥0∞) (hhide : LeafHide S publicKey (3 * (fuel + 1) + 2) δLeaf)
    (hinV : Function.Injective V.layout.input) (hkeyV : Function.Injective V.layout.key)
    (cOutV : Nat) (houtV : ∀ b, Fintype.card {r : Bits lambda // V.layout.output r = b} ≤ cOutV)
    (hsim : SimulatorTermBounds S V verifyBudget publicKey sampleWitness adversary encode fuel εMask εSep εSeed εZero εSZ εBatch) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        ((εMask +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         (εSep + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         (εSeed + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         ((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
         εWitOf lambda tau kappa fuel +
         unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
         (εZero +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         (εSZ +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
         ((εBatch + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel)) +
          (εSD fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa cOutV fuel))) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  refine (forgery_le_final_named S V verifyBudget publicKey sampleWitness adversary εMask εSep εSeed εZero εSZ εBatch hlambda
    hlayoutV htau encode hmid hencoding hlinesEnc hencode bound hcommit hverify hone fuel hSencode hhigher hsample hvc εR hin hl
    hL c hfiber cKey hkey cOut hout q hq hretry δ hdata hNb hNR hL2 δLeaf hhide hinV hkeyV cOutV houtV hsim).trans ?_
  gcongr
  exact hhard adversary htau fuel

end
end SDitH.Proofs.InstanceHardness
