import SDitH.Proofs.CandidateSerialization

/-! The composed forgery bound averaged over a distribution of instances.
The per-instance bound is averaged against a probability mass function on
an index type carrying the signing setting, the encoded public key and the
witness sampler; the hardness assumption `DistributionHard` bounds the
average syndrome-decoding success of the witness-free solver over that
distribution, and the mean-square form of the bound follows by linearity.
On a finite index type the averaged advantage itself is bounded through
the weighted power-mean inequality. The instance distribution is a
parameter: the key generation's own law (Algorithm 2) is not formed,
because the literal routine reads the undefined `B` and `x_A`. -/

namespace SDitH.Proofs.DistributionalFinal

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
  {ι : Type} (p : PMF ι)
  (Sof : ι → SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (pkOf : ι → List Bool) (swOf : ι → PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type u}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The explicit terms of the composed bound as a function of its hardness
term `h`: the named simulator constants, the proved slacks and the
fork-and-extract terms, as in `SeedTermDischarge.forgery_le_final_named_C`. -/
def rhsTerms (c cKey cOut cOutV q bound fuel : Nat) (εR δ δLeaf εMask εSep εZero εSZ εBatch h : ℝ≥0∞) : ℝ≥0∞ :=
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
         εCollOf lambda tau kappa cOutV fuel +
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
          (h +
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
         digestInv lambda)

omit [NeZero tau] in
/-- The terms are affine in the hardness term. -/
theorem rhsTerms_add (c cKey cOut cOutV q bound fuel : Nat) (εR δ δLeaf εMask εSep εZero εSZ εBatch h : ℝ≥0∞) :
    rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch h =
      rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch 0 + h := by
  unfold rhsTerms
  ring

/-- The forger's winning probability with the instance drawn from `p`. -/
def averagedAdvantage (fuel : Nat) : ℝ≥0∞ :=
  ∑' i, p i * advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary fuel

/-- The witness-free solver's syndrome-decoding success with the instance drawn from `p`. -/
def averagedRSD (htau : 0 < tau) (fuel : Nat) : ℝ≥0∞ :=
  ∑' i, p i * rsdSuccess (Sof i) V verifyBudget (pkOf i) (swOf i) adversary htau fuel

/-- The hardness assumption over the instance distribution: every budgeted
adversary's solver returns a weight-`w` solution of the drawn instance with
average probability at most `εSD` of the budget. -/
def DistributionHard (εSD : ℕ → ℝ≥0∞) : Prop :=
  ∀ {State : Type u} (adversary : Adversary (List Bool) (List Bool)
      (Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
      (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)
    (htau : 0 < tau) (fuel : Nat),
    averagedRSD p Sof V verifyBudget pkOf swOf adversary htau fuel ≤ εSD fuel

/-- The mean-square form of the composed forgery bound over the instance distribution. -/
theorem forgery_le_final_meanSquare (εSD : ℕ → ℝ≥0∞)
    (hhard : DistributionHard.{u} p Sof V verifyBudget pkOf swOf εSD) (εMask εSep εZero εSZ εBatch : ℝ≥0∞) (hlambda : 0 < lambda) (hlayoutV : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : ∀ i, V.middle = candidateMiddle (Sof i).signer.xi (Sof i).signer.p V.nodes encode (Sof i).signer.randomCount (Sof i).signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : ∀ i, encode = fun hidden => Spec.BLC.psi (Sof i).signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat)
    (hSencode : ∀ i, (Sof i).encode = fun hidden => psi (Sof i).signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hhigher : 1 ≤ higherCount) (hsample : ∀ i, ∀ witness ∈ (swOf i).support, IsSolution (Sof i) witness)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR : ℝ≥0∞)
    (hin : ∀ i, Function.Injective (Sof i).signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ i, ∀ κ, Fintype.card {r : Bits lambda // (Sof i).signer.layout.key ((Sof i).signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ i, ∀ κ, Fintype.card {r : Bits lambda // (Sof i).signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ i, ∀ b, Fintype.card {r : Bits lambda // (Sof i).signer.layout.output r = b} ≤ cOut)
    (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ i, ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent (Sof i) (pkOf i) witness message world) true ≤ εR)
    (δ : ℝ≥0∞) (hdata : ∀ i, DataClose (Sof i) (pkOf i) (3 * (fuel + 1) + 2) δ)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (δLeaf : ℝ≥0∞) (hhide : ∀ i, LeafHide (Sof i) (pkOf i) (3 * (fuel + 1) + 2) δLeaf)
    (hinV : Function.Injective V.layout.input) (hkeyV : Function.Injective V.layout.key)
    (cOutV : Nat) (houtV : ∀ b, Fintype.card {r : Bits lambda // V.layout.output r = b} ≤ cOutV)
    (hsim : ∀ i, SimulatorTermBounds5 (Sof i) V verifyBudget (pkOf i) (swOf i) adversary encode fuel εMask εSep εZero εSZ εBatch) :
    ∑' i, p i * (advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch (εSD fuel) := by
  have hpt : ∀ i, (advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) - digestInv lambda) ^ 2 ≤ ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch (rsdSuccess (Sof i) V verifyBudget (pkOf i) (swOf i) adversary htau fuel) := fun i =>
    forgery_le_final_named_C (Sof i) V verifyBudget (pkOf i) (swOf i) adversary εMask εSep εZero εSZ εBatch hlambda hlayoutV
      htau encode (hmid i) hencoding hlinesEnc (hencode i) bound hcommit hverify hone fuel (hSencode i) hhigher (hsample i) hvc εR
      (hin i) hl hL c (hfiber i) cKey (hkey i) cOut (hout i) q hq (hretry i) δ (hdata i) hNb hNR hL2 δLeaf (hhide i) hinV hkeyV
      cOutV houtV (hsim i)
  calc ∑' i, p i * (advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) - digestInv lambda) ^ 2
      ≤ ∑' i, p i * (((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch (rsdSuccess (Sof i) V verifyBudget (pkOf i) (swOf i) adversary htau fuel)) := ENNReal.tsum_le_tsum fun i => mul_le_mul_right (hpt i) _
    _ = ∑' i, (p i * (((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch (0)) + ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * (p i * rsdSuccess (Sof i) V verifyBudget (pkOf i) (swOf i) adversary htau fuel)) := by
        refine tsum_congr fun i => ?_
        rw [rhsTerms_add]
        ring
    _ = ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch (0) + ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * ∑' i, p i * rsdSuccess (Sof i) V verifyBudget (pkOf i) (swOf i) adversary htau fuel := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul, ENNReal.tsum_mul_left]
    _ ≤ ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch (0) + ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * εSD fuel := add_le_add_right (mul_le_mul_right (hhard adversary htau fuel) _) _
    _ = ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch (εSD fuel) := by
        rw [rhsTerms_add (h := εSD fuel)]
        ring

/-- The composed forgery bound on the averaged advantage over a finite
instance distribution. -/
theorem averaged_forgery_le_final [Fintype ι] (εSD : ℕ → ℝ≥0∞)
    (hhard : DistributionHard.{u} p Sof V verifyBudget pkOf swOf εSD) (εMask εSep εZero εSZ εBatch : ℝ≥0∞) (hlambda : 0 < lambda) (hlayoutV : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : ∀ i, V.middle = candidateMiddle (Sof i).signer.xi (Sof i).signer.p V.nodes encode (Sof i).signer.randomCount (Sof i).signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : ∀ i, encode = fun hidden => Spec.BLC.psi (Sof i).signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat)
    (hSencode : ∀ i, (Sof i).encode = fun hidden => psi (Sof i).signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hhigher : 1 ≤ higherCount) (hsample : ∀ i, ∀ witness ∈ (swOf i).support, IsSolution (Sof i) witness)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR : ℝ≥0∞)
    (hin : ∀ i, Function.Injective (Sof i).signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ i, ∀ κ, Fintype.card {r : Bits lambda // (Sof i).signer.layout.key ((Sof i).signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ i, ∀ κ, Fintype.card {r : Bits lambda // (Sof i).signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ i, ∀ b, Fintype.card {r : Bits lambda // (Sof i).signer.layout.output r = b} ≤ cOut)
    (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ i, ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent (Sof i) (pkOf i) witness message world) true ≤ εR)
    (δ : ℝ≥0∞) (hdata : ∀ i, DataClose (Sof i) (pkOf i) (3 * (fuel + 1) + 2) δ)
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (δLeaf : ℝ≥0∞) (hhide : ∀ i, LeafHide (Sof i) (pkOf i) (3 * (fuel + 1) + 2) δLeaf)
    (hinV : Function.Injective V.layout.input) (hkeyV : Function.Injective V.layout.key)
    (cOutV : Nat) (houtV : ∀ b, Fintype.card {r : Bits lambda // V.layout.output r = b} ≤ cOutV)
    (hsim : ∀ i, SimulatorTermBounds5 (Sof i) V verifyBudget (pkOf i) (swOf i) adversary encode fuel εMask εSep εZero εSZ εBatch) :
    (averagedAdvantage p Sof V verifyBudget pkOf swOf adversary (fuel + 1) - digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 * rhsTerms (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) c cKey cOut cOutV q bound fuel εR δ δLeaf εMask εSep εZero εSZ εBatch (εSD fuel) := by
  have hmean := forgery_le_final_meanSquare p Sof V verifyBudget pkOf swOf adversary εSD hhard εMask εSep εZero εSZ εBatch
    hlambda hlayoutV htau encode hmid hencoding hlinesEnc hencode bound hcommit hverify hone fuel hSencode hhigher hsample hvc εR
    hin hl hL c hfiber cKey hkey cOut hout q hq hretry δ hdata hNb hNR hL2 δLeaf hhide hinV hkeyV cOutV houtV hsim
  have hsum1 : ∑ i, p i = 1 := by
    have h := p.tsum_coe
    rw [tsum_fintype] at h
    exact h
  have h1 : averagedAdvantage p Sof V verifyBudget pkOf swOf adversary (fuel + 1) - digestInv lambda ≤ ∑ i, p i * (advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) - digestInv lambda) := by
    unfold averagedAdvantage
    rw [tsum_fintype, tsub_le_iff_right]
    calc ∑ i, p i * advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) ≤ ∑ i, p i * ((advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) - digestInv lambda) + digestInv lambda) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_right le_tsub_add _
      _ = ∑ i, p i * (advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) - digestInv lambda) + digestInv lambda := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum1, one_mul]
  have h2 : (averagedAdvantage p Sof V verifyBudget pkOf swOf adversary (fuel + 1) - digestInv lambda) ^ 2 ≤ (∑ i, p i * (advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) - digestInv lambda)) ^ 2 := pow_le_pow_left' h1 2
  have h3 : (∑ i, p i * (advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) - digestInv lambda)) ^ 2 ≤ ∑ i, p i * (advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) - digestInv lambda) ^ 2 := by
    have := ENNReal.rpow_arith_mean_le_arith_mean_rpow (s := Finset.univ) p (fun i => advantage (scheme (Spec.CandidateScheme.components (Sof i) V verifyBudget (pkOf i) (swOf i))) adversary (fuel + 1) - digestInv lambda) hsum1 (p := 2) one_le_two
    simpa only [ENNReal.rpow_two] using this
  rw [tsum_fintype] at hmean
  exact (h2.trans h3).trans hmean

end
end SDitH.Proofs.DistributionalFinal
