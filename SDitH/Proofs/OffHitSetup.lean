import SDitH.Proofs.SlicedInvariance
import SDitH.Proofs.LeafMixtureGen
import SDitH.Proofs.HitTerm

/-! The setup of the off-hit closeness: the off-hit pruned mean as the
posterior mean of the inner mean, the bounds by one, the tuple
probability (the sliced data at the constant one) with its sum at most
one, the complement of the no-hit mass as the hit mass, and the
distinct-tree and hit terms over the uniform root. -/

namespace SDitH.Proofs.OffHitSetup

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

open SwapClose

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

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (publicKey message : List Bool) (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda)
  (wsign : Fin (selectorCount widths * w) → ZMod 2)
  (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
  (Ψ : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞)

/-- The off-hit pruned mean is the posterior mean of the inner mean. -/
theorem prunedMeanOff_eq_posterior :
    prunedMeanOff S publicKey (hitPre S) wsign message salt root digest world Ψ =
      mean (posterior world.other.cipherHistory) (SigningData.inner S publicKey message salt root digest wsign world Ψ) := by
  unfold prunedMeanOff SigningData.inner
  simp only [resampleW, resample, mean_map]
  rfl

/-- The sliced data is at most one for a functional at most one. -/
theorem sliced_le_one (hΨ : ∀ x, Ψ x ≤ 1) (h : Fin tau → Fin (2 ^ kappa)) (nodes : Nat → Spec.BAVC.Seed lambda)
    (g : Family (Bits lambda) (Bits lambda)) : sliced S publicKey message salt root digest wsign world Ψ h nodes g ≤ 1 := by
  unfold sliced
  calc _ ≤ 1 * 1 := mul_le_mul' (indicator_le_one _) (mean_le_const _ _ 1 fun o _ => ?_)
    _ = 1 := mul_one _
  unfold tailData
  refine mean_le_const _ _ 1 fun out' _ => mean_le_const _ _ 1 fun q _ => ?_
  calc _ ≤ 1 * 1 := mul_le_mul' (indicator_le_one _) (mean_le_const _ _ 1 fun w'' _ => hΨ _)
    _ = 1 := mul_one _

/-- The inner mean is at most one for a functional at most one. -/
theorem inner_le_one (hΨ : ∀ x, Ψ x ≤ 1) (g : Family (Bits lambda) (Bits lambda)) :
    SigningData.inner S publicKey message salt root digest wsign world Ψ g ≤ 1 := by
  unfold SigningData.inner
  refine mean_le_const _ _ 1 fun r _ => ?_
  calc _ ≤ 1 * 1 := mul_le_mul' (indicator_le_one _) (mean_le_const _ _ 1 fun w'' _ => hΨ _)
    _ = 1 := mul_one _

/-- The tuple probability: the sliced data at the constant one. -/
def slicedOne (h : Fin tau → Fin (2 ^ kappa)) (nodes : Nat → Spec.BAVC.Seed lambda) (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  sliced S publicKey message salt root digest wsign world (fun _ => 1) h nodes g

/-- The sliced data is at most the tuple probability. -/
theorem sliced_le_slicedOne (hΨ : ∀ x, Ψ x ≤ 1) (h : Fin tau → Fin (2 ^ kappa)) (nodes : Nat → Spec.BAVC.Seed lambda)
    (g : Family (Bits lambda) (Bits lambda)) :
    sliced S publicKey message salt root digest wsign world Ψ h nodes g ≤ slicedOne S publicKey message salt root digest wsign world h nodes g := by
  unfold slicedOne sliced tailData
  refine mul_le_mul' le_rfl (mean_le_mean _ _ _ fun o _ => mean_le_mean _ _ _ fun out' _ => mean_le_mean _ _ _ fun q _ => ?_)
  exact mul_le_mul' le_rfl (mean_le_mean _ _ _ fun w'' _ => hΨ _)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem commitsOf_done (c : Fin tau × Fin (2 ^ kappa) → Spec.BAVC.Digest lambda) :
    commitsOf (lambda := lambda) (s := s) (wit := selectorCount widths * w) (rnd := lambda * (widths.length - 1)) (.done c) = c := rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem sum_indicator_eq {γ : Type*} [Fintype γ] [DecidableEq γ] (sel : γ) :
    ∑ h : γ, indicator (decide (sel = h)) = 1 := by
  have h : ∀ h : γ, indicator (decide (sel = h)) = if h = sel then (1 : ℝ≥0∞) else 0 := by
    intro h
    by_cases hh : sel = h
    · subst hh; simp [indicator]
    · have hh' : h ≠ sel := fun h' => hh h'.symm
      simp [indicator, hh, hh']
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The tuple probabilities sum to at most one. -/
theorem sum_slicedOne_le_one (nodes : Nat → Spec.BAVC.Seed lambda) (g : Family (Bits lambda) (Bits lambda)) :
    ∑ h : Fin tau → Fin (2 ^ kappa), slicedOne S publicKey message salt root digest wsign world h nodes g ≤ 1 := by
  unfold slicedOne sliced tailData
  simp only [mean_const, mul_one, phaseView, mean_map, viewOf, commitsOf_done]
  calc _ ≤ ∑ h : Fin tau → Fin (2 ^ kappa), mean (phaseRun S.signer salt g root world.other) fun o =>
        mean (runFixed procedure trivialFamily (tau + 4) (commitTail S.signer salt wsign nodes (commitsOf o.state)) o.hashTable
          o.hashHistory [] o.trace) fun out' =>
          mean (simPost S publicKey message salt digest out'.state world.hashTable) fun q =>
            indicator (decide (sigHidden S q.1 = h)) :=
        Finset.sum_le_sum fun h _ => mul_le_of_le_one_left (zero_le _) (indicator_le_one _)
    _ = mean (phaseRun S.signer salt g root world.other) fun o =>
        mean (runFixed procedure trivialFamily (tau + 4) (commitTail S.signer salt wsign nodes (commitsOf o.state)) o.hashTable
          o.hashHistory [] o.trace) fun out' =>
          mean (simPost S publicKey message salt digest out'.state world.hashTable) fun q =>
            ∑ h : Fin tau → Fin (2 ^ kappa), indicator (decide (sigHidden S q.1 = h)) := by
        rw [sum_mean]
        refine congrArg _ (funext fun o => ?_)
        rw [sum_mean]
        refine congrArg _ (funext fun out' => ?_)
        rw [sum_mean]
    _ = 1 := by
        simp only [sum_indicator_eq, mean_const]

/-- The hit mass at a family. -/
def hitMass (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) (setFamily world g)) fun r =>
    indicator (hitPre S salt root world r)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem indicator_not_add (b : Bool) : indicator (!b) + indicator b = 1 := by
  cases b <;> simp [indicator]

/-- The no-hit mass and the hit mass sum to one. -/
theorem inner_one_add_hitMass (g : Family (Bits lambda) (Bits lambda)) :
    SigningData.inner S publicKey message salt root digest wsign world (fun _ => 1) g +
      hitMass S publicKey message salt root digest wsign world g = 1 := by
  unfold SigningData.inner hitMass
  simp only [mean_const, mul_one]
  rw [← mean_add]
  simp only [indicator_not_add, mean_const]

/-- The tuple probabilities at the expansion's tree are the no-hit mass. -/
theorem sum_slicedOne_eq (g : Family (Bits lambda) (Bits lambda)) :
    ∑ h : Fin tau → Fin (2 ^ kappa), slicedOne S publicKey message salt root digest wsign world h (baseTree S.signer salt g root) g =
      SigningData.inner S publicKey message salt root digest wsign world (fun _ => 1) g :=
  (inner_eq_sum S publicKey message salt root digest wsign world (fun _ => 1) g).symm

variable (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
  (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey) (B : Nat)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem one_sub_indicator (b : Bool) : 1 - indicator b = indicator (!b) := by
  cases b <;> simp [indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
include hL2 hin hl hL hfiber hfiberR in
/-- The distinct-tree failure over the uniform root is at most the hit
bound. -/
theorem badTree_mean_le (hw : InvC (tau := tau) (kappa := kappa) B world) :
    (mean (PMF.uniformOfFintype (Bits lambda)) fun root => mean (posterior world.other.cipherHistory) fun g =>
      1 - distInd S.signer salt world.other root g) ≤
      εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * B) := by
  have hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g world.other.cipherHistory := ⟨_, hw.2.1⟩
  have hlen : world.other.cipherHistory.length ≤ commitBudget tau kappa * B := hw.2.2
  have hcard : (keysOf world.other.cipherHistory).card ≤ commitBudget tau kappa * B := (card_keysOf_le _).trans hlen
  calc _ = mean (rootDraw world.other.cipherHistory) fun x => indicator (decide (¬ GoodTree S.signer salt world.other x)) := by
        rw [mean_rootDraw]
        refine congrArg _ (funext fun root => congrArg _ (funext fun g => ?_))
        unfold distInd
        rw [one_sub_indicator]
        simp [GoodTree]
    _ ≤ _ := bad_tree_le S.signer salt world.other hin hl hL (by omega) c hfiber cKey hfiberR hpos
        (commitBudget tau kappa * B + 2 * (tau * 2 ^ kappa - 1) + 1) (by omega)
    _ ≤ _ := by
        unfold εHit
        have hA1 : ((cKey * (keysOf world.other.cipherHistory).card : Nat) : ℝ≥0∞) ≤
            ((cKey * (commitBudget tau kappa * B) : Nat) : ℝ≥0∞) :=
          Nat.cast_le.mpr (Nat.mul_le_mul_left _ hcard)
        have hA2 : ((c * ((keysOf world.other.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) ≤
            ((c * (commitBudget tau kappa * B + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) :=
          Nat.cast_le.mpr (Nat.mul_le_mul_left _ (by omega))
        exact add_le_add (mul_le_mul' hA1 le_rfl) (mul_le_mul' le_rfl (add_le_add
          (mul_le_mul' le_rfl (ENNReal.div_le_div_right hA2 _)) le_rfl))

include hL2 hin hl hL hfiber hfiberR in
/-- The hit mass over the uniform draws is at most the hit bound. -/
theorem hitMass_mean_le (hw : InvC (tau := tau) (kappa := kappa) B world) :
    (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        mean (posterior world.other.cipherHistory) (hitMass S publicKey message salt root digest wsign world)) ≤
      εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * B) := by
  refine le_trans (le_of_eq ?_) (badTerm_hitPre S publicKey hL2 hin hl hL c hfiber cKey hfiberR B wsign message world hw)
  unfold hitMass
  simp only [resampleW, resample, mean_map]
  rfl

end
end SDitH.Proofs.OffHitSetup
