import SDitH.Proofs.LeafSliced
import SDitH.Proofs.OffHitClose

/-! The leaf term from the leaf hiding. The leaf hit at an execution's hidden
leaf is the sliced data of the functional recording the leaf's key, at the
expansion's tree; with the tuple's leaves replaced it is the mixing family
of that functional, invariant under the exchange. The leaf hiding, a named
data-level hypothesis, bounds the mixing family's mean over uniform
blocks; the mixture upper bound then bounds the leaf term, over the two
tuples carrying mass and the executions. -/

namespace SDitH.Proofs.LeafTermBound

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

open OffHitSetup
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)

open OffHitChain TupleOfDigest
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)

open OffHitAssembly TouchSplit TouchAssembly TouchIdentity TouchBound RootPosteriorBound
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)
open Spec.HashCipherTrace (runFixed Result)
open Spec.HashCipherProgram (procedure Program)

open LeafSliced OffHitClose AllViewBounds OwnViewExchange CommitViewExchange
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)
open Spec.HashCipherTrace (runFixed Result)
open Spec.HashCipherProgram (procedure Program)

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (publicKey message : List Bool) (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda)
  (wsign : Fin (selectorCount widths * w) → ZMod 2)
  (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
  (Gc : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF (Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))))

/-- The functional recording a key: the continuation's probability of
recording it. -/
def keyFun (κ : Bits lambda) : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞ :=
  fun p => mean (Gc p.1 p.2) fun y => indicator (decide (κ ∈ keysOf (newT y)))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem keyFun_le_one (κ : Bits lambda) (p : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : keyFun Gc κ p ≤ 1 :=
  mean_le_const _ _ 1 fun _ _ => indicator_le_one _

/-- The leaf hit as sliced data: the functional recording the hidden leaf's
key, at the expansion's tree. -/
theorem leafHit_eq_slicedView (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda)) :
    leafHit S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S) (contT Gc) newT h e
        (root, g) =
      slicedView S publicKey message salt root digest wsign world
        (keyFun Gc (S.signer.layout.key (node (treeExpand S.signer.layout g S.signer.variant salt) root (leafAddress e (h e)))))
        h (baseTree S.signer salt g root) g := by
  unfold leafHit viewAll ownView Spec.SharedScheme.runProgram slicedView phaseView phaseRun baseTree
  simp only
  rw [commitRun_eq, commitRest_run, PMF.bind_map]
  simp only [mean_bind, mean_map]
  refine mean_congr_support _ _ _ fun o ho => ?_
  obtain ⟨c, hc⟩ := runFixed_bounded_done g _ _ (commitPhase_bounded S.signer salt _) _ _ _ _ o ho
  rw [continueRun_done g _ _ o c hc, runFixed_history_shift]
  simp only [mean_map, appendHistory, viewOf, hc, commitsOf]
  unfold tailData
  rw [commitTail_family S.signer salt wsign trivialFamily g]
  refine mean_congr_support _ _ _ fun b hb => ?_
  have hb0 : b.cipherHistory = [] := commitTail_history S.signer salt wsign trivialFamily _ _ _ _ _ _ _ b hb
  simp only [hb0, List.nil_append, Function.comp_apply, postT, mean_map]
  refine congrArg _ (funext fun q => ?_)
  simp only [hiddenT, contT, newT, keyFun, stripFamily, pruneShared, tupleKeys, resampleW, resample, mean_map, mean_bind]

/-- The mixing family of the leaf hit: the functional recording the key of
the replaced block, at the tree with the tuple's leaves replaced. -/
def leafFct (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau) (x : Fin tau → Bits lambda) (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  slicedView S publicKey message salt root digest wsign world (keyFun Gc (S.signer.layout.key (S.signer.layout.output (x e)))) h
    (treeWith S h (baseTree S.signer salt g root) x) g

theorem leafFct_blocks (hL2 : 2 ≤ tau * 2 ^ kappa) (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda)) :
    leafFct S publicKey message salt root digest wsign world Gc h e (blocks S.signer salt root h g) g =
      leafHit S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S) (contT Gc) newT h e
        (root, g) := by
  rw [leafHit_eq_slicedView]
  unfold leafFct
  have hleaf := leaf_bounds h e
  have hκ : S.signer.layout.output (blocks S.signer salt root h g e) =
      node (treeExpand S.signer.layout g S.signer.variant salt) root (leafAddress e (h e)) := by
    unfold blocks leaf
    exact (node_eq_output_nodeBlock S.signer.layout g S.signer.variant salt root _ (by show 1 < leaf h e; omega)).symm
  rw [hκ, ← slicedView_blocks S publicKey message salt root digest wsign world _ h hL2 g]

theorem leafFct_le_one (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau) (x : Fin tau → Bits lambda) (g : Family (Bits lambda) (Bits lambda)) :
    leafFct S publicKey message salt root digest wsign world Gc h e x g ≤ 1 :=
  slicedView_le_one S publicKey message salt root digest wsign world _ h (keyFun_le_one Gc _) _ g

theorem leafFct_inv (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hL2 : 2 ≤ tau * 2 ^ kappa) (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau) (x : Fin tau → Bits lambda) (e' : Fin tau)
    (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hd : Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory)
    (hbad : ¬ Bad S.signer.layout (tau * 2 ^ kappa) S.signer.variant salt root (leaf h e')
      (node (treeExpand S.signer.layout g S.signer.variant salt) root (leaf h e' / 2)) world.other.cipherHistory v' g) :
    leafFct S publicKey message salt root digest wsign world Gc h e x
        (exchanged S.signer.layout g S.signer.variant salt root (leaf h e') v') =
      leafFct S publicKey message salt root digest wsign world Gc h e x g :=
  slicedView_exchanged S publicKey message salt root digest wsign world _ h hin hl hL hL2 x e' g hd v' hbad

theorem leafFct_eq_zero_of_not_mem (h : Fin tau → Fin (2 ^ kappa)) (hh : h ∉ tuples S digest) (e : Fin tau) (x : Fin tau → Bits lambda)
    (g : Family (Bits lambda) (Bits lambda)) :
    leafFct S publicKey message salt root digest wsign world Gc h e x g = 0 :=
  slicedView_eq_zero_of_not_mem S publicKey message salt root digest wsign world _ h hh _ g

/-- The leaf hiding: a named data-level hypothesis. With the tuple's leaves
replaced by a block tuple, the continuation's probability of recording the
key of the replaced block at an execution, summed over the block tuples, is
at most the number of block tuples times the slack, on the distinct
trees. -/
def LeafHide (B : Nat) (δ : ℝ≥0∞) : Prop :=
  ∀ (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
    InvC (tau := tau) (kappa := kappa) B world → ∀ (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda)
    (Gc : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF (Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))))
    (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda)),
    Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory →
    (∑ x : Fin tau → Bits lambda, leafFct S publicKey message salt root digest wsign world Gc h e x g) ≤
      (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * δ

/-- The leaf-term slack from the leaf hiding: twice the number of executions
times the blocks' power over the scaling's power times the hiding slack. -/
def εLeafOf (c B : Nat) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  2 * (tau : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) /
    ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau) * δ

variable (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c) (B : Nat)
  (hNb : c * (commitBudget tau kappa * B + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))

include hL2 hin hl hL hfiber hNb in
/-- The leaf term from the leaf hiding. -/
theorem leafTerm_le (hw : InvC (tau := tau) (kappa := kappa) B world) (δ : ℝ≥0∞) (hhide : LeafHide S publicKey B δ) :
    leafTerm S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S) (contT Gc) newT ≤
      εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c B δ := by
  have hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g world.other.cipherHistory := ⟨_, hw.2.1⟩
  have hlen : world.other.cipherHistory.length ≤ commitBudget tau kappa * B := hw.2.2
  have hcard : (keysOf world.other.cipherHistory).card ≤ commitBudget tau kappa * B := (card_keysOf_le _).trans hlen
  set Nn : ℕ := Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) with hNn
  have hsc : scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B ≤ Nn := by
    unfold scaleAt
    exact Nat.sub_le_sub_left (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _) _
  have hsc0 : 0 < scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B := by
    unfold scaleAt; omega
  have hNn0 : (Nn : ℝ≥0∞) ^ tau ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hNntop : (Nn : ℝ≥0∞) ^ tau ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  set K : ℝ≥0∞ := ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) /
    ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau * δ with hK
  -- the per-tuple, per-execution bound at a fixed root
  have hterm : ∀ (root : Bits lambda) (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau),
      mean (posterior world.other.cipherHistory) (fun g => indicator (decide (GoodTree S.signer salt world.other (root, g))) *
        leafHit S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S) (contT Gc) newT h e
          (root, g)) ≤ K := by
    intro root h e
    have hdI : ∀ g, indicator (decide (GoodTree S.signer salt world.other (root, g))) = distInd S.signer salt world.other root g :=
      fun g => rfl
    simp only [hdI, ← leafFct_blocks S publicKey message salt root digest wsign world Gc hL2 h e]
    have hup := mixture_upper S.signer salt world.other root h hL2 hin hl hL hpos c hfiber
      (leafFct S publicKey message salt root digest wsign world Gc h e)
      (fun x g => leafFct_le_one S publicKey message salt root digest wsign world Gc h e x g)
      (fun x e' v' g hd hbad => leafFct_inv S publicKey message salt root digest wsign world Gc hin hl hL hL2 h e x e' v' g hd hbad)
    have hsum : (∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory) (fun g =>
        distInd S.signer salt world.other root g * leafFct S publicKey message salt root digest wsign world Gc h e x g)) ≤
        (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * δ := by
      rw [sum_mean_mul (posterior world.other.cipherHistory) (distInd S.signer salt world.other root)
        (fun x g => leafFct S publicKey message salt root digest wsign world Gc h e x g) Finset.univ]
      refine (mean_le_const _ _ _ fun g _ => ?_)
      by_cases hd : Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory
      · simp only [distInd, hd, decide_true, RandomOracleTrap.indicator_true, one_mul]
        exact hhide wsign message world hw salt root digest Gc h e g hd
      · simp only [distInd, hd, decide_false, RandomOracleTrap.indicator_false, zero_mul, zero_le]
    have hdiv : mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
        leafFct S publicKey message salt root digest wsign world Gc h e (blocks S.signer salt root h g) g) ≤
        (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * δ / (Nn : ℝ≥0∞) ^ tau := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hNn0) (Or.inl hNntop), mul_comm]
      exact hup.trans hsum
    refine hdiv.trans ?_
    rw [hK, card_tuples_eq, ENNReal.mul_div_right_comm]
    refine mul_le_mul' ?_ le_rfl
    exact ENNReal.div_le_div_left (pow_le_pow_left' (Nat.cast_le.mpr hsc) tau) _
  -- the leaf term over the two tuples and the executions
  unfold leafTerm
  simp only [mean_rootDraw]
  calc _ = mean (PMF.uniformOfFintype (Bits lambda)) fun root => ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau,
        mean (posterior world.other.cipherHistory) fun g => indicator (decide (GoodTree S.signer salt world.other (root, g))) *
          leafHit S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S) (contT Gc) newT
            h e (root, g) := by
        simp only [sum_mean]
    _ ≤ mean (PMF.uniformOfFintype (Bits lambda)) fun _ => ((tuples S digest).card : ℝ≥0∞) * ((tau : ℝ≥0∞) * K) := by
        refine mean_le_mean _ _ _ fun root _ => ?_
        rw [sum_tuples S digest _ (fun h hh => ?_)]
        · calc _ ≤ ∑ h ∈ tuples S digest, ∑ e : Fin tau, K :=
                Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun e _ => hterm root h e
            _ = _ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        · refine Finset.sum_eq_zero fun e _ => ?_
          have hdI : ∀ g, indicator (decide (GoodTree S.signer salt world.other (root, g))) = distInd S.signer salt world.other root g :=
            fun g => rfl
          simp only [hdI, ← leafFct_blocks S publicKey message salt root digest wsign world Gc hL2 h e,
            leafFct_eq_zero_of_not_mem S publicKey message salt root digest wsign world Gc h hh, mul_zero, mean_const]
    _ ≤ _ := by
        rw [mean_const]
        unfold εLeafOf
        rw [hK]
        calc ((tuples S digest).card : ℝ≥0∞) * ((tau : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) /
              ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau * δ))
            ≤ 2 * ((tau : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) /
              ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau * δ)) :=
              mul_le_mul' (by exact_mod_cast card_tuples_le S digest) le_rfl
          _ = _ := by ring

variable (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

omit message salt root digest wsign world Gc in
include hL2 hin hl hL hfiber hNb in
/-- The leaf-term bound for the run's continuations from the leaf hiding. -/
theorem leafR_of_leafHide (δ : ℝ≥0∞) (hhide : LeafHide S publicKey B δ) :
    LeafR S V verifyBudget publicKey sampleWitness adversary (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c B δ) B := by
  intro wsign witness message m world hw fuel' pk next trace Cp hfuel salt digest
  exact leafTerm_le S publicKey message salt digest wsign world _ hL2 hin hl hL c hfiber B hNb
    (invC_mono m B world (by omega) hw) δ hhide

omit message salt root digest wsign world Gc in
include hL2 hin hl hL hfiber hNb in
/-- The leaf-term bound for the cut's continuations from the leaf hiding. -/
theorem leafC_of_leafHide (δ : ℝ≥0∞) (hhide : LeafHide S publicKey B δ) :
    LeafC S V verifyBudget publicKey sampleWitness adversary (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) c B δ) B := by
  intro wsign witness message m world hw index fuel' pk next trace Cp hfuel salt digest
  exact leafTerm_le S publicKey message salt digest wsign world _ hL2 hin hl hL c hfiber B hNb
    (invC_mono m B world (by omega) hw) δ hhide

end
end SDitH.Proofs.LeafTermBound
