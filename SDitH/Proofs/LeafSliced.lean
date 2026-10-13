import SDitH.Proofs.OffHitAssembly
import SDitH.Proofs.TouchBound

/-! The sliced data without the hit factor, and the leaf hit as sliced
data. The leaf term's hit at an execution's hidden leaf is the sliced data
of the functional recording the leaf's key, at the expansion's tree; with
the tuple's leaves replaced it is the mixing family of that functional. -/

namespace SDitH.Proofs.LeafSliced

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
  (h : Fin tau → Fin (2 ^ kappa))

/-- The sliced data without the hit factor. -/
def slicedView (nodes : Nat → Spec.BAVC.Seed lambda) (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (phaseView S.signer salt g root (tupleKeys S salt root h g) world.other) fun o =>
    tailData S publicKey message salt digest wsign world Ψ h nodes (commitsOf o.state) o.hashTable o.hashHistory o.trace
      o.cipherHistory

theorem sliced_eq_view (nodes : Nat → Spec.BAVC.Seed lambda) (g : Family (Bits lambda) (Bits lambda)) :
    sliced S publicKey message salt root digest wsign world Ψ h nodes g =
      indicator (!touchesG (tupleKeys S salt root h g) world) * slicedView S publicKey message salt root digest wsign world Ψ h nodes g :=
  rfl

theorem slicedView_congr (n₁ n₂ : Nat → Spec.BAVC.Seed lambda) (hn : ∀ a, 0 < a → a < 2 * (tau * 2 ^ kappa) → n₁ a = n₂ a)
    (g : Family (Bits lambda) (Bits lambda)) :
    slicedView S publicKey message salt root digest wsign world Ψ h n₁ g =
      slicedView S publicKey message salt root digest wsign world Ψ h n₂ g := by
  unfold slicedView tailData
  simp only [commitTail_congr S.signer salt wsign n₁ n₂ hn]

theorem slicedView_blocks (hL2 : 2 ≤ tau * 2 ^ kappa) (g : Family (Bits lambda) (Bits lambda)) :
    slicedView S publicKey message salt root digest wsign world Ψ h (baseTree S.signer salt g root) g =
      slicedView S publicKey message salt root digest wsign world Ψ h
        (treeWith S h (baseTree S.signer salt g root) (blocks S.signer salt root h g)) g :=
  slicedView_congr S publicKey message salt root digest wsign world Ψ h _ _
    (fun a ha0 haL => (treeWith_blocks S salt root h hL2 g a ha0 haL).symm) g

theorem slicedView_le_one (hΨ : ∀ x, Ψ x ≤ 1) (nodes : Nat → Spec.BAVC.Seed lambda) (g : Family (Bits lambda) (Bits lambda)) :
    slicedView S publicKey message salt root digest wsign world Ψ h nodes g ≤ 1 := by
  unfold slicedView
  refine mean_le_const _ _ 1 fun o _ => ?_
  unfold tailData
  refine mean_le_const _ _ 1 fun out' _ => mean_le_const _ _ 1 fun q _ => ?_
  calc _ ≤ 1 * 1 := mul_le_mul' (indicator_le_one _) (mean_le_const _ _ 1 fun w'' _ => hΨ _)
    _ = 1 := mul_one _

theorem slicedView_eq_zero_of_not_mem (hh : h ∉ tuples S digest) (nodes : Nat → Spec.BAVC.Seed lambda)
    (g : Family (Bits lambda) (Bits lambda)) :
    slicedView S publicKey message salt root digest wsign world Ψ h nodes g = 0 := by
  have hne : ∀ q : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Spec.BAVC.Digest lambda)),
      sigHidden S q.1 = hiddenOfDigest S digest ∨ sigHidden S q.1 = defaultTuple → sigHidden S q.1 ≠ h := by
    intro q hq heq
    apply hh
    unfold tuples
    rcases hq with h1 | h1
    · rw [← heq, h1]; exact Finset.mem_insert_self _ _
    · rw [← heq, h1]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  unfold slicedView tailData
  refine (mean_le_const _ _ 0 fun o _ => mean_le_const _ _ 0 fun out' _ =>
    mean_le_const _ _ 0 fun q hq => ?_).antisymm (zero_le _)
  have h0 := hne q (sigHidden_simPost S publicKey message salt digest out'.state world.hashTable q hq)
  simp [h0, indicator]

variable (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (hL2 : 2 ≤ tau * 2 ^ kappa)

include hin hl hL hL2 in
/-- The sliced data without the hit factor, with the tuple's leaves replaced,
is unchanged by the exchange at one of the tuple's leaves. -/
theorem slicedView_exchanged (x : Fin tau → Bits lambda) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda))
    (hd : Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory) (v' : Bits lambda)
    (hbad : ¬ Bad S.signer.layout (tau * 2 ^ kappa) S.signer.variant salt root (leaf h e)
      (node (treeExpand S.signer.layout g S.signer.variant salt) root (leaf h e / 2)) world.other.cipherHistory v' g) :
    slicedView S publicKey message salt root digest wsign world Ψ h
        (treeWith S h (baseTree S.signer salt (exchanged S.signer.layout g S.signer.variant salt root (leaf h e) v') root) x)
        (exchanged S.signer.layout g S.signer.variant salt root (leaf h e) v') =
      slicedView S publicKey message salt root digest wsign world Ψ h (treeWith S h (baseTree S.signer salt g root) x) g := by
  have hleaf := leaf_bounds h e
  have hb : 1 < leaf h e := by omega
  obtain ⟨hp, hp', G1, G2, G3, G4⟩ :=
    conditions_of_distinct S.signer.layout (tau * 2 ^ kappa) g S.signer.variant salt root world.other.cipherHistory hd (leaf h e) hb
      hleaf.2 v' hbad
  have hb' : node (treeExpand S.signer.layout g S.signer.variant salt) root (leaf h e) =
      S.signer.layout.output (nodeBlock S.signer.layout g S.signer.variant salt root (leaf h e)) :=
    node_eq_output_nodeBlock S.signer.layout g S.signer.variant salt root (leaf h e) hb
  have hκ : ∀ en ∈ world.other.cipherHistory,
      en.key ≠ S.signer.layout.key (S.signer.layout.output (nodeBlock S.signer.layout g S.signer.variant salt root (leaf h e))) :=
    fun en hen heq => hd.1 (leaf h e) (by omega) hleaf.2 (by rw [hb']; exact mem_keysOf.mpr ⟨en, hen, heq⟩)
  have hκ' : ∀ en ∈ world.other.cipherHistory, en.key ≠ S.signer.layout.key (S.signer.layout.output v') := by
    intro en hen heq
    simp only [Bad, not_or] at hbad
    exact hbad.1 (by rw [← heq]; exact mem_keysOf.mpr ⟨en, hen, rfl⟩)
  have hpath : leaf h e ∈ pathAddresses (leafAddress e (h e)) :=
    mem_pathAddresses_iff.mpr ⟨hb, 0, by simp [leaf]⟩
  have htree : ∀ a, 0 < a → a < 2 * (tau * 2 ^ kappa) →
      treeWith S h (baseTree S.signer salt (exchanged S.signer.layout g S.signer.variant salt root (leaf h e) v') root) x a =
        treeWith S h (baseTree S.signer salt g root) x a := by
    intro a ha0 haL
    by_cases hex : ∃ e', leaf h e' = a
    · obtain ⟨e', rfl⟩ := hex
      rw [treeWith_leaf, treeWith_leaf]
    · rw [treeWith_other S h _ _ a fun e' he' => hex ⟨e', he'⟩, treeWith_other S h _ _ a fun e' he' => hex ⟨e', he'⟩]
      have hpos : 0 < tau * 2 ^ kappa := by omega
      unfold baseTree
      rw [run_exchanged S.signer.layout hin hl (tau * 2 ^ kappa) hL g S.signer.variant salt root (fun _ => root) (leaf h e) hb
        hleaf.2 v' hp hp' G1 G2 G3 G4 (tau * 2 ^ kappa - 1) (by omega) a ha0 (by omega), if_neg (fun hab => hex ⟨e, hab.symm⟩)]
  rw [slicedView_congr S publicKey message salt root digest wsign world Ψ h _ _ htree]
  unfold slicedView
  have hview := phaseView_exchanged_all S.signer salt { world.other with family := g } root (leaf h e) hb hleaf.2 v' hin hl hL hp hp'
    G1 G2 G3 G4 hκ hκ' h e hpath
  simp only at hview
  rw [phaseView_setFamily, phaseView_setFamily] at hview
  unfold tupleKeys
  rw [hview]
  rfl

end
end SDitH.Proofs.LeafSliced
