import SDitH.Proofs.SigningData
import SDitH.Proofs.LeafMixture

/-! The sliced data under the exchange of a hidden leaf's value. With the
tuple's leaves replaced by given blocks, the sliced data at a family is
unchanged by the exchange at one of the tuple's leaves on the distinct
trees with a target that is not bad: the phase view pruned at the tuple's
keys is unchanged, the hit factor reads the pre-call history at keys
other than the two exchanged leaf keys, and the tree with the leaves
replaced agrees on the allocated addresses. At the family's own blocks the
replaced tree is the expansion's tree. -/

namespace SDitH.Proofs.SlicedInvariance

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

/-- A tree with the tuple's leaves replaced by given blocks' outputs. -/
def treeWith (t : Nat → Spec.BAVC.Seed lambda) (x : Fin tau → Bits lambda) : Nat → Spec.BAVC.Seed lambda := fun c =>
  if hex : ∃ e, leaf h e = c then S.signer.layout.output (x (Classical.choose hex)) else t c

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem treeWith_leaf (t : Nat → Spec.BAVC.Seed lambda) (x : Fin tau → Bits lambda) (e : Fin tau) :
    treeWith S h t x (leaf h e) = S.signer.layout.output (x e) := by
  unfold treeWith
  have hex : ∃ e', leaf h e' = leaf h e := ⟨e, rfl⟩
  rw [dif_pos hex]
  have hc : Classical.choose hex = e := by
    by_contra hne
    exact leaf_ne h _ _ hne (Classical.choose_spec hex)
  rw [hc]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem treeWith_other (t : Nat → Spec.BAVC.Seed lambda) (x : Fin tau → Bits lambda) (c : Nat) (hc : ∀ e, leaf h e ≠ c) :
    treeWith S h t x c = t c := by
  unfold treeWith
  rw [dif_neg (fun ⟨e, he⟩ => hc e he)]

/-- The sliced data depends on the tree only within the allocated
addresses. -/
theorem sliced_congr (n₁ n₂ : Nat → Spec.BAVC.Seed lambda) (hn : ∀ a, 0 < a → a < 2 * (tau * 2 ^ kappa) → n₁ a = n₂ a)
    (g : Family (Bits lambda) (Bits lambda)) :
    sliced S publicKey message salt root digest wsign world Ψ h n₁ g = sliced S publicKey message salt root digest wsign world Ψ h n₂ g := by
  unfold sliced tailData
  simp only [commitTail_congr S.signer salt wsign n₁ n₂ hn]

omit [Field F] [Algebra (ZMod 2) F] [DecidableEq F] in
/-- At the family's own blocks the replaced tree is the expansion's tree
within the allocated addresses. -/
theorem treeWith_blocks (hL2 : 2 ≤ tau * 2 ^ kappa) (g : Family (Bits lambda) (Bits lambda)) (a : Nat) (ha0 : 0 < a)
    (haL : a < 2 * (tau * 2 ^ kappa)) :
    treeWith S h (baseTree S.signer salt g root) (blocks S.signer salt root h g) a = baseTree S.signer salt g root a := by
  by_cases hex : ∃ e, leaf h e = a
  · obtain ⟨e, rfl⟩ := hex
    rw [treeWith_leaf]
    unfold blocks
    have hleaf := leaf_bounds h e
    show S.signer.layout.output (nodeBlock S.signer.layout g S.signer.variant salt root (leaf h e)) = _
    rw [← node_eq_output_nodeBlock S.signer.layout g S.signer.variant salt root (leaf h e) (by omega)]
    unfold leaf
    exact (baseTree_leaf S.signer salt g root e (h e)).symm
  · exact treeWith_other S h _ _ a fun e he => hex ⟨e, he⟩

/-- The sliced data at the expansion's tree is the sliced data at the
replaced tree at the own blocks. -/
theorem sliced_blocks (hL2 : 2 ≤ tau * 2 ^ kappa) (g : Family (Bits lambda) (Bits lambda)) :
    sliced S publicKey message salt root digest wsign world Ψ h (baseTree S.signer salt g root) g =
      sliced S publicKey message salt root digest wsign world Ψ h
        (treeWith S h (baseTree S.signer salt g root) (blocks S.signer salt root h g)) g :=
  sliced_congr S publicKey message salt root digest wsign world Ψ h _ _
    (fun a ha0 haL => (treeWith_blocks S salt root h hL2 g a ha0 haL).symm) g

variable (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (hL2 : 2 ≤ tau * 2 ^ kappa)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
include hin hl hL hL2 in
/-- The hit factor is unchanged by the exchange at a tuple's leaf. -/
theorem touches_tupleKeys_exchanged (e : Fin tau) (g : Family (Bits lambda) (Bits lambda))
    (hd : Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory) (v' : Bits lambda)
    (hbad : ¬ Bad S.signer.layout (tau * 2 ^ kappa) S.signer.variant salt root (leaf h e)
      (node (treeExpand S.signer.layout g S.signer.variant salt) root (leaf h e / 2)) world.other.cipherHistory v' g) :
    touchesG (tupleKeys S salt root h (exchanged S.signer.layout g S.signer.variant salt root (leaf h e) v')) world =
      touchesG (tupleKeys S salt root h g) world := by
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
  have hmem := mem_hiddenKeysAll_exchanged S.signer.layout g S.signer.variant salt root h hin hl hL (leaf h e) hb hleaf.2 v' hp hp'
    G1 G2 G3 G4 e hpath
  unfold touchesG touchesW tupleKeys
  congr 1
  refine propext ⟨fun ⟨en, hen, hk⟩ => ⟨en, hen, ?_⟩, fun ⟨en, hen, hk⟩ => ⟨en, hen, ?_⟩⟩
  · have := (hmem en.key).mp (List.mem_cons_of_mem _ hk)
    simp only [List.mem_cons] at this
    exact this.resolve_left (hκ' en hen)
  · have := (hmem en.key).mpr (List.mem_cons_of_mem _ hk)
    simp only [List.mem_cons] at this
    exact this.resolve_left (hκ en hen)

include hin hl hL hL2 in
/-- The sliced data with the tuple's leaves replaced is unchanged by the
exchange at one of the tuple's leaves, on the distinct trees with a
target that is not bad. -/
theorem sliced_exchanged (x : Fin tau → Bits lambda) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda))
    (hd : Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory) (v' : Bits lambda)
    (hbad : ¬ Bad S.signer.layout (tau * 2 ^ kappa) S.signer.variant salt root (leaf h e)
      (node (treeExpand S.signer.layout g S.signer.variant salt) root (leaf h e / 2)) world.other.cipherHistory v' g) :
    sliced S publicKey message salt root digest wsign world Ψ h
        (treeWith S h (baseTree S.signer salt (exchanged S.signer.layout g S.signer.variant salt root (leaf h e) v') root) x)
        (exchanged S.signer.layout g S.signer.variant salt root (leaf h e) v') =
      sliced S publicKey message salt root digest wsign world Ψ h (treeWith S h (baseTree S.signer salt g root) x) g := by
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
  -- the replaced trees agree on the allocated addresses
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
  rw [sliced_congr S publicKey message salt root digest wsign world Ψ h _ _ htree]
  -- the view and the hit factor
  unfold sliced
  rw [touches_tupleKeys_exchanged S salt root world h hin hl hL hL2 e g hd v' hbad]
  have hview := phaseView_exchanged_all S.signer salt { world.other with family := g } root (leaf h e) hb hleaf.2 v' hin hl hL hp hp'
    G1 G2 G3 G4 hκ hκ' h e hpath
  simp only at hview
  rw [phaseView_setFamily, phaseView_setFamily] at hview
  unfold tupleKeys
  rw [hview]
  rfl

end
end SDitH.Proofs.SlicedInvariance
