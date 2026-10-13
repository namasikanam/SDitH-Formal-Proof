import SDitH.Proofs.SwapCloseSplit

/-! The bad term for the pre-call hit. A key of the signature's hidden
path is the key of a tree node below twice the leaf count, so a pre-call
hit is a failure of the tree's keys to be fresh and distinct; the
distinctness failure probability under the joint draw of the root and
the posterior family (`bad_tree_le`) then bounds the hit term, uniformly
in the recorded history's length through the counted invariant. The
bound is the first part of the uniform touching bound. -/

namespace SDitH.Proofs.HitTerm

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

open SwapClose SwapCloseSplit TouchTotal TouchAssembly RootPosteriorBound TreeDistinct TreeStepFresh HiddenKeys HiddenTuple
open HiddenEntries HiddenLeafNode SharedPrune ForkRestore SDitH.Proofs.SeedTree
open Spec.SeedTree (leafAddress leafOffset node)
open ForkOutcome (runProgram_family)
open Spec.IdealCipher (Family Matches)

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (publicKey : List Bool)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The hit bound: the root's key among the recorded keys, plus the
distinctness failure of the tree's keys. -/
def εHit (c cKey M : Nat) : ℝ≥0∞ :=
  ((cKey * M : Nat) : ℝ≥0∞) * (Fintype.card (Bits lambda) : ℝ≥0∞)⁻¹ +
    (tau * 2 ^ kappa - 1 : ℕ) *
      (2 * (((c * (M + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) /
          ((Fintype.card (Bits lambda) - (M + 2 * (tau * 2 ^ kappa - 1) + 1) : Nat) : ℝ≥0∞)) +
        (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - (M + 2 * (tau * 2 ^ kappa - 1) + 1) : Nat) : ℝ≥0∞))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The hit bound is the first part of the uniform touching bound. -/
theorem εHit_le_εTouch (c cKey M B' : Nat) (εLeaf : ℝ≥0∞) :
    εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey M ≤
      εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey M B' εLeaf :=
  le_self_add

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A key of the hidden path is the key of a tree node below twice the
leaf count. -/
theorem hidden_path_node (hL1 : 1 ≤ tau * 2 ^ kappa) (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (g : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root : Bits lambda)
    (hidden : Fin tau → Fin (2 ^ kappa)) (κ : Bits lambda) (hκ : κ ∈ hiddenKeysAll layout g variant salt root hidden) :
    ∃ b, 1 ≤ b ∧ b < 2 * (tau * 2 ^ kappa) ∧ layout.key (node (treeExpand layout g variant salt) root b) = κ := by
  obtain ⟨e, he⟩ := (mem_hiddenKeysAll layout g variant salt root hidden κ).mp hκ
  obtain ⟨b, hb, rfl⟩ := (mem_hiddenKeys layout g variant salt root _ κ).mp he
  refine ⟨b, ?_, ?_, rfl⟩
  · rcases hb with rfl | hb
    · exact le_rfl
    · exact (lt_of_mem_pathAddresses hb).le
  · rcases hb with rfl | hb
    · omega
    · obtain ⟨-, k, hk⟩ := mem_pathAddresses_iff.mp hb
      rw [← hk]
      have hlt := leafOffset_lt e (hidden e)
      calc leafAddress e (hidden e) / 2 ^ k ≤ leafAddress e (hidden e) := Nat.div_le_self _ _
        _ < 2 * (tau * 2 ^ kappa) := by unfold leafAddress; omega

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A pre-call hit is a distinctness failure of the tree at the output's
family. -/
theorem not_goodTree_of_hitPre (hL1 : 1 ≤ tau * 2 ^ kappa) (salt root : Bits lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (r : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (h : hitPre S salt root world r = true) :
    ¬ GoodTree S.signer salt world.other (root, r.2.other.family) := by
  intro hg
  unfold hitPre touchesG touchesW at h
  obtain ⟨e, he, hk⟩ := of_decide_eq_true h
  obtain ⟨b, hb1, hb2, hbk⟩ := hidden_path_node hL1 S.signer.layout r.2.other.family S.signer.variant salt root (sigHidden S r.1)
    e.key hk
  exact hg.1 b hb1 hb2 (by rw [hbk]; exact mem_keysOf.mpr ⟨e, he, rfl⟩)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The hit indicator is at most the distinctness failure indicator. -/
theorem indicator_hitPre_le (hL1 : 1 ≤ tau * 2 ^ kappa) (salt root : Bits lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (r : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    indicator (hitPre S salt root world r) ≤
      indicator (decide (¬ GoodTree S.signer salt world.other (root, r.2.other.family))) := by
  cases hh : hitPre S salt root world r
  · simp [indicator]
  · have := not_goodTree_of_hitPre S hL1 salt root world r hh
    simp [indicator, this]

/-- The signing call keeps the family. -/
theorem commitOracle_family (salt root : Bits lambda) (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (digest : Spec.BAVC.Digest lambda) (w' : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (r : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (hr : r ∈ (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w').support) :
    r.2.other.family = w'.other.family := by
  simp only [commitOracle, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hr
  obtain ⟨p, hp, q, -, rfl⟩ := hr
  exact runProgram_family _ _ _ p hp

/-- The bad term for the pre-call hit at the counted invariant's budget. -/
theorem badTerm_hitPre (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey) (B : Nat) :
    BadTerm S publicKey (hitPre S) B (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * B)) := by
  intro wsign message world hw
  have hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g world.other.cipherHistory := ⟨_, hw.2.1⟩
  have hlen : world.other.cipherHistory.length ≤ commitBudget tau kappa * B := hw.2.2
  have hcard : (keysOf world.other.cipherHistory).card ≤ commitBudget tau kappa * B := (card_keysOf_le _).trans hlen
  refine mean_le_const _ _ _ fun salt _ => ?_
  rw [mean_comm]
  refine mean_le_const _ _ _ fun digest _ => ?_
  calc (mean (PMF.uniformOfFintype (Bits lambda)) fun root => mean (resampleW resample world) fun w' =>
          mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w') fun r =>
            indicator (hitPre S salt root world r))
      ≤ mean (PMF.uniformOfFintype (Bits lambda)) fun root => mean (resampleW resample world) fun w' =>
          indicator (decide (¬ GoodTree S.signer salt world.other (root, w'.other.family))) := by
        refine mean_le_mean _ _ _ fun root _ => mean_le_mean _ _ _ fun w' _ => mean_le_const _ _ _ fun r hr => ?_
        rw [← commitOracle_family S publicKey salt root wsign message digest w' r hr]
        exact indicator_hitPre_le S (by omega) salt root world r
    _ = mean (rootDraw world.other.cipherHistory) fun x => indicator (decide (¬ GoodTree S.signer salt world.other x)) := by
        rw [mean_rootDraw]
        refine congrArg _ (funext fun root => ?_)
        unfold resampleW resample
        simp only [mean_map]
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

end
end SDitH.Proofs.HitTerm
