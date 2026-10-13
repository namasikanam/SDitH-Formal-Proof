import SDitH.Proofs.InputPresentBound
import SDitH.Proofs.NewMentionPrefix
import SDitH.Proofs.PrefixMentionBound

/-! The input-present bound with the relative mention term. The mention
term relative to the world's own trace replaces the cumulative one, and
its bound is the sum of the per-query mention steps alone, so the
input-present bound reads: the relative mention term (at most the steps
over the prefix budget from the trace's length) plus the row-stored term
plus the support count over the digest count. -/

namespace SDitH.Proofs.InputPresentUniform

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner Spec.HashCipherTrace
open Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain Spec.BAVCChainInputs
open Spec.RandomOracleTrap (indicator)
open Spec.SlopeConsistencyGame (Out)
open Spec.PIOPArithmetic (selectorCount)
open SignStep SignCompare CommitDecomposition RunBind CommitSplitRun PrefixLinesFresh PrefixHeadSplit HeadLastSplit
open HeadLastRun PrefixOrMention PrefixFromHead CommitLinesEvent CommitLinesEvents TailLinesDigest TableSupport
open InputPresentTail SharedGameInvariant OuterFresh InputPresentBound NewMention NewMentionChain NewMentionPrefix
open PrefixMentionBound
open scoped Classical ENNReal

noncomputable section


variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The prefix's relative mention term of a world: over a uniform salt and
root, the mention event relative to the world's trace on the witness-free
prefix run. -/
def mentionTermN
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : PMF Bool :=
  (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
    (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
      (runFixed procedure world.other.family (prefixBudget tau kappa) (commitPrefix S.signer salt root) world.other.hashTable
        world.other.hashHistory world.other.cipherHistory world.other.trace).map fun mid =>
          newBad (digestMention (mentions lambda tau)) world.other.trace mid.trace

/-- The input-present bound with the relative mention term. -/
theorem inputPresent_leN (hl : 0 < lambda) (htau : tau ≠ 0) (publicKey : List Bool)
    (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (hw : WellFormed world.other) {n : Nat} (hn : Supported world.hashTable n) :
    (inputPresent S publicKey witness message world) true ≤
      (mentionTermN S world) true + (rowTerm S htau world) true + (n : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ := by
  unfold inputPresent mentionTermN rowTerm
  rw [prepareSigning_eq]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  refine bind_true_le_two_add _ _ _ _ _ (fun salt _ => ?_)
  refine bind_true_le_two_add _ _ _ _ _ (fun root _ => ?_)
  unfold runProgram
  simp only [PMF.map_comp, Function.comp_def]
  have hsplit : runFixed procedure world.other.family (commitBudget tau kappa) (commitProgram S.signer salt root witness)
      world.other.hashTable world.other.hashHistory world.other.cipherHistory world.other.trace =
        (runFixed procedure world.other.family (headBudget tau kappa - 1) (headInit S.signer salt root) world.other.hashTable
          world.other.hashHistory world.other.cipherHistory world.other.trace).bind fun mid0 =>
          (((continueRun world.other.family 1 (lastRow htau) mid0).bind
            (continueRun world.other.family 3 (prefixTail S.signer salt))).bind
            (continueRun world.other.family 1 (commitTail S.signer salt witness))) := by
    rw [runFixed_commit_split S.signer salt root witness world.other.family world.other.hashTable world.other.hashHistory
      world.other.cipherHistory world.other.trace,
      runFixed_prefix_split S.signer salt root world.other.family world.other.hashTable world.other.hashHistory
      world.other.cipherHistory world.other.trace,
      runFixed_head_split htau S.signer salt root world.other.family world.other.hashTable world.other.hashHistory
      world.other.cipherHistory world.other.trace, PMF.bind_bind, PMF.bind_bind]
    congr 1
    funext mid0
    rw [PMF.bind_bind]
  have hprefix : runFixed procedure world.other.family (prefixBudget tau kappa) (commitPrefix S.signer salt root)
      world.other.hashTable world.other.hashHistory world.other.cipherHistory world.other.trace =
        (runFixed procedure world.other.family (headBudget tau kappa - 1) (headInit S.signer salt root) world.other.hashTable
          world.other.hashHistory world.other.cipherHistory world.other.trace).bind fun mid0 =>
          (continueRun world.other.family 1 (lastRow htau) mid0).bind (continueRun world.other.family 3 (prefixTail S.signer salt)) := by
    rw [runFixed_prefix_split S.signer salt root world.other.family world.other.hashTable world.other.hashHistory
      world.other.cipherHistory world.other.trace,
      runFixed_head_split htau S.signer salt root world.other.family world.other.hashTable world.other.hashHistory
      world.other.cipherHistory world.other.trace, PMF.bind_bind]
  rw [hsplit, hprefix, PMF.map_bind, PMF.map_bind]
  have hc := bind_le_bind_add_cost
    (runFixed procedure world.other.family (headBudget tau kappa - 1) (headInit S.signer salt root) world.other.hashTable
      world.other.hashHistory world.other.cipherHistory world.other.trace)
    (fun mid0 => (((continueRun world.other.family 1 (lastRow htau) mid0).bind
        (continueRun world.other.family 3 (prefixTail S.signer salt))).bind
        (continueRun world.other.family 1 (commitTail S.signer salt witness))).map fun out =>
          decide (world.hashTable ⟨publicKey, message, (preparedOf S salt (out.state,
            ⟨world.other.family, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩)).1⟩ ≠ none))
    (fun _ => PMF.pure false)
    (fun mid0 => (((continueRun world.other.family 1 (lastRow htau) mid0).bind
        (continueRun world.other.family 3 (prefixTail S.signer salt))).map fun mid =>
          newBad (digestMention (mentions lambda tau)) world.other.trace mid.trace) true +
      indicator (rowStored htau mid0) + (n : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹) true
    (fun mid0 hmid0 => by
      dsimp only
      cases hrs : rowStored htau mid0 with
      | true =>
        rw [RandomOracleTrap.indicator_true]
        exact (PMF.coe_le_one _ _).trans (le_add_left (le_add_right (le_add_left le_rfl)))
      | false =>
        obtain ⟨data, hdata⟩ := runFixed_bounded_done world.other.family _ _ (headInit_bounded htau S.signer salt root)
          world.other.hashTable world.other.hashHistory world.other.cipherHistory world.other.trace mid0 hmid0
        have hq : mid0.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) = none := by
          by_contra hne
          have hdec : rowStored htau mid0 = true := decide_eq_true ⟨data, hdata, hne⟩
          rw [hrs] at hdec
          exact Bool.false_ne_true hdec
        obtain ⟨htr0, hord0, hfresh0, hext0, hstored0, _⟩ := HashCipherTrace.run_invariants procedure world.other.family
          _ _ world.other.hashTable world.other.hashHistory world.other.cipherHistory world.other.trace mid0 hmid0 hw.1
          hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2
        rw [RandomOracleTrap.indicator_false, add_zero, PMF.map_bind]
        have hL : world.other.trace.length ≤ mid0.trace.length :=
          runFixed_length_le procedure world.other.family _ _ world.other.hashTable world.other.hashHistory
            world.other.cipherHistory world.other.trace mid0 hmid0
        refine (bind_true_le_event_add _ _ (fun mid => newBad (digestMention (mentions lambda tau)) world.other.trace mid.trace)
          _ (fun mid hmid hbad => ?_)).trans (le_add_left le_rfl)
        rcases prefix_or_mention_fromN hl htau S.signer salt world.other.family world.other.trace mid0 hL htr0 hord0 hfresh0
            hext0 hstored0 data hdata hq mid hmid with h | ⟨head, o, a, m, hstate, hlines⟩
        · simp [h] at hbad
        · have hfr : mid.hashTable (linesInput S.signer salt witness (head.1, head.2.1, head.2.2, o, a, m)) = none := by
            cases hc : mid.hashTable (linesInput S.signer salt witness (head.1, head.2.1, head.2.2, o, a, m)) with
            | none => rfl
            | some d =>
              have := hlines _ d hc
              simp [this] at hbad
          exact tail_present_le S publicKey message salt witness world.hashTable hn world.other.family mid _ hstate hfr _)
  rw [PMF.bind_const] at hc
  simp only [PMF.pure_apply, Bool.true_eq_false, if_false, zero_add] at hc
  refine hc.trans (le_of_eq ?_)
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, PMF.bind_apply,
    RandomOracleTrap.map_true_eq]

/-- The relative mention term's bound: the per-query steps over the prefix
budget from the trace's length. -/
theorem mentionTermN_le
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    (mentionTermN S world) true ≤
      ∑ i ∈ Finset.range (prefixBudget tau kappa), mentionStep lambda tau (world.other.trace.length + i) := by
  unfold mentionTermN
  refine ChallengeMixtures.bind_true_le _ _ _ (fun salt _ => ?_)
  refine ChallengeMixtures.bind_true_le _ _ _ (fun root _ => ?_)
  exact run_prefix_boundN procedure world.other.family (digestMention (mentions lambda tau)) (mentionStep lambda tau)
    (fun log input => ProductOracle.digest_mention_query_bound (mentions lambda tau) (tau + 2)
      (fun input => SDitH.Proofs.BAVCChainInputs.mentions_card_le input) log input)
    (prefixBudget tau kappa) (commitPrefix S.signer salt root) world.other.hashTable world.other.hashHistory
    world.other.cipherHistory world.other.trace

end
end SDitH.Proofs.InputPresentUniform
