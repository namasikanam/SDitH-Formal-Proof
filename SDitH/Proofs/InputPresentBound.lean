import SDitH.Proofs.InputPresentTail
import SDitH.Proofs.SharedGameInvariant

/-! The input-present bound. At a world with a well-formed shared part and
a hash table supported by n inputs, the honest preparation's hash input
is already present with probability at most the prefix's mention term
plus the row-stored term plus n over the digest count: the commitment
run splits into the head's initial part, the rest of the prefix and the
tail; the rest either raises the mention event or finishes with the lines
input fresh, unless the last row query was stored; and at a fresh lines
input the tail stores the input with probability at most n over the
digest count. -/

namespace SDitH.Proofs.InputPresentBound

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner Spec.HashCipherTrace
open Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain Spec.BAVCChainInputs
open Spec.RandomOracleTrap (indicator)
open Spec.SlopeConsistencyGame (Out)
open Spec.PIOPArithmetic (selectorCount)
open SignStep SignCompare CommitDecomposition RunBind CommitSplitRun PrefixLinesFresh PrefixHeadSplit HeadLastSplit
open HeadLastRun PrefixOrMention PrefixFromHead CommitLinesEvent CommitLinesEvents TailLinesDigest TableSupport
open InputPresentTail SharedGameInvariant OuterFresh
open scoped Classical ENNReal

noncomputable section

section Generic

variable {A : Type*}

/-- A Boolean bind bounded pointwise by two bind-shaped events plus a
constant. -/
theorem bind_true_le_two_add (p : PMF A) (f g₁ g₂ : A → PMF Bool) (K : ℝ≥0∞)
    (h : ∀ a ∈ p.support, (f a) true ≤ (g₁ a) true + (g₂ a) true + K) :
    (p.bind f) true ≤ (p.bind g₁) true + (p.bind g₂) true + K := by
  have hc := bind_le_bind_add_cost p f (fun _ => PMF.pure false) (fun a => (g₁ a) true + (g₂ a) true + K) true
    (fun a ha => by
      dsimp only
      exact (h a ha).trans (le_add_left le_rfl))
  rw [PMF.bind_const] at hc
  simp only [PMF.pure_apply, Bool.true_eq_false, if_false, zero_add] at hc
  refine hc.trans (le_of_eq ?_)
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, PMF.bind_apply, PMF.bind_apply]

end Generic

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The prefix's mention term of a world: over a uniform salt and root, the
mention event on the witness-free prefix run. -/
def mentionTerm
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : PMF Bool :=
  (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
    (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
      (runFixed procedure world.other.family (prefixBudget tau kappa) (commitPrefix S.signer salt root) world.other.hashTable
        world.other.hashHistory world.other.cipherHistory world.other.trace).map mentionEvent

/-- The row-stored term of a world: over a uniform salt and root, the
row-stored event on the head's initial run. -/
def rowTerm (htau : tau ≠ 0)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : PMF Bool :=
  (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
    (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
      (runFixed procedure world.other.family (headBudget tau kappa - 1) (headInit S.signer salt root) world.other.hashTable
        world.other.hashHistory world.other.cipherHistory world.other.trace).map (rowStored htau)

/-- The input-present bound at a well-formed, supported world. -/
theorem inputPresent_le (hl : 0 < lambda) (htau : tau ≠ 0) (publicKey : List Bool)
    (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (hw : WellFormed world.other) {n : Nat} (hn : Supported world.hashTable n) :
    (inputPresent S publicKey witness message world) true ≤
      (mentionTerm S world) true + (rowTerm S htau world) true + (n : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ := by
  unfold inputPresent mentionTerm rowTerm
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
        (continueRun world.other.family 3 (prefixTail S.signer salt))).map mentionEvent) true +
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
        refine (bind_true_le_event_add _ _ mentionEvent _ (fun mid hmid hbad => ?_)).trans (le_add_left le_rfl)
        rcases prefix_or_mention_from hl htau S.signer salt world.other.family mid0 htr0 hord0 hfresh0 hext0 hstored0 data
            hdata hq mid hmid with h | ⟨head, o, a, m, hstate, hlines⟩
        · simp [mentionEvent, h] at hbad
        · have hfr : mid.hashTable (linesInput S.signer salt witness (head.1, head.2.1, head.2.2, o, a, m)) = none := by
            cases hc : mid.hashTable (linesInput S.signer salt witness (head.1, head.2.1, head.2.2, o, a, m)) with
            | none => rfl
            | some d =>
              have := hlines _ d hc
              simp [mentionEvent, this] at hbad
          exact tail_present_le S publicKey message salt witness world.hashTable hn world.other.family mid _ hstate hfr _)
  rw [PMF.bind_const] at hc
  simp only [PMF.pure_apply, Bool.true_eq_false, if_false, zero_add] at hc
  refine hc.trans (le_of_eq ?_)
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, PMF.bind_apply,
    RandomOracleTrap.map_true_eq]

end
end SDitH.Proofs.InputPresentBound
