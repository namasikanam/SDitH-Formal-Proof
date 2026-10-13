import SDitH.Proofs.PrefixFromHead

/-! The commitment run's lines digest up to two named events. The row-stored
event is the last row query stored at the head's initial result. Two
witnesses' commitment runs have lines-digest distributions within the
prefix's mention-event probability plus the row-stored event's
probability, with no further condition. -/

namespace SDitH.Proofs.CommitLinesEvents

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.RandomOracleTrap (indicator)
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind CommitSplitRun PrefixLinesFresh PrefixHeadSplit OuterFresh
open HeadLastSplit HeadLastRun PrefixOrMention PrefixFromHead CommitLinesEvent TailLinesDigest
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The named event: the last row query stored at the head's initial
result. -/
def rowStored (htau : tau ≠ 0)
    (mid0 : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa))) : Bool :=
  decide (∃ data : HeadData lambda tau kappa, mid0.state = .done data ∧
    mid0.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) ≠ none)

/-- The mention event on a prefix result. -/
def mentionEvent
    (mid : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd))) :
    Bool :=
  prefixBad (digestMention (mentions lambda tau)) mid.trace

/-- From a head-initial result with the last row query fresh, the two
witnesses' rest-of-commitment runs are within the mention event's
probability. -/
theorem rest_le {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (hl : 0 < lambda) (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (mid0 : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (htraced : Traced mid0.hashTable mid0.trace) (hord : Ordered mid0.trace) (hfresh : Fresh mid0.trace)
    (hext : ∀ entry ∈ mid0.trace, Extends entry.before mid0.hashTable)
    (hstored : ∀ entry ∈ mid0.trace, mid0.hashTable entry.input = some entry.answer)
    (data : HeadData lambda tau kappa) (hdata : mid0.state = .done data)
    (hq : mid0.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) = none)
    (witness fake : Fin wit → ZMod 2) (E : Option (Digest lambda)) :
    ((((continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt))).bind
        (continueRun family 1 (commitTail S salt witness))).map linesDigestOf) E ≤
      ((((continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt))).bind
          (continueRun family 1 (commitTail S salt fake))).map linesDigestOf) E +
        (((continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt))).map
          mentionEvent) true := by
  rw [PMF.map_bind, PMF.map_bind]
  refine bind_le_bind_add_event _ _ _ _ (fun mid hmid hbad => ?_) E
  rcases prefix_or_mention_from hl htau S salt family mid0 htraced hord hfresh hext hstored data hdata hq mid hmid
    with h | ⟨head, o, a, m, hstate, hlines⟩
  · simp [mentionEvent, h] at hbad
  · have hw : mid.hashTable (linesInput S salt witness (head.1, head.2.1, head.2.2, o, a, m)) = none := by
      cases hc : mid.hashTable (linesInput S salt witness (head.1, head.2.1, head.2.2, o, a, m)) with
      | none => rfl
      | some d =>
        have := hlines _ d hc
        simp [mentionEvent, this] at hbad
    have hf : mid.hashTable (linesInput S salt fake (head.1, head.2.1, head.2.2, o, a, m)) = none := by
      cases hc : mid.hashTable (linesInput S salt fake (head.1, head.2.1, head.2.2, o, a, m)) with
      | none => rfl
      | some d =>
        have := hlines _ d hc
        simp [mentionEvent, this] at hbad
    exact tail_linesDigest_congr S salt witness fake family mid _ hstate hw hf

/-- Two witnesses' commitment runs have lines-digest distributions within
the mention event's probability plus the row-stored event's probability. -/
theorem commit_linesDigest_le_events {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (hl : 0 < lambda)
    (htau : tau ≠ 0) (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (t0 : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd)))
    (htraced : Traced t0 log) (hord : Ordered log) (hfresh : Fresh log) (hext : ∀ entry ∈ log, Extends entry.before t0)
    (hstored : ∀ entry ∈ log, t0 entry.input = some entry.answer)
    (witness fake : Fin wit → ZMod 2) (E : Option (Digest lambda)) :
    ((runFixed procedure family (commitBudget tau kappa) (commitProgram S salt root witness) t0 hashes ciphers log).map
        linesDigestOf) E ≤
      ((runFixed procedure family (commitBudget tau kappa) (commitProgram S salt root fake) t0 hashes ciphers log).map
          linesDigestOf) E +
        ((runFixed procedure family (prefixBudget tau kappa) (commitPrefix S salt root) t0 hashes ciphers log).map
          mentionEvent) true +
        ((runFixed procedure family (headBudget tau kappa - 1) (headInit S salt root) t0 hashes ciphers log).map
          (rowStored htau)) true := by
  have hsplit : ∀ w : Fin wit → ZMod 2,
      runFixed procedure family (commitBudget tau kappa) (commitProgram S salt root w) t0 hashes ciphers log =
        (runFixed procedure family (headBudget tau kappa - 1) (headInit S salt root) t0 hashes ciphers log).bind
          fun mid0 => (((continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt))).bind
            (continueRun family 1 (commitTail S salt w))) := by
    intro w
    rw [runFixed_commit_split S salt root w family t0 hashes ciphers log,
      runFixed_prefix_split S salt root family t0 hashes ciphers log,
      runFixed_head_split htau S salt root family t0 hashes ciphers log, PMF.bind_bind, PMF.bind_bind]
    congr 1
    funext mid0
    rw [PMF.bind_bind]
  have hprefix : runFixed procedure family (prefixBudget tau kappa) (commitPrefix S salt root) t0 hashes ciphers log =
      (runFixed procedure family (headBudget tau kappa - 1) (headInit S salt root) t0 hashes ciphers log).bind
        fun mid0 => (continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt)) := by
    rw [runFixed_prefix_split S salt root family t0 hashes ciphers log,
      runFixed_head_split htau S salt root family t0 hashes ciphers log, PMF.bind_bind]
  rw [hsplit witness, hsplit fake, hprefix, PMF.map_bind, PMF.map_bind, PMF.map_bind]
  refine (bind_le_bind_add_cost
    (runFixed procedure family (headBudget tau kappa - 1) (headInit S salt root) t0 hashes ciphers log)
    (fun mid0 => (((continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt))).bind
      (continueRun family 1 (commitTail S salt witness))).map linesDigestOf)
    (fun mid0 => (((continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt))).bind
      (continueRun family 1 (commitTail S salt fake))).map linesDigestOf)
    (fun mid0 => (((continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt))).map
      mentionEvent) true + indicator (rowStored htau mid0)) E (fun mid0 hmid0 => ?_)).trans (le_of_eq ?_)
  · dsimp only
    cases hrs : rowStored htau mid0 with
    | true =>
      rw [RandomOracleTrap.indicator_true]
      exact (PMF.coe_le_one _ _).trans (le_add_left (le_add_left le_rfl))
    | false =>
      obtain ⟨data, hdata⟩ := runFixed_bounded_done family _ _ (headInit_bounded htau S salt root) t0 hashes ciphers
        log mid0 hmid0
      have hq : mid0.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) = none := by
        by_contra hne
        have hdec : rowStored htau mid0 = true := decide_eq_true ⟨data, hdata, hne⟩
        rw [hrs] at hdec
        exact Bool.false_ne_true hdec
      obtain ⟨htr0, hord0, hfresh0, hext0, hstored0, _⟩ := HashCipherTrace.run_invariants procedure family _ _ t0
        hashes ciphers log mid0 hmid0 htraced hord hfresh hext hstored
      rw [RandomOracleTrap.indicator_false, add_zero]
      exact rest_le hl htau S salt family mid0 htr0 hord0 hfresh0 hext0 hstored0 data hdata hq witness fake E
  · dsimp only
    rw [add_assoc]
    congr 1
    simp_rw [mul_add]
    rw [ENNReal.tsum_add, RandomOracleTrap.map_true_eq]
    congr 1

end
end SDitH.Proofs.CommitLinesEvents
