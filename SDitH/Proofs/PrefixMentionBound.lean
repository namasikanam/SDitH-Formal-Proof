import SDitH.Proofs.CommitLinesEvent

/-! The prefix's mention-event probability. The prefix run's mention event is
bounded by the prefix-dependent trap bound: the event's indicator on the
starting log plus, per query of the prefix budget, the current log length
times the mention-set size over the digest count. Combined with the
commitment runs' comparison, two witnesses' lines-digest distributions
are within this bound. -/

namespace SDitH.Proofs.PrefixMentionBound

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.RandomOracleTrap (indicator)
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition CommitSplitRun PrefixLinesFresh PrefixHeadSplit HeadLastSplit OuterFresh
open SDitH.Proofs.BAVCChainInputs CommitLinesEvent TailLinesDigest
open scoped Classical ENNReal BigOperators

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The per-query mention bound after a log of the given length. -/
def mentionStep (lambda tau : Nat) (n : Nat) : ℝ≥0∞ :=
  (n : ℝ≥0∞) * (tau + 2 : Nat) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹

/-- The prefix run's mention event is bounded by the prefix-dependent trap
bound over the prefix budget. -/
theorem prefix_mention_bound {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (t0 : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd))) :
    ((runFixed procedure family (prefixBudget tau kappa) (commitPrefix S salt root) t0 hashes ciphers log).map
        fun mid => prefixBad (digestMention (mentions lambda tau)) mid.trace) true ≤
      indicator (prefixBad (digestMention (mentions lambda tau)) log) +
        ∑ i ∈ Finset.range (prefixBudget tau kappa), mentionStep lambda tau (log.length + i) :=
  HashCipherTrace.run_prefix_bound procedure family (digestMention (mentions lambda tau)) (mentionStep lambda tau)
    (fun log input => ProductOracle.digest_mention_query_bound (mentions lambda tau) (tau + 2)
      (fun input => mentions_card_le input) log input)
    (prefixBudget tau kappa) (commitPrefix S salt root) t0 hashes ciphers log

/-- Two witnesses' commitment runs have lines-digest distributions within
the prefix's mention bound. -/
theorem commit_linesDigest_le_bound {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (hl : 0 < lambda)
    (htau : tau ≠ 0) (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (t0 : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd)))
    (htraced : Traced t0 log) (hord : Ordered log) (hfresh : Fresh log) (hext : ∀ entry ∈ log, Extends entry.before t0)
    (hstored : ∀ entry ∈ log, t0 entry.input = some entry.answer)
    (hrow : ∀ (mid0 : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
        (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
      (data : HeadData lambda tau kappa),
      mid0 ∈ (runFixed procedure family (headBudget tau kappa - 1) (headInit S salt root) t0 hashes ciphers log).support →
      mid0.state = .done data →
      mid0.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) = none)
    (witness fake : Fin wit → ZMod 2) (E : Option (Digest lambda)) :
    ((runFixed procedure family (commitBudget tau kappa) (commitProgram S salt root witness) t0 hashes ciphers log).map
        linesDigestOf) E ≤
      ((runFixed procedure family (commitBudget tau kappa) (commitProgram S salt root fake) t0 hashes ciphers log).map
          linesDigestOf) E +
        (indicator (prefixBad (digestMention (mentions lambda tau)) log) +
          ∑ i ∈ Finset.range (prefixBudget tau kappa), mentionStep lambda tau (log.length + i)) :=
  (commit_linesDigest_le hl htau S salt root family t0 hashes ciphers log htraced hord hfresh hext hstored hrow witness
    fake E).trans (add_le_add_right (prefix_mention_bound S salt root family t0 hashes ciphers log) _)

end
end SDitH.Proofs.PrefixMentionBound
