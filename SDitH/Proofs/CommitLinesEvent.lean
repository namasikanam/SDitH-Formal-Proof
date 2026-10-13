import SDitH.Proofs.PrefixOrMention
import SDitH.Proofs.TailLinesDigest

/-! The commitment run's lines digest up to the mention event. Each prefix
result either raises the mention event on its trace or finishes with its
data and the lines input of any witness fresh. Two continuations that
agree off an event have distributions within the event's probability. So
two witnesses' commitment runs have lines-digest distributions within the
prefix's mention-event probability. -/

namespace SDitH.Proofs.CommitLinesEvent

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind CommitSplitRun PrefixLinesFresh PrefixHeadSplit HeadLastSplit OuterFresh
open PrefixOrMention TailLinesDigest
open scoped Classical ENNReal

noncomputable section

section Generic

variable {A B : Type*}

/-- Two continuations that agree off an event: the first's distribution is
within the event's probability of the second's. -/
theorem bind_le_bind_add_event (p : PMF A) (f g : A → PMF B) (bad : A → Bool)
    (h : ∀ a ∈ p.support, bad a = false → f a = g a) (b : B) :
    (p.bind f) b ≤ (p.bind g) b + (p.map bad) true := by
  simp only [PMF.bind_apply, PMF.map_apply]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · cases hb : bad a with
    | false =>
      rw [h a ha hb, if_neg (by decide), add_zero]
    | true =>
      rw [if_pos rfl]
      calc p a * f a b ≤ p a * 1 := mul_le_mul_right (PMF.coe_le_one _ _) _
        _ = p a := mul_one _
        _ ≤ p a * g a b + p a := le_add_self
  · rw [PMF.mem_support_iff, not_not] at ha
    rw [ha]
    simp

end Generic

variable {lambda tau kappa s wit rnd : Nat}

/-- Each prefix result: the mention event on its trace, or its finished data
with the lines input of any witness fresh. -/
theorem prefix_lines_fresh_or_mention {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (hl : 0 < lambda)
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
    (witness : Fin wit → ZMod 2)
    (mid : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (hmid : mid ∈ (runFixed procedure family (prefixBudget tau kappa) (commitPrefix S salt root) t0 hashes ciphers
      log).support) :
    prefixBad (digestMention (mentions lambda tau)) mid.trace = true ∨
      ∃ data : PrefixData lambda tau kappa s wit rnd, mid.state = .done data ∧
        mid.hashTable (linesInput S salt witness data) = none := by
  rcases prefix_or_mention hl htau S salt root family t0 hashes ciphers log htraced hord hfresh hext hstored hrow mid
      hmid with h | ⟨head, o, a, m, hstate, hlines⟩
  · exact Or.inl h
  · cases hc : mid.hashTable (linesInput S salt witness (head.1, head.2.1, head.2.2, o, a, m)) with
    | some d => exact Or.inl (hlines _ d hc)
    | none => exact Or.inr ⟨_, hstate, hc⟩

/-- Two witnesses' commitment runs have lines-digest distributions within
the prefix's mention-event probability. -/
theorem commit_linesDigest_le {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (hl : 0 < lambda)
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
        ((runFixed procedure family (prefixBudget tau kappa) (commitPrefix S salt root) t0 hashes ciphers log).map
          fun mid => prefixBad (digestMention (mentions lambda tau)) mid.trace) true := by
  rw [runFixed_commit_split S salt root witness family t0 hashes ciphers log,
    runFixed_commit_split S salt root fake family t0 hashes ciphers log, PMF.map_bind, PMF.map_bind]
  refine bind_le_bind_add_event _ _ _ _ (fun mid hmid hbad => ?_) E
  rcases prefix_lines_fresh_or_mention hl htau S salt root family t0 hashes ciphers log htraced hord hfresh hext hstored
      hrow witness mid hmid with h | ⟨data, hstate, hfree⟩
  · simp [h] at hbad
  · rcases prefix_lines_fresh_or_mention hl htau S salt root family t0 hashes ciphers log htraced hord hfresh hext
        hstored hrow fake mid hmid with h' | ⟨data', hstate', hfree'⟩
    · simp [h'] at hbad
    · have hd : data' = data := Program.done.inj (hstate'.symm.trans hstate)
      subst hd
      exact tail_linesDigest_congr S salt witness fake family mid data' hstate hfree hfree'

end
end SDitH.Proofs.CommitLinesEvent
