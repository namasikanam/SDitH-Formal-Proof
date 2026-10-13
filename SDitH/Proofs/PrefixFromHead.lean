import SDitH.Proofs.PrefixMentionBound

/-! The prefix statement from the head's initial result, and a bind bound
with pointwise costs. A continuation from a finished result with the run
invariants keeps them; from a head-initial result with the last row query
fresh, the rest of the prefix (last row query, then the three queries)
either raises the mention event or finishes with the three answers and a
stored lines input raising the event. Two continuations whose pointwise
distance is a cost have binds within the expected cost. -/

namespace SDitH.Proofs.PrefixFromHead

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind CommitSplitRun PrefixLinesFresh PrefixHeadSplit PrefixLinesFreshRun OuterFresh
open HeadLastSplit HeadLastRun PrefixTailOrMention PrefixOrMention
open scoped Classical ENNReal

noncomputable section

section Generic

variable {A B : Type*}

/-- Two continuations within a pointwise cost: the binds are within the
expected cost. -/
theorem bind_le_bind_add_cost (p : PMF A) (f g : A → PMF B) (c : A → ℝ≥0∞) (b : B)
    (h : ∀ a ∈ p.support, f a b ≤ g a b + c a) :
    (p.bind f) b ≤ (p.bind g) b + ∑' a, p a * c a := by
  simp only [PMF.bind_apply]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [← mul_add]
    exact mul_le_mul_right (h a ha) _
  · rw [PMF.mem_support_iff, not_not] at ha
    rw [ha]
    simp

end Generic

variable {Input Digest Key Block A B : Type*} [Fintype Digest] [Nonempty Digest]

/-- A continuation from a finished result with the run invariants keeps
them. -/
theorem continueRun_invariants (family : Spec.IdealCipher.Family Key Block) (m : Nat)
    (f : A → Program Input Digest Key Block B) (mid : Result Input Digest Key Block (Program Input Digest Key Block A))
    (v : A) (hmid : mid.state = .done v) (out : Result Input Digest Key Block (Program Input Digest Key Block B))
    (hout : out ∈ (continueRun family m f mid).support)
    (htraced : Traced mid.hashTable mid.trace) (hord : Ordered mid.trace) (hfresh : Fresh mid.trace)
    (hext : ∀ entry ∈ mid.trace, Extends entry.before mid.hashTable)
    (hstored : ∀ entry ∈ mid.trace, mid.hashTable entry.input = some entry.answer) :
    Traced out.hashTable out.trace ∧ Ordered out.trace ∧ Fresh out.trace ∧
      (∀ entry ∈ out.trace, Extends entry.before out.hashTable) ∧
      ∀ entry ∈ out.trace, out.hashTable entry.input = some entry.answer := by
  obtain ⟨out', hout', _, htable, htrace⟩ := continueRun_done_support family m f mid v hmid out hout
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := HashCipherTrace.run_invariants procedure family m (f v) mid.hashTable
    mid.hashHistory mid.cipherHistory mid.trace out' hout' htraced hord hfresh hext hstored
  rw [htable, htrace]
  exact ⟨h1, h2, h3, h4, h5⟩

variable {lambda tau kappa s wit rnd : Nat}

/-- From a head-initial result with the run invariants and the last row
query fresh, the rest of the prefix either raises the mention event or
finishes with the three answers, where a stored lines input raises it. -/
theorem prefix_or_mention_from {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (hl : 0 < lambda)
    (htau : tau ≠ 0) (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (mid0 : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (htraced : Traced mid0.hashTable mid0.trace) (hord : Ordered mid0.trace) (hfresh : Fresh mid0.trace)
    (hext : ∀ entry ∈ mid0.trace, Extends entry.before mid0.hashTable)
    (hstored : ∀ entry ∈ mid0.trace, mid0.hashTable entry.input = some entry.answer)
    (data : HeadData lambda tau kappa) (hdata : mid0.state = .done data)
    (hq : mid0.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) = none)
    (mid : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (hmid : mid ∈ ((continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt))).support) :
    prefixBad (digestMention (mentions lambda tau)) mid.trace = true ∨
      ∃ (head : HeadData lambda tau kappa) (o a m : Out lambda s wit rnd),
        mid.state = .done (head.1, head.2.1, head.2.2, o, a, m) ∧
        ∀ (tail : List Bool) (d : Out lambda s wit rnd), mid.hashTable (linesQuery a.1 tail) = some d →
          prefixBad (digestMention (mentions lambda tau)) mid.trace = true := by
  obtain ⟨mid1, hmid1, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmid
  obtain ⟨htr1, hord1, hfresh1, hext1, hstored1⟩ := continueRun_invariants family 1 (lastRow htau) mid0 data hdata mid1
    hmid1 htraced hord hfresh hext hstored
  obtain ⟨a, hstate1, hmention⟩ := outer_mention_after_head hl htau family mid0 data hdata hq mid1 hmid1 htr1 salt
  obtain ⟨mid', hmid', hstate, htable, htrace⟩ := continueRun_done_support family 3 (prefixTail S salt) mid1 _ hstate1
    mid hcont
  rcases prefixTail_or_mention S salt (data.1, data.2.1, Function.update data.2.2 (lastIndex htau) a.1) family
      mid1.hashTable mid1.hashHistory mid1.cipherHistory mid1.trace htr1 hord1 hfresh1 hext1 hstored1 hmention mid'
      hmid' with h | ⟨o, a', m, hstate', hlines⟩
  · rw [htrace]
    exact Or.inl h
  · refine Or.inr ⟨(data.1, data.2.1, Function.update data.2.2 (lastIndex htau) a.1), o, a', m, hstate.trans hstate',
      fun tail d hd => ?_⟩
    rw [htrace]
    exact hlines tail d (htable ▸ hd)

end
end SDitH.Proofs.PrefixFromHead
