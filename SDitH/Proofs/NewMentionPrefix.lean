import SDitH.Proofs.NewMentionChain
import SDitH.Proofs.PrefixFromHead

/-! The head and prefix statements with the relative event. A run's trace is
at least as long as its starting log; after a fresh last row query a
stored outer string raises the relative event; the head's result has the
outer string's stored case raising it; the prefix run from a head-initial
result either raises the relative event or finishes with the lines input
fresh unless it is stored, which raises the relative event. -/

namespace SDitH.Proofs.NewMentionPrefix

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind PrefixLinesFresh PrefixHeadSplit PrefixLinesFreshRun ThreeHashRun OuterFresh
open HeadLastSplit HeadLastRun PrefixTailOrMention PrefixOrMention PrefixFromHead TraceSuffix NewMention NewMentionChain
open scoped Classical

noncomputable section

section Generic

variable {Input Digest Key Block State A B : Type*} [Fintype Digest] [Nonempty Digest]

/-- A run's trace is at least as long as its starting log. -/
theorem runFixed_length_le (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Spec.IdealCipher.Family Key Block) (fuel : Nat) (state : State) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support) :
    log.length ≤ out.trace.length := by
  obtain ⟨new, hnew⟩ := runFixed_trace_suffix procedure family fuel state table hashes ciphers log out hout
  rw [hnew, List.length_append]
  omega

/-- A continuation's trace is at least as long as the finished result's. -/
theorem continueRun_length_le (family : Spec.IdealCipher.Family Key Block) (m : Nat)
    (f : A → Program Input Digest Key Block B) (mid : Result Input Digest Key Block (Program Input Digest Key Block A))
    (v : A) (hmid : mid.state = .done v) (out : Result Input Digest Key Block (Program Input Digest Key Block B))
    (hout : out ∈ (continueRun family m f mid).support) : mid.trace.length ≤ out.trace.length := by
  obtain ⟨out', hout', _, _, htrace⟩ := continueRun_done_support family m f mid v hmid out hout
  rw [htrace]
  exact runFixed_length_le procedure family m (f v) mid.hashTable mid.hashHistory mid.cipherHistory mid.trace out' hout'

end Generic

variable {lambda tau kappa s wit rnd : Nat}

/-- After a fresh last row query with the traced invariant, a stored outer
string over the recorded row hashes raises the relative event. -/
theorem outer_mention_after_headN (hl : 0 < lambda) (htau : tau ≠ 0)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (L : List (Entry (List Bool) (Out lambda s wit rnd)))
    (mid : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (hL : L.length ≤ mid.trace.length) (data : HeadData lambda tau kappa) (hmid : mid.state = .done data)
    (hfresh : mid.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) = none)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (hout : out ∈ (continueRun family 1 (lastRow htau) mid).support) (htraced : Traced out.hashTable out.trace)
    (salt : Seed lambda) :
    ∃ a : Out lambda s wit rnd,
      out.state = .done (data.1, data.2.1, Function.update data.2.2 (lastIndex htau) a.1) ∧
      ∀ d : Out lambda s wit rnd,
        out.hashTable (outerString salt (Function.update data.2.2 (lastIndex htau) a.1)) = some d →
          newBad (digestMention (mentions lambda tau)) L out.trace = true := by
  obtain ⟨a, hstate, htrace, _⟩ := lastRow_shape htau family mid data hmid hfresh out hout
  refine ⟨a, hstate, fun d hd => ?_⟩
  rw [htrace] at htraced ⊢
  exact outer_stored_mentionN hl L out.hashTable _ _ hL htraced (fun e i => data.2.1 (e, i)) (lastIndex htau) rfl salt _
    (by simp) d hd

/-- From a head-initial result with the run invariants and the last row
query fresh, the rest of the prefix either raises the relative event or
finishes with the three answers, where a stored lines input raises it. -/
theorem prefix_or_mention_fromN {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (hl : 0 < lambda)
    (htau : tau ≠ 0) (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (L : List (Entry (List Bool) (Out lambda s wit rnd)))
    (mid0 : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (hL : L.length ≤ mid0.trace.length)
    (htraced : Traced mid0.hashTable mid0.trace) (hord : Ordered mid0.trace) (hfresh : Fresh mid0.trace)
    (hext : ∀ entry ∈ mid0.trace, Extends entry.before mid0.hashTable)
    (hstored : ∀ entry ∈ mid0.trace, mid0.hashTable entry.input = some entry.answer)
    (data : HeadData lambda tau kappa) (hdata : mid0.state = .done data)
    (hq : mid0.hashTable (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)) = none)
    (mid : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (hmid : mid ∈ ((continueRun family 1 (lastRow htau) mid0).bind (continueRun family 3 (prefixTail S salt))).support) :
    newBad (digestMention (mentions lambda tau)) L mid.trace = true ∨
      ∃ (head : HeadData lambda tau kappa) (o a m : Out lambda s wit rnd),
        mid.state = .done (head.1, head.2.1, head.2.2, o, a, m) ∧
        ∀ (tail : List Bool) (d : Out lambda s wit rnd), mid.hashTable (linesQuery a.1 tail) = some d →
          newBad (digestMention (mentions lambda tau)) L mid.trace = true := by
  obtain ⟨mid1, hmid1, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmid
  obtain ⟨htr1, hord1, hfresh1, hext1, hstored1⟩ := continueRun_invariants family 1 (lastRow htau) mid0 data hdata mid1
    hmid1 htraced hord hfresh hext hstored
  have hL1 : L.length ≤ mid1.trace.length :=
    hL.trans (continueRun_length_le family 1 (lastRow htau) mid0 data hdata mid1 hmid1)
  obtain ⟨a, hstate1, hmention⟩ := outer_mention_after_headN hl htau family L mid0 hL data hdata hq mid1 hmid1 htr1 salt
  obtain ⟨mid', hmid', hstate, htable, htrace⟩ := continueRun_done_support family 3 (prefixTail S salt) mid1 _ hstate1
    mid hcont
  rcases prefixTail_or_mentionN S salt (data.1, data.2.1, Function.update data.2.2 (lastIndex htau) a.1) family L
      mid1.hashTable mid1.hashHistory mid1.cipherHistory mid1.trace hL1 htr1 hord1 hfresh1 hext1 hstored1 hmention mid'
      hmid' with h | ⟨o, a', m, hstate', hlines⟩
  · rw [htrace]
    exact Or.inl h
  · refine Or.inr ⟨(data.1, data.2.1, Function.update data.2.2 (lastIndex htau) a.1), o, a', m, hstate.trans hstate',
      fun tail d hd => ?_⟩
    rw [htrace]
    exact hlines tail d (htable ▸ hd)

end
end SDitH.Proofs.NewMentionPrefix
