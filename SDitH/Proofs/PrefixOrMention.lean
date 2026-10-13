import SDitH.Proofs.PrefixTailOrMention

/-! The prefix run: mention event or fresh lines input. A bounded program's
run with its bound as fuel finishes, so the head's initial part finishes;
with the last row query fresh at that result (an explicit condition, the
named candidate term for the commitments' freshness), the head's result
has the outer string's stored case raising the mention event. The prefix
run is the head's run continued by the last three queries, so it either
raises the mention event or finishes with the three answers and a stored
lines input raising the event. -/

namespace SDitH.Proofs.PrefixOrMention

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind CommitSplitRun PrefixLinesFresh PrefixHeadSplit PrefixLinesFreshRun ThreeHashRun OuterFresh
open HeadLastSplit HeadLastRun PrefixTailOrMention
open scoped Classical

noncomputable section

variable {Input Digest Key Block A : Type*} [Fintype Digest] [Nonempty Digest]

/-- A bounded program's run with its bound as fuel finishes. -/
theorem runFixed_bounded_done (family : Spec.IdealCipher.Family Key Block) (k : Nat)
    (p : Program Input Digest Key Block A) (hp : Bounded k p) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block (Program Input Digest Key Block A))
    (hout : out ∈ (runFixed procedure family k p table hashes ciphers log).support) :
    ∃ v : A, out.state = .done v := by
  induction k generalizing p table hashes ciphers log out with
  | zero =>
    cases p with
    | done v =>
      simp only [runFixed, PMF.mem_support_pure_iff] at hout
      subst out
      exact ⟨v, rfl⟩
    | hash input next => exact absurd hp (by simp [Bounded])
    | cipher request next => exact absurd hp (by simp [Bounded])
  | succ k ih =>
    cases p with
    | done v =>
      have hstep : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block A)).step (.done v) = PMF.pure .stop := rfl
      simp only [runFixed, hstep, PMF.pure_bind, PMF.mem_support_pure_iff] at hout
      subst out
      exact ⟨v, rfl⟩
    | hash input next =>
      have hstep : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block A)).step (.hash input next) = PMF.pure (.hash input next) := rfl
      simp only [runFixed, hstep, PMF.pure_bind] at hout
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      obtain ⟨v, hv⟩ := ih (next result.1) (hp result.1) _ _ _ _ inner hinner
      exact ⟨v, by rw [(mark_fields _ _).1, hv]⟩
    | cipher request next =>
      have hstep : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block A)).step (.cipher request next) = PMF.pure (.cipher request next) := rfl
      simp only [runFixed, hstep, PMF.pure_bind] at hout
      exact ih _ (hp _) _ _ _ _ out hout

variable {lambda tau kappa s wit rnd : Nat}

/-- The head's run finishes, and with the last row query fresh at the
initial part's result, a stored outer string raises the mention event. -/
theorem head_outer_mention {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (hl : 0 < lambda) (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda)
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
    (mid : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (HeadData lambda tau kappa)))
    (hmid : mid ∈ (runFixed procedure family (headBudget tau kappa) (prefixHead S salt root) t0 hashes ciphers log).support) :
    ∃ head : HeadData lambda tau kappa, mid.state = .done head ∧
      ∀ d, mid.hashTable (outerString salt head.2.2) = some d →
        prefixBad (digestMention (mentions lambda tau)) mid.trace = true := by
  have hinv := HashCipherTrace.run_invariants procedure family _ _ t0 hashes ciphers log mid hmid htraced hord hfresh
    hext hstored
  rw [runFixed_head_split htau S salt root family t0 hashes ciphers log] at hmid
  obtain ⟨mid0, hmid0, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmid
  obtain ⟨data, hdata⟩ := runFixed_bounded_done family _ _ (headInit_bounded htau S salt root) t0 hashes ciphers log
    mid0 hmid0
  obtain ⟨a, hstate, hmention⟩ := outer_mention_after_head hl htau family mid0 data hdata (hrow mid0 data hmid0 hdata)
    mid hcont hinv.1 salt
  exact ⟨(data.1, data.2.1, Function.update data.2.2 (lastIndex htau) a.1), hstate, hmention⟩

/-- The prefix run: either the mention event is raised on its trace, or it
finishes with the head's data and the three answers, where a stored lines
input of the auxiliary answer raises the event. -/
theorem prefix_or_mention {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (hl : 0 < lambda) (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda)
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
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (hout : out ∈ (runFixed procedure family (prefixBudget tau kappa) (commitPrefix S salt root) t0 hashes ciphers
      log).support) :
    prefixBad (digestMention (mentions lambda tau)) out.trace = true ∨
      ∃ (head : HeadData lambda tau kappa) (o a m : Out lambda s wit rnd),
        out.state = .done (head.1, head.2.1, head.2.2, o, a, m) ∧
        ∀ (tail : List Bool) (d : Out lambda s wit rnd), out.hashTable (linesQuery a.1 tail) = some d →
          prefixBad (digestMention (mentions lambda tau)) out.trace = true := by
  rw [runFixed_prefix_split S salt root family t0 hashes ciphers log] at hout
  obtain ⟨mid, hmid, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨head, hhead, houter⟩ := head_outer_mention hl htau S salt root family t0 hashes ciphers log htraced hord hfresh
    hext hstored hrow mid hmid
  obtain ⟨htr, hord', hfresh', hext', hstored', _⟩ := HashCipherTrace.run_invariants procedure family _ _ t0 hashes
    ciphers log mid hmid htraced hord hfresh hext hstored
  obtain ⟨out', hout', hstate, htable, htrace⟩ := continueRun_done_support family 3 (prefixTail S salt) mid head hhead
    out hcont
  rcases prefixTail_or_mention S salt head family mid.hashTable mid.hashHistory mid.cipherHistory mid.trace htr hord'
      hfresh' hext' hstored' houter out' hout' with h | ⟨o, a, m, hstate', hlines⟩
  · rw [htrace]
    exact Or.inl h
  · refine Or.inr ⟨head, o, a, m, hstate.trans hstate', fun tail d hd => ?_⟩
    rw [htrace]
    exact hlines tail d (htable ▸ hd)

end
end SDitH.Proofs.PrefixOrMention
