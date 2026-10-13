import SDitH.Proofs.TraceSuffix

/-! The prefix's last three queries: mention event or fresh shape. Stepping
through the outer, auxiliary and mask queries, each is either stored (so,
by the stored-mention lemmas, the mention event is raised on the current
log and persists to the run's trace) or fresh (so the run continues from
the recorded entry). When all three are fresh the run has the three-entry
shape, and a stored lines input of the auxiliary answer raises the
mention event. So the prefix run either raises the mention event or
finishes with the lines input fresh unless the event is raised. -/

namespace SDitH.Proofs.PrefixTailOrMention

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind PrefixLinesFresh ThreeHashRun ThreeHashShape StoredLinesMention LinesMention
open QueryPrefixes ChainFresh TraceSuffix
open scoped Classical

noncomputable section

variable {Input Digest Key Block A : Type*} [Fintype Digest] [Nonempty Digest]

/-- A fresh query's updated table is traced by the recorded entry. -/
theorem traced_update (table : Input → Option Digest) (log : List (Entry Input Digest)) (input : Input) (answer : Digest)
    (htraced : Traced table log) (h : table input = none) :
    Traced (Function.update table input (some answer)) (⟨table, input, answer⟩ :: log) := by
  have hmem : (answer, Function.update table input (some answer)) ∈ (Spec.RandomOracle.query table input).support := by
    unfold Spec.RandomOracle.query
    rw [h]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨answer, PMF.mem_support_uniformOfFintype _, rfl⟩
  have hq := SDitH.Proofs.RandomOracleTrace.query_traced table log input _ htraced hmem
  simpa [record, h] using hq

/-- Three hash queries: either the prefix event is raised on the run's trace,
or all three were fresh and the run has the three-entry shape. -/
theorem three_hash_or_mention (family : Spec.IdealCipher.Family Key Block)
    (bad : List (Entry Input Digest) → Input → Digest → Bool) (outerIn : Input) (auxIn : Digest → Input)
    (maskIn : Digest → Digest → Input) (k : Digest → Digest → Digest → A) (t0 : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (htraced : Traced t0 log) (houter : ∀ d, t0 outerIn = some d → prefixBad bad log = true)
    (haux : ∀ (o : Digest) (t1 : Input → Option Digest) (d : Digest), Traced t1 (⟨t0, outerIn, o⟩ :: log) →
      t1 (auxIn o) = some d → prefixBad bad (⟨t0, outerIn, o⟩ :: log) = true)
    (hmask : ∀ (o a : Digest) (t1 t2 : Input → Option Digest) (d : Digest),
      Traced t2 (⟨t1, auxIn o, a⟩ :: ⟨t0, outerIn, o⟩ :: log) → t2 (maskIn o a) = some d →
      prefixBad bad (⟨t1, auxIn o, a⟩ :: ⟨t0, outerIn, o⟩ :: log) = true)
    (out : Result Input Digest Key Block (Program Input Digest Key Block A))
    (hout : out ∈ (runFixed procedure family 3
      (.hash outerIn fun o => .hash (auxIn o) fun a => .hash (maskIn o a) fun m => .done (k o a m))
      t0 hashes ciphers log).support) :
    prefixBad bad out.trace = true ∨
    ∃ o a m : Digest,
      let t1 := Function.update t0 outerIn (some o)
      let t2 := Function.update t1 (auxIn o) (some a)
      out.state = .done (k o a m) ∧
      out.hashTable = Function.update t2 (maskIn o a) (some m) ∧
      out.trace = ⟨t2, maskIn o a, m⟩ :: ⟨t1, auxIn o, a⟩ :: ⟨t0, outerIn, o⟩ :: log := by
  cases h0 : t0 outerIn with
  | some d => exact Or.inl (runFixed_prefixBad procedure family bad 3 _ t0 hashes ciphers log out hout (houter d h0))
  | none =>
    obtain ⟨o, out1, hout1, heq1⟩ := runFixed_hash_fresh_support family 2 outerIn _ t0 hashes ciphers log h0 out hout
    have htr1 := traced_update t0 log outerIn o htraced h0
    cases h1 : Function.update t0 outerIn (some o) (auxIn o) with
    | some d =>
      refine Or.inl ?_
      rw [heq1, (mark_fields _ _).2.2.2.2]
      exact runFixed_prefixBad procedure family bad 2 _ _ _ ciphers _ out1 hout1 (haux o _ d htr1 h1)
    | none =>
      obtain ⟨a, out2, hout2, heq2⟩ := runFixed_hash_fresh_support family 1 (auxIn o) _ _ _ ciphers _ h1 out1 hout1
      have htr2 := traced_update _ _ (auxIn o) a htr1 h1
      cases h2 : Function.update (Function.update t0 outerIn (some o)) (auxIn o) (some a) (maskIn o a) with
      | some d =>
        refine Or.inl ?_
        rw [heq1, (mark_fields _ _).2.2.2.2, heq2, (mark_fields _ _).2.2.2.2]
        exact runFixed_prefixBad procedure family bad 1 _ _ _ ciphers _ out2 hout2 (hmask o a _ _ d htr2 h2)
      | none =>
        obtain ⟨m, out3, hout3, heq3⟩ := runFixed_hash_fresh_support family 0 (maskIn o a) _ _ _ ciphers _ h2 out2 hout2
        have h3 := runFixed_zero_support family (k o a m) _ _ ciphers _ out3 hout3
        refine Or.inr ⟨o, a, m, ?_, ?_, ?_⟩
        · rw [heq1, (mark_fields _ _).1, heq2, (mark_fields _ _).1, heq3, (mark_fields _ _).1, h3]
        · rw [heq1, (mark_fields _ _).2.1, heq2, (mark_fields _ _).2.1, heq3, (mark_fields _ _).2.1, h3]
        · rw [heq1, (mark_fields _ _).2.2.2.2, heq2, (mark_fields _ _).2.2.2.2, heq3, (mark_fields _ _).2.2.2.2, h3]

variable {lambda tau kappa s wit rnd : Nat}

/-- The auxiliary query's tail of the head's data. -/
def auxTailOf {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt : Bits lambda) (head : HeadData lambda tau kappa) : List Bool :=
  Spec.BLCHashChain.sourceTail S.encoding (Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow
    (Spec.BLCCommit.randomTable S.p salt (fun e i => head.1 (leafNode e i).val) S.randomCount S.enough)))

theorem auxInputOf_eq {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt : Bits lambda) (head : HeadData lambda tau kappa) (o : Out lambda s wit rnd) :
    auxInputOf S salt head o = auxQuery o.1 (auxTailOf S salt head) := rfl

/-- The prefix's last three queries from a head result: either the mention
event is raised on the run's trace, or the run finishes with the three
answers and a stored lines input of the auxiliary answer raises the
mention event. -/
theorem prefixTail_or_mention {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (head : HeadData lambda tau kappa)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (t0 : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd)))
    (htraced : Traced t0 log) (hord : Ordered log) (hfresh : Fresh log) (hext : ∀ entry ∈ log, Extends entry.before t0)
    (hstored : ∀ entry ∈ log, t0 entry.input = some entry.answer)
    (houter : ∀ d, t0 (outerString salt head.2.2) = some d → prefixBad (digestMention (mentions lambda tau)) log = true)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (hout : out ∈ (runFixed procedure family 3 (prefixTail S salt head) t0 hashes ciphers log).support) :
    prefixBad (digestMention (mentions lambda tau)) out.trace = true ∨
      ∃ o a m : Out lambda s wit rnd, out.state = .done (head.1, head.2.1, head.2.2, o, a, m) ∧
        ∀ (tail : List Bool) (d : Out lambda s wit rnd), out.hashTable (linesQuery a.1 tail) = some d →
          prefixBad (digestMention (mentions lambda tau)) out.trace = true := by
  rcases three_hash_or_mention family (digestMention (mentions lambda tau)) (outerString salt head.2.2)
      (auxInputOf S salt head) (fun _ a => maskInput a.1) (fun o a m => (head.1, head.2.1, head.2.2, o, a, m))
      t0 hashes ciphers log htraced houter
      (fun o t1 d htr h => aux_stored_mention t1 ⟨t0, outerString salt head.2.2, o⟩ log htr salt head.2.2 rfl
        (auxTailOf S salt head) d h)
      (fun o a t1 t2 d htr h => mask_stored_mention t2 ⟨t1, auxInputOf S salt head o, a⟩ _ htr o.1 (auxTailOf S salt head)
        (auxInputOf_eq S salt head o) d h)
      out hout with h | ⟨o, a, m, hstate, _, htrace⟩
  · exact Or.inl h
  · obtain ⟨htr, _, _, _, _, _⟩ := HashCipherTrace.run_invariants procedure family 3 (prefixTail S salt head) t0 hashes
      ciphers log out hout htraced hord hfresh hext hstored
    refine Or.inr ⟨o, a, m, hstate, fun tail d hd => ?_⟩
    rw [htrace] at htr ⊢
    exact prefixBad_of_stored (mentions lambda tau) out.hashTable _ _ _ htr (linesQuery a.1 tail) d hd
      (linesQuery_ne_maskInput a.1 a.1 tail) (linesQuery_ne_auxQuery a.1 o.1 tail _)
      (auxiliary_mem_mentions_lines a.1 tail)

end
end SDitH.Proofs.PrefixTailOrMention
