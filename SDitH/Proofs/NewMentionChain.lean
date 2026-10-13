import SDitH.Proofs.NewMention
import SDitH.Proofs.PrefixTailOrMention

/-! The chain's mention events relative to a base log. The relative event
persists along runs and continuations; the auxiliary, mask, outer and
lines stored inputs raise it (their mentioning entries are new); and the
prefix's last three queries either raise it or finish fresh with the
lines input's stored case raising it. -/

namespace SDitH.Proofs.NewMentionChain

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain Spec.HashCipherProgram Spec.SharedSigner
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind PrefixLinesFresh ThreeHashRun ThreeHashShape StoredLinesMention LinesMention
open QueryPrefixes ChainFresh TraceSuffix OuterFresh PrefixLinesFreshRun NewMention PrefixTailOrMention
open SDitH.Proofs.BAVCChainInputs
open scoped Classical

noncomputable section

section Generic

variable {Input Digest : Type*}

/-- The relative event persists under new entries in front. -/
theorem newBad_persist (bad : List (Entry Input Digest) → Input → Digest → Bool) (L new t : List (Entry Input Digest))
    (h : newBad bad L t = true) : newBad bad L (new ++ t) = true := by
  unfold newBad at h ⊢
  have hlt : L.length < t.length := by
    by_contra hc
    push_neg at hc
    rw [Nat.sub_eq_zero_of_le hc] at h
    simp [prefixBadN] at h
  rw [List.length_append, show new.length + t.length - L.length = new.length + (t.length - L.length) by omega]
  exact prefixBadN_persist bad new t _ h

/-- A newest entry's event, relative to a base the log extends. -/
theorem newBad_head (bad : List (Entry Input Digest) → Input → Digest → Bool) (L log : List (Entry Input Digest))
    (e : Entry Input Digest) (hL : L.length ≤ log.length) (h : prefixBadN bad (log.length - L.length + 1) (e :: log) = true) :
    newBad bad L (e :: log) = true := by
  unfold newBad
  rw [List.length_cons, show log.length + 1 - L.length = log.length - L.length + 1 by omega]
  exact h

/-- A second-newest entry's event, relative to a base the log extends. -/
theorem newBad_two (bad : List (Entry Input Digest) → Input → Digest → Bool) (L log : List (Entry Input Digest))
    (e₂ e₁ : Entry Input Digest) (hL : L.length ≤ log.length)
    (h : prefixBadN bad (log.length - L.length + 2) (e₂ :: e₁ :: log) = true) : newBad bad L (e₂ :: e₁ :: log) = true := by
  unfold newBad
  rw [List.length_cons, List.length_cons, show log.length + 1 + 1 - L.length = log.length - L.length + 2 by omega]
  exact h

variable {Key Block State A B : Type*} [Fintype Digest] [Nonempty Digest]

/-- The relative event on the starting log persists to the run's trace. -/
theorem runFixed_newBad (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Spec.IdealCipher.Family Key Block) (bad : List (Entry Input Digest) → Input → Digest → Bool)
    (L : List (Entry Input Digest)) (fuel : Nat) (state : State) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support)
    (h : newBad bad L log = true) : newBad bad L out.trace = true := by
  obtain ⟨new, hnew⟩ := runFixed_trace_suffix procedure family fuel state table hashes ciphers log out hout
  rw [hnew]
  exact newBad_persist bad L new log h

/-- The relative event on a finished result's trace persists to any
continuation. -/
theorem continueRun_newBad (family : Spec.IdealCipher.Family Key Block)
    (bad : List (Entry Input Digest) → Input → Digest → Bool) (L : List (Entry Input Digest)) (m : Nat)
    (f : A → Program Input Digest Key Block B) (mid : Result Input Digest Key Block (Program Input Digest Key Block A))
    (v : A) (hmid : mid.state = .done v) (out : Result Input Digest Key Block (Program Input Digest Key Block B))
    (hout : out ∈ (continueRun family m f mid).support) (h : newBad bad L mid.trace = true) :
    newBad bad L out.trace = true := by
  obtain ⟨out', hout', _, _, htrace⟩ := continueRun_done_support family m f mid v hmid out hout
  rw [htrace]
  exact runFixed_newBad procedure family bad L m (f v) mid.hashTable mid.hashHistory mid.cipherHistory mid.trace out'
    hout' h

/-- Three hash queries: either the relative event is raised on the run's
trace, or all three were fresh and the run has the three-entry shape. -/
theorem three_hash_or_mentionN (family : Spec.IdealCipher.Family Key Block)
    (bad : List (Entry Input Digest) → Input → Digest → Bool) (L : List (Entry Input Digest)) (outerIn : Input)
    (auxIn : Digest → Input) (maskIn : Digest → Digest → Input) (k : Digest → Digest → Digest → A)
    (t0 : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Entry Input Digest)) (htraced : Traced t0 log) (houter : ∀ d, t0 outerIn = some d → newBad bad L log = true)
    (haux : ∀ (o : Digest) (t1 : Input → Option Digest) (d : Digest), Traced t1 (⟨t0, outerIn, o⟩ :: log) →
      t1 (auxIn o) = some d → newBad bad L (⟨t0, outerIn, o⟩ :: log) = true)
    (hmask : ∀ (o a : Digest) (t1 t2 : Input → Option Digest) (d : Digest),
      Traced t2 (⟨t1, auxIn o, a⟩ :: ⟨t0, outerIn, o⟩ :: log) → t2 (maskIn o a) = some d →
      newBad bad L (⟨t1, auxIn o, a⟩ :: ⟨t0, outerIn, o⟩ :: log) = true)
    (out : Result Input Digest Key Block (Program Input Digest Key Block A))
    (hout : out ∈ (runFixed procedure family 3
      (.hash outerIn fun o => .hash (auxIn o) fun a => .hash (maskIn o a) fun m => .done (k o a m))
      t0 hashes ciphers log).support) :
    newBad bad L out.trace = true ∨
    ∃ o a m : Digest,
      let t1 := Function.update t0 outerIn (some o)
      let t2 := Function.update t1 (auxIn o) (some a)
      out.state = .done (k o a m) ∧
      out.hashTable = Function.update t2 (maskIn o a) (some m) ∧
      out.trace = ⟨t2, maskIn o a, m⟩ :: ⟨t1, auxIn o, a⟩ :: ⟨t0, outerIn, o⟩ :: log := by
  cases h0 : t0 outerIn with
  | some d => exact Or.inl (runFixed_newBad procedure family bad L 3 _ t0 hashes ciphers log out hout (houter d h0))
  | none =>
    obtain ⟨o, out1, hout1, heq1⟩ := runFixed_hash_fresh_support family 2 outerIn _ t0 hashes ciphers log h0 out hout
    have htr1 := traced_update t0 log outerIn o htraced h0
    cases h1 : Function.update t0 outerIn (some o) (auxIn o) with
    | some d =>
      refine Or.inl ?_
      rw [heq1, (mark_fields _ _).2.2.2.2]
      exact runFixed_newBad procedure family bad L 2 _ _ _ ciphers _ out1 hout1 (haux o _ d htr1 h1)
    | none =>
      obtain ⟨a, out2, hout2, heq2⟩ := runFixed_hash_fresh_support family 1 (auxIn o) _ _ _ ciphers _ h1 out1 hout1
      have htr2 := traced_update _ _ (auxIn o) a htr1 h1
      cases h2 : Function.update (Function.update t0 outerIn (some o)) (auxIn o) (some a) (maskIn o a) with
      | some d =>
        refine Or.inl ?_
        rw [heq1, (mark_fields _ _).2.2.2.2, heq2, (mark_fields _ _).2.2.2.2]
        exact runFixed_newBad procedure family bad L 1 _ _ _ ciphers _ out2 hout2 (hmask o a _ _ d htr2 h2)
      | none =>
        obtain ⟨m, out3, hout3, heq3⟩ := runFixed_hash_fresh_support family 0 (maskIn o a) _ _ _ ciphers _ h2 out2 hout2
        have h3 := runFixed_zero_support family (k o a m) _ _ ciphers _ out3 hout3
        refine Or.inr ⟨o, a, m, ?_, ?_, ?_⟩
        · rw [heq1, (mark_fields _ _).1, heq2, (mark_fields _ _).1, heq3, (mark_fields _ _).1, h3]
        · rw [heq1, (mark_fields _ _).2.1, heq2, (mark_fields _ _).2.1, heq3, (mark_fields _ _).2.1, h3]
        · rw [heq1, (mark_fields _ _).2.2.2.2, heq2, (mark_fields _ _).2.2.2.2, heq3, (mark_fields _ _).2.2.2.2, h3]

end Generic

variable {lambda tau : Nat} {M : Type*}

/-- After the outer query, a stored auxiliary query of the outer answer raises
the relative event. -/
theorem aux_stored_mentionN (L : List (Entry (List Bool) (Digest lambda × M)))
    (table : List Bool → Option (Digest lambda × M)) (outerEntry : Entry (List Bool) (Digest lambda × M))
    (older : List (Entry (List Bool) (Digest lambda × M))) (hL : L.length ≤ older.length)
    (htraced : Traced table (outerEntry :: older)) (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda)
    (houter : outerEntry.input = outerString salt rowHashes) (tail : List Bool) (d : Digest lambda × M)
    (hstored : table (auxQuery outerEntry.answer.1 tail) = some d) :
    newBad (digestMention (mentions lambda tau)) L (outerEntry :: older) = true :=
  newBad_head _ L older outerEntry hL (prefixBadN_of_stored_head (mentions lambda tau) table outerEntry older htraced _ d
    hstored (by rw [houter]; exact prefix_ne 2 1 (by decide) _ _) (root_mem_mentions outerEntry.answer.1 tail) _)

/-- After the auxiliary query, a stored mask input of the auxiliary answer
raises the relative event. -/
theorem mask_stored_mentionN (L : List (Entry (List Bool) (Digest lambda × M)))
    (table : List Bool → Option (Digest lambda × M)) (auxEntry : Entry (List Bool) (Digest lambda × M))
    (older : List (Entry (List Bool) (Digest lambda × M))) (hL : L.length ≤ older.length)
    (htraced : Traced table (auxEntry :: older)) (root : Digest lambda) (tail : List Bool)
    (haux : auxEntry.input = auxQuery root tail) (d : Digest lambda × M)
    (hstored : table (maskInput auxEntry.answer.1) = some d) :
    newBad (digestMention (mentions lambda tau)) L (auxEntry :: older) = true :=
  newBad_head _ L older auxEntry hL (prefixBadN_of_stored_head (mentions lambda tau) table auxEntry older htraced _ d
    hstored (by rw [haux]; exact (auxQuery_ne_maskInput root auxEntry.answer.1 tail).symm)
    (auxiliary_mem_mentions auxEntry.answer.1) _)

variable {N : Nat}

/-- After the last row query, a stored outer string over the recorded row
hashes raises the relative event. -/
theorem outer_stored_mentionN (hl : 0 < lambda) (L : List (Entry (List Bool) (Digest lambda × M)))
    (table : List Bool → Option (Digest lambda × M)) (rowEntry : Entry (List Bool) (Digest lambda × M))
    (older : List (Entry (List Bool) (Digest lambda × M))) (hL : L.length ≤ older.length)
    (htraced : Traced table (rowEntry :: older)) (commits : Spec.BAVCBinding.Commitments lambda tau N) (e : Fin tau)
    (hrow : rowEntry.input = Spec.BAVCBinding.rowQuery commits e) (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda)
    (hanswer : rowHashes e = rowEntry.answer.1) (d : Digest lambda × M)
    (hstored : table (outerString salt rowHashes) = some d) :
    newBad (digestMention (mentions lambda tau)) L (rowEntry :: older) = true :=
  newBad_head _ L older rowEntry hL (prefixBadN_of_stored_head (mentions lambda tau) table rowEntry older htraced _ d hstored
    (by rw [hrow]; exact outerString_ne_rowQuery hl salt rowHashes commits e)
    (by rw [← hanswer]; exact rowHash_mem_mentions salt rowHashes e) _)

variable {kappa s wit rnd : Nat}

/-- The prefix's last three queries from a head result: either the relative
event is raised on the run's trace, or the run finishes with the three
answers and a stored lines input raises the relative event. -/
theorem prefixTail_or_mentionN {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (head : HeadData lambda tau kappa)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (L : List (Entry (List Bool) (Out lambda s wit rnd)))
    (t0 : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Entry (List Bool) (Out lambda s wit rnd))) (hL : L.length ≤ log.length)
    (htraced : Traced t0 log) (hord : Ordered log) (hfresh : Fresh log) (hext : ∀ entry ∈ log, Extends entry.before t0)
    (hstored : ∀ entry ∈ log, t0 entry.input = some entry.answer)
    (houter : ∀ d, t0 (outerString salt head.2.2) = some d → newBad (digestMention (mentions lambda tau)) L log = true)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s wit rnd)))
    (hout : out ∈ (runFixed procedure family 3 (prefixTail S salt head) t0 hashes ciphers log).support) :
    newBad (digestMention (mentions lambda tau)) L out.trace = true ∨
      ∃ o a m : Out lambda s wit rnd, out.state = .done (head.1, head.2.1, head.2.2, o, a, m) ∧
        ∀ (tail : List Bool) (d : Out lambda s wit rnd), out.hashTable (linesQuery a.1 tail) = some d →
          newBad (digestMention (mentions lambda tau)) L out.trace = true := by
  rcases three_hash_or_mentionN family (digestMention (mentions lambda tau)) L (outerString salt head.2.2)
      (auxInputOf S salt head) (fun _ a => maskInput a.1) (fun o a m => (head.1, head.2.1, head.2.2, o, a, m))
      t0 hashes ciphers log htraced houter
      (fun o t1 d htr h => aux_stored_mentionN L t1 ⟨t0, outerString salt head.2.2, o⟩ log hL htr salt head.2.2 rfl
        (auxTailOf S salt head) d h)
      (fun o a t1 t2 d htr h => mask_stored_mentionN L t2 ⟨t1, auxInputOf S salt head o, a⟩ _
        (by simp only [List.length_cons]; omega) htr o.1 (auxTailOf S salt head) (auxInputOf_eq S salt head o) d h)
      out hout with h | ⟨o, a, m, hstate, _, htrace⟩
  · exact Or.inl h
  · obtain ⟨htr, _, _, _, _, _⟩ := HashCipherTrace.run_invariants procedure family 3 (prefixTail S salt head) t0 hashes
      ciphers log out hout htraced hord hfresh hext hstored
    refine Or.inr ⟨o, a, m, hstate, fun tail d hd => ?_⟩
    rw [htrace] at htr ⊢
    refine newBad_two _ L _ _ _ (by simp only [List.length_cons]; omega) ?_
    exact prefixBadN_of_stored (mentions lambda tau) out.hashTable _ _ _ htr (linesQuery a.1 tail) d hd
      (linesQuery_ne_maskInput a.1 a.1 tail) (linesQuery_ne_auxQuery a.1 o.1 tail _)
      (auxiliary_mem_mentions_lines a.1 tail) _

end
end SDitH.Proofs.NewMentionChain
