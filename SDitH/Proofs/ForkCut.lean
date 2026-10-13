import SDitH.Proofs.BAVCChainInputs
import SDitH.Proofs.OracleChain

/-! Chains across a fork cut. The fork table is a cut of a branch's fresh-
query log: every fresh entry was answered after the cut or is already
stored by it. A stored sink-first chain whose sink is present in the cut
is then entirely present in the cut, or a fresh digest hit a mentioned
value. The verifier's Hashlines string mentions the auxiliary digest, so
the auxiliary, outer and row strings of an accepted verification are
present in the cut whenever its lines string is, up to the mention event.
Whether the lines string itself is in the cut is a separate fixed-target
event, charged later. -/

namespace SDitH.Proofs.ForkCut

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.OracleChain Spec.RandomOracleTrace
open Spec.RandomOracleMention Spec.ProductOracle
open scoped Classical
noncomputable section

variable {lambda tau N : Nat} {M : Type*}

/-- The verifier's Hashlines string. -/
def linesString (auxiliary : Digest lambda) (tail : List Bool) : List Bool :=
  Spec.BLCHashChain.linesQuery auxiliary tail

theorem window_linesString (auxiliary : Digest lambda) (tail : List Bool) :
    window (linesString auxiliary tail) 8 = auxiliary := by
  funext i
  simp only [window, linesString, Spec.BLCHashChain.linesQuery]
  rw [show 8 = (byteBits 3).length from (BAVCChainInputs.byteBits_length 3).symm, BAVCChainInputs.getD_append_right,
    BAVCChainInputs.getD_append_left _ _ _ (by simp [i.isLt]), BAVCChainInputs.getD_ofFn]

theorem auxiliary_mem_mentions_lines (auxiliary : Digest lambda) (tail : List Bool) :
    auxiliary ∈ mentions lambda tau (linesString auxiliary tail) :=
  Finset.mem_image.mpr ⟨8, by simp [offsets], window_linesString auxiliary tail⟩

theorem byteBits_three_ne_two : byteBits 3 ≠ byteBits 2 := by decide

theorem byteBits_three_ne_one : byteBits 3 ≠ byteBits 1 := by decide

theorem linesString_ne_auxString (a : Digest lambda) (t : List Bool) (root : Digest lambda) (tail : List Bool) :
    linesString a t ≠ auxString root tail := by
  intro h
  have ht := congrArg (List.take 8) h
  simp only [linesString, Spec.BLCHashChain.linesQuery, auxString, Spec.BLCHashChain.auxQuery,
    BAVCChainInputs.take_eight] at ht
  exact byteBits_three_ne_two ht

theorem linesString_ne_outerString (a : Digest lambda) (t : List Bool) (salt : Seed lambda)
    (rowHashes : Fin tau → Digest lambda) : linesString a t ≠ outerString salt rowHashes := by
  intro h
  have ht := congrArg (List.take 8) h
  simp only [linesString, Spec.BLCHashChain.linesQuery, outerString, BAVCChainInputs.take_eight] at ht
  exact byteBits_three_ne_one ht

theorem linesString_ne_rowString (a : Digest lambda) (t : List Bool) (row : Fin N → Digest lambda) :
    linesString a t ≠ rowString row := by
  intro h
  have ht := congrArg (List.take 8) h
  simp only [linesString, Spec.BLCHashChain.linesQuery, rowString, BAVCChainInputs.take_eight] at ht
  exact byteBits_three_ne_one ht

theorem chain_linked_lines (salt : Seed lambda) (rows : Fin tau → Fin N → Digest lambda) (rowHashes : Fin tau → Digest lambda)
    (root : Digest lambda) (tail : List Bool) (auxiliary : Digest lambda) (linesTail : List Bool) (e : Fin tau) :
    LinkedTo (mentions lambda tau) (linesString auxiliary linesTail) (chain salt rows rowHashes root tail auxiliary e) ∧
      Linked (mentions lambda tau) (chain salt rows rowHashes root tail auxiliary e) := by
  refine ⟨auxiliary_mem_mentions_lines auxiliary linesTail, ?_⟩
  exact ⟨BAVCChainInputs.root_mem_mentions root tail, BAVCChainInputs.rowHash_mem_mentions salt rowHashes e, trivial⟩

theorem chain_distinct_lines (hlambda : 0 < lambda) (htau : 0 < tau) (hN : 0 < N) (salt : Seed lambda)
    (rows : Fin tau → Fin N → Digest lambda) (rowHashes : Fin tau → Digest lambda)
    (root : Digest lambda) (tail : List Bool) (auxiliary : Digest lambda) (linesTail : List Bool) (e : Fin tau) :
    (∀ p ∈ chain salt rows rowHashes root tail auxiliary e, p.1 ≠ linesString auxiliary linesTail) ∧
      (chain salt rows rowHashes root tail auxiliary e).Pairwise (fun p q => p.1 ≠ q.1) := by
  refine ⟨?_, (BAVCChainInputs.chain_distinct hlambda htau hN salt rows rowHashes root tail auxiliary e).2⟩
  intro p hp
  simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact (linesString_ne_auxString auxiliary linesTail root tail).symm
  · exact (linesString_ne_outerString auxiliary linesTail salt rowHashes).symm
  · exact (linesString_ne_rowString auxiliary linesTail (rows e)).symm

section Cut

variable {Input D : Type*}

/-- The fork table is a cut of the log: every fresh entry was answered
after it, or before it and is stored by it. -/
def Cut (P : Input → Option (D × M)) (log : List (Entry Input (D × M))) : Prop :=
  ∀ entry ∈ log, Extends P entry.before ∨ (Extends entry.before P ∧ P entry.input = some entry.answer)

theorem sink_entry_before_cut (log : List (Entry Input (D × M))) (T P : Input → Option (D × M))
    (htraced : Traced T log) (hcut : Cut P log) (hPT : Extends P T) (sink : Input) (y : D × M)
    (hsink : P sink = some y) : ∃ ey ∈ log, ey.input = sink ∧ Extends ey.before P := by
  obtain ⟨ey, hey, heyi, _, hbefore, _⟩ := htraced.1 sink y (hPT sink y hsink)
  refine ⟨ey, hey, heyi, ?_⟩
  rcases hcut ey hey with hpost | ⟨hpre, _⟩
  · exfalso
    have h1 := hpost sink y hsink
    rw [hbefore] at h1
    cases h1
  · exact hpre

/-- A stored chain whose sink is in the cut is present in the cut, or a
fresh digest hit a mentioned value. -/
theorem chain_present_at_cut (mentions : Input → Finset D) (log : List (Entry Input (D × M)))
    (T P : Input → Option (D × M)) (hord : Ordered log) (hfresh : Fresh log) (htraced : Traced T log)
    (hcut : Cut P log) (hPT : Extends P T) (links : List (Input × D)) (sink : Input)
    (hto : LinkedTo mentions sink links) (hlinked : Linked mentions links)
    (hne : ∀ p ∈ links, p.1 ≠ sink) (hpair : links.Pairwise (fun p q => p.1 ≠ q.1)) (hstored : Stored T links)
    (hsink : (P sink).isSome) :
    Present P links ∨ prefixBad (digestMention mentions) log = true := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsink
  obtain ⟨ey, hey, heyi, hpre⟩ := sink_entry_before_cut log T P htraced hcut hPT sink y hy
  rcases OracleChain.chain_present_or_mention mentions log T hord hfresh htraced links sink hto hlinked hne hpair
    hstored ey hey heyi with hpres | hbad
  · left
    intro p hp
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hpres p hp)
    rw [hpre p.1 v hv]
    rfl
  · exact Or.inr hbad

end Cut

/-- The verifier's chain at a cut: if the lines string is in the cut, every
auxiliary, outer and row string of the accepted verification is in the
cut, or a fresh digest hit a mentioned value. -/
theorem verification_chain_at_cut (hlambda : 0 < lambda) (htau : 0 < tau) (hN : 0 < N)
    (log : List (Entry (List Bool) (Digest lambda × M))) (T P : List Bool → Option (Digest lambda × M))
    (hord : Ordered log) (hfresh : Fresh log) (htraced : Traced T log) (hcut : Cut P log) (hPT : Extends P T)
    (salt : Seed lambda) (rows : Fin tau → Fin N → Digest lambda) (rowHashes : Fin tau → Digest lambda)
    (root : Digest lambda) (tail : List Bool) (auxiliary : Digest lambda) (linesTail : List Bool)
    (hrows : ∀ e, ∃ pair, T (rowString (rows e)) = some pair ∧ pair.1 = rowHashes e)
    (houter : ∃ pair, T (outerString salt rowHashes) = some pair ∧ pair.1 = root)
    (haux : ∃ pair, T (auxString root tail) = some pair ∧ pair.1 = auxiliary)
    (hlines : (P (linesString auxiliary linesTail)).isSome) :
    ((∀ e, (P (rowString (rows e))).isSome) ∧ (P (outerString salt rowHashes)).isSome ∧
        (P (auxString root tail)).isSome) ∨
      prefixBad (digestMention (mentions lambda tau)) log = true := by
  by_cases hbad : prefixBad (digestMention (mentions lambda tau)) log = true
  · exact Or.inr hbad
  left
  have hall : ∀ e : Fin tau, Present P (chain salt rows rowHashes root tail auxiliary e) := by
    intro e
    obtain ⟨hto, hlinked⟩ := chain_linked_lines salt rows rowHashes root tail auxiliary linesTail e
    obtain ⟨hne, hpair⟩ := chain_distinct_lines hlambda htau hN salt rows rowHashes root tail auxiliary linesTail e
    have hstored : Stored T (chain salt rows rowHashes root tail auxiliary e) := by
      intro p hp
      simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact haux
      · exact houter
      · exact hrows e
    rcases chain_present_at_cut (mentions lambda tau) log T P hord hfresh htraced hcut hPT
      (chain salt rows rowHashes root tail auxiliary e) (linesString auxiliary linesTail) hto hlinked hne hpair
      hstored hlines with hpresent | hbad'
    · exact hpresent
    · exact absurd hbad' hbad
  obtain ⟨e0, _⟩ : ∃ e : Fin tau, True := ⟨⟨0, htau⟩, trivial⟩
  exact ⟨fun e => hall e (rowString (rows e), rowHashes e) (by simp [chain]),
    hall e0 (outerString salt rowHashes, root) (by simp [chain]),
    hall e0 (auxString root tail, auxiliary) (by simp [chain])⟩

end
end SDitH.Proofs.ForkCut
