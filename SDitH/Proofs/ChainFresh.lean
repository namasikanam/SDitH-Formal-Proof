import SDitH.Proofs.StoredLinesMention
import SDitH.Proofs.QueryPrefixes

/-! The chain queries' freshness as mention events. A stored input whose
entry is older than the newest entry and which mentions the newest answer
raises the mention event; so, after the outer query, a stored auxiliary
query of the outer answer is a mention of that answer, and after the
auxiliary query a stored mask input of the auxiliary answer is a mention
of that answer. Under the negation of the charged mention event, the
auxiliary and mask inputs are therefore fresh when the prefix asks them. -/

namespace SDitH.Proofs.ChainFresh

open Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.BAVCChainInputs Spec.BLCHashChain
open Spec.DomainSeparation Spec.BAVC
open SDitH.Proofs.BAVCChainInputs QueryPrefixes
open scoped Classical

variable {Input D M : Type*}

/-- A stored input whose entry is older than the newest entry and which
mentions the newest answer raises the mention event. -/
theorem prefixBad_of_stored_head (mentions : Input → Finset D) (table : Input → Option (D × M))
    (newest : Entry Input (D × M)) (older : List (Entry Input (D × M))) (htraced : Traced table (newest :: older))
    (L : Input) (d : D × M) (hstored : table L = some d) (hne : L ≠ newest.input)
    (hmention : newest.answer.1 ∈ mentions L) :
    prefixBad (digestMention mentions) (newest :: older) = true := by
  obtain ⟨entry, hentry, hinput, _, _, _⟩ := htraced.1 L d hstored
  have holder : entry ∈ older := by
    simp only [List.mem_cons] at hentry
    rcases hentry with h | h
    · exact absurd (by rw [← hinput, h]) hne
    · exact h
  have hhead : digestMention mentions older newest.input newest.answer = true := by
    unfold digestMention
    rw [List.any_eq_true]
    exact ⟨entry, holder, by rw [hinput]; exact decide_eq_true hmention⟩
  simp only [prefixBad, hhead, Bool.true_or]

variable {lambda tau : Nat}

/-- The auxiliary query is never the mask input: their lengths differ. -/
theorem auxQuery_ne_maskInput (root auxiliary : Digest lambda) (tail : List Bool) :
    auxQuery root tail ≠ maskInput auxiliary := by
  intro h
  have hlen := congrArg List.length h
  simp only [auxQuery, maskInput, List.length_append, List.length_ofFn, byteBits_length] at hlen
  omega

/-- After the outer query, a stored auxiliary query of the outer answer is a
mention event. -/
theorem aux_stored_mention (table : List Bool → Option (Digest lambda × M)) (outerEntry : Entry (List Bool) (Digest lambda × M))
    (older : List (Entry (List Bool) (Digest lambda × M))) (htraced : Traced table (outerEntry :: older))
    (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda) (houter : outerEntry.input = outerString salt rowHashes)
    (tail : List Bool) (d : Digest lambda × M) (hstored : table (auxQuery outerEntry.answer.1 tail) = some d) :
    prefixBad (digestMention (mentions lambda tau)) (outerEntry :: older) = true :=
  prefixBad_of_stored_head (mentions lambda tau) table outerEntry older htraced _ d hstored
    (by rw [houter]; exact prefix_ne 2 1 (by decide) _ _) (root_mem_mentions outerEntry.answer.1 tail)

/-- After the auxiliary query, a stored mask input of the auxiliary answer is
a mention event. -/
theorem mask_stored_mention (table : List Bool → Option (Digest lambda × M)) (auxEntry : Entry (List Bool) (Digest lambda × M))
    (older : List (Entry (List Bool) (Digest lambda × M))) (htraced : Traced table (auxEntry :: older))
    (root : Digest lambda) (tail : List Bool) (haux : auxEntry.input = auxQuery root tail)
    (d : Digest lambda × M) (hstored : table (maskInput auxEntry.answer.1) = some d) :
    prefixBad (digestMention (mentions lambda tau)) (auxEntry :: older) = true :=
  prefixBad_of_stored_head (mentions lambda tau) table auxEntry older htraced _ d hstored
    (by rw [haux]; exact (auxQuery_ne_maskInput root auxEntry.answer.1 tail).symm) (auxiliary_mem_mentions auxEntry.answer.1)

end SDitH.Proofs.ChainFresh
