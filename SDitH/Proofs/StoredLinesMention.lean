import SDitH.Proofs.ThreeHashShape
import SDitH.Proofs.LinesMention
import SDitH.Proofs.QueryPrefixes
import SDitH.Spec.ProductOracle
import SDitH.Spec.RandomOracleMention

/-! A stored lines input is a mention event. After the prefix's final three
fresh queries, the trace is the mask, auxiliary and outer entries over the
older entries, and the table traces its stored inputs to entries. A lines
input stored at tail time differs from the three newest entries' inputs,
so its entry is older than the auxiliary query's, and it mentions the
auxiliary digest; hence the auxiliary answer is mentioned by an older
input, which is the mention event already charged in the composed bound.
Under the negation of that event the lines input is fresh, whatever the
witness. -/

namespace SDitH.Proofs.StoredLinesMention

open Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.BAVCChainInputs Spec.BLCHashChain
open Spec.DomainSeparation Spec.BAVC
open scoped Classical

variable {Input D M : Type*}

/-- A stored input whose entry is older than a recorded answer that it
mentions raises the mention event. -/
theorem prefixBad_of_stored (mentions : Input → Finset D) (table : Input → Option (D × M))
    (newest : Entry Input (D × M)) (auxEntry : Entry Input (D × M)) (older : List (Entry Input (D × M)))
    (htraced : Traced table (newest :: auxEntry :: older)) (L : Input) (d : D × M) (hstored : table L = some d)
    (hne1 : L ≠ newest.input) (hne2 : L ≠ auxEntry.input) (hmention : auxEntry.answer.1 ∈ mentions L) :
    prefixBad (digestMention mentions) (newest :: auxEntry :: older) = true := by
  obtain ⟨entry, hentry, hinput, _, _, _⟩ := htraced.1 L d hstored
  have holder : entry ∈ older := by
    simp only [List.mem_cons] at hentry
    rcases hentry with h | h | h
    · exact absurd (by rw [← hinput, h]) hne1
    · exact absurd (by rw [← hinput, h]) hne2
    · exact h
  have hmid : digestMention mentions older auxEntry.input auxEntry.answer = true := by
    unfold digestMention
    rw [List.any_eq_true]
    exact ⟨entry, holder, by rw [hinput]; exact decide_eq_true hmention⟩
  simp only [prefixBad, hmid, Bool.true_or, Bool.or_true]

end SDitH.Proofs.StoredLinesMention
