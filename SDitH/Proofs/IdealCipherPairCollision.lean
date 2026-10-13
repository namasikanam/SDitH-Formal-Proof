import SDitH.Spec.IdealCipherPairCollision
import SDitH.Proofs.IdealCipherComparison

namespace SDitH.Proofs.IdealCipherPairCollision

open Spec.IdealCipher Spec.IdealCipherPairCollision
open scoped Classical ENNReal
noncomputable section

variable {Key Block Tag : Type*}

theorem unseen_iff (history : List (Entry Key Block)) (key : Key) (input : Block) :
    Unseen history key input ↔ ¬ ∃ e ∈ history, e.key = key ∧ e.input = input := by
  simp only [Unseen]
  push_neg
  rfl

theorem witness_symm (project : Block → Tag) (companion : Block → Block)
    (family : Family Key Block) (left right : Entry Key Block)
    (h : PairWitness project companion family left right) :
    PairWitness project companion family right left := by
  exact ⟨Ne.symm h.1, h.2.1.symm, h.2.2.1.symm, by simpa only [← h.2.1] using h.2.2.2.symm⟩

theorem witnessed_mono (project : Block → Tag) (companion : Block → Block)
    (family : Family Key Block) (left right : List (Entry Key Block)) (hsub : left ⊆ right)
    (h : Witnessed project companion family left) : Witnessed project companion family right := by
  obtain ⟨a, ha, b, hb, hw⟩ := h
  exact ⟨a, hsub ha, b, hsub hb, hw⟩

/-- A first matching half must leave a companion input unobserved. If both
companions were already known, they form an earlier matching half instead.
This handles arbitrary query order, including inverse queries and repeats. -/
theorem new_witness_first (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (family : Family Key Block) (history : List (Entry Key Block)) (newest old : Entry Key Block)
    (hmatches : Matches family (newest :: history)) (hold : old ∈ history)
    (hpair : PairWitness project companion family newest old)
    (hprevious : ¬ Witnessed project companion family history) :
    FirstPair project companion family history newest old := by
  have hfresh : Unseen history newest.key newest.input := by
    rw [unseen_iff]
    rintro ⟨e, he, hk, hi⟩
    have hout : e.output = newest.output := by
      rw [← hmatches e (List.mem_cons_of_mem _ he), hk, hi]
      exact hmatches newest List.mem_cons_self
    apply hprevious
    refine ⟨e, he, old, hold, ?_⟩
    simpa only [PairWitness, hk, hi, hout] using hpair
  refine ⟨hfresh, hpair, ?_⟩
  by_contra hnot
  have hboth := not_or.mp hnot
  have hleftMissing := hboth.1
  have hrightMissing := hboth.2
  rw [unseen_iff, not_not] at hleftMissing hrightMissing
  obtain ⟨left, hl, hlk, hli⟩ := hleftMissing
  obtain ⟨right, hr, hrk, hri⟩ := hrightMissing
  have hleft : left ∈ history := by
    rcases List.mem_cons.mp hl with he | he
    · subst left
      exact False.elim (hnofix newest.input hli.symm)
    · exact he
  have hright : right ∈ history := by
    rcases List.mem_cons.mp hr with he | he
    · subst right
      exact False.elim (hpair.1 hrk)
    · exact he
  apply hprevious
  refine ⟨left, hleft, right, hright, ?_⟩
  refine ⟨by simpa only [hlk, hrk] using hpair.1, hli.trans hri.symm, ?_, ?_⟩
  · rw [← hmatches left hl, ← hmatches right hr, hlk, hrk, hli, hri]
    exact hpair.2.2.2
  · rw [hlk, hrk, hli, hinvolution, hmatches newest List.mem_cons_self,
      hpair.2.1, hmatches old (List.mem_cons_of_mem _ hold)]
    exact hpair.2.2.1

theorem witnessed_cons (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (family : Family Key Block) (history : List (Entry Key Block)) (newest : Entry Key Block)
    (hmatches : Matches family (newest :: history))
    (h : Witnessed project companion family (newest :: history)) :
    Witnessed project companion family history ∨
      ∃ old ∈ history, FirstPair project companion family history newest old := by
  by_cases hp : Witnessed project companion family history
  · exact Or.inl hp
  · right
    obtain ⟨left, hl, right, hr, hw⟩ := h
    rcases List.mem_cons.mp hl with rfl | hlold
    · rcases List.mem_cons.mp hr with rfl | hrold
      · exact False.elim (hw.1 rfl)
      · exact ⟨right, hrold, new_witness_first project companion hinvolution hnofix family history _ right hmatches hrold hw hp⟩
    · rcases List.mem_cons.mp hr with rfl | hrold
      · exact ⟨left, hlold, new_witness_first project companion hinvolution hnofix family history _ left hmatches hlold
          (witness_symm project companion family left _ hw) hp⟩
      · exact False.elim (hp ⟨left, hlold, right, hrold, hw⟩)

end
end SDitH.Proofs.IdealCipherPairCollision
