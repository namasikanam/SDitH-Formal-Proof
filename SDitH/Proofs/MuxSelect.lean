import SDitH.Spec.PIOPArithmetic
import SDitH.Spec.UnitaryPolynomial
import SDitH.Spec.Syndrome

/-! The mux tree with unitary binary selectors selects one leaf: a layer
whose stored coordinates have at most one nonzero entry picks that entry's
successor column (or the default column when all are zero), and the tree
composes the layers' columns into a leaf address. -/

namespace SDitH.Proofs.MuxSelect

open Spec.PIOPArithmetic Spec.UnitaryPolynomial
open scoped BigOperators Classical

noncomputable section

/-- The column selected by one layer's binary coordinates. -/
def selectCol {r : Nat} (bits : Fin r → ZMod 2) : Fin (r + 1) :=
  if h : ∃ k, bits k ≠ 0 then (Classical.choose h).succ else 0

/-- The leaf address selected by a chunk's selectors. -/
def selectAddress : (widths : List Nat) → Selectors (ZMod 2) widths → Fin (leafCount widths)
  | [], _ => ⟨0, by decide⟩
  | _ :: rest, selectors => blockIndex (selectAddress rest selectors.2) (selectCol selectors.1)

/-- Every layer has at most one nonzero coordinate. -/
def AllAtMostOne : (widths : List Nat) → Selectors (ZMod 2) widths → Prop
  | [], _ => True
  | _ :: rest, selectors => AtMostOne selectors.1 ∧ AllAtMostOne rest selectors.2

theorem allAtMostOne_of_selectorAt : ∀ (widths : List Nat) (selectors : Selectors (ZMod 2) widths),
    (∀ j : Fin widths.length, AtMostOne (selectorAt widths selectors j)) → AllAtMostOne widths selectors
  | [], _, _ => trivial
  | r :: rest, selectors, h =>
    ⟨by simpa [selectorAt] using h ⟨0, by simp⟩,
      allAtMostOne_of_selectorAt rest selectors.2 fun j => by simpa [selectorAt] using h j.succ⟩

theorem zmod_two_eq_one_of_ne_zero (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

/-- A binary layer with at most one nonzero coordinate selects its column. -/
theorem mux_select {r : Nat} (bits : Fin r → ZMod 2) (hone : AtMostOne bits) (values : Fin (r + 1) → ZMod 2) :
    mux bits values = values (selectCol bits) := by
  unfold mux selectCol
  by_cases h : ∃ k, bits k ≠ 0
  · rw [dif_pos h]
    have hchoose : bits (Classical.choose h) ≠ 0 := Classical.choose_spec h
    have hsum : ∑ k, bits k * (values k.succ - values 0) =
        bits (Classical.choose h) * (values (Classical.choose h).succ - values 0) := by
      rw [Finset.sum_eq_single (Classical.choose h)]
      · intro k _ hk
        have hzero : bits k = 0 := by
          by_contra hne
          exact hk (hone k (Classical.choose h) hne hchoose)
        rw [hzero, zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hsum, zmod_two_eq_one_of_ne_zero _ hchoose, one_mul]
    ring
  · rw [dif_neg h]
    push_neg at h
    simp [h]

/-- The mux tree with unitary binary selectors reads the selected leaf. -/
theorem muxTree_select : ∀ (widths : List Nat) (selectors : Selectors (ZMod 2) widths)
    (_hsel : AllAtMostOne widths selectors) (leaves : Fin (leafCount widths) → ZMod 2),
    muxTree widths selectors leaves = leaves (selectAddress widths selectors)
  | [], _, _, leaves => rfl
  | _ :: rest, selectors, hsel, leaves => by
    simp only [muxTree, selectAddress]
    rw [muxTree_select rest selectors.2 hsel.2, mux_select selectors.1 hsel.1]

end
end SDitH.Proofs.MuxSelect
