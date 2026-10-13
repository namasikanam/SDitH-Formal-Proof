import SDitH.Spec.Syndrome
import Mathlib.Tactic

namespace SDitH.Proofs

open Spec

variable {F : Type*} [Field F] {J : Type*} [Fintype J] {I : J → Type*}

/-- The tensor product of elementary vectors is elementary, as used in §2.2.
This proves the mathematical product-index claim, without resolving the PDF's
inconsistent flat vector dimensions or coordinate order. -/
theorem tensor_elementary (positions : (j : J) → I j) :
    tensor (F := F) (fun j => elementary (positions j)) = elementary positions := by
  classical
  funext coordinate
  by_cases h : coordinate = positions
  · subst coordinate
    simp [tensor, elementary]
  · have he : ∃ j, coordinate j ≠ positions j := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨j, hj⟩ := he
    simp only [elementary, if_neg h, tensor]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact if_neg hj

end SDitH.Proofs
