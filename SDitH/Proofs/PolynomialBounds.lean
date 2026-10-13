import SDitH.Spec.PIOP
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! The algebraic ingredients cited in the §2.1 soundness discussion.
These do not establish soundness of the inconsistent literal verifier or of
the signature scheme; that distinction is part of the public coverage ledger. -/

namespace SDitH.Proofs

open scoped Classical

variable {F : Type*} [Field F]

/-- A nonzero residual of degree at most d can vanish at at most d distinct
challenge values. No uniform-challenge or transcript-independence premise is
smuggled into this purely algebraic statement. -/
theorem residual_root_count (p : Polynomial F) (hp : p ≠ 0) (S : Finset F) (d : Nat)
    (hdegree : p.natDegree ≤ d) :
    (S.filter (fun x => p.eval x = 0)).card ≤ d := by
  classical
  apply le_trans (Polynomial.card_le_degree_of_subset_roots ?_) hdegree
  intro x hx
  exact (Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp hx).2

/-- Fixing all other batching coefficients, a nonzero constraint gives exactly
one cancelling value for its coefficient. Counting uniformly sampled challenges
and connecting this to an adaptive protocol remain separate obligations. -/
theorem unique_cancelling_coefficient (a b : F) (ha : a ≠ 0) :
    ∃! γ : F, a * γ + b = 0 := by
  have hroot : a * (-b / a) + b = 0 := by
    field_simp
    ring
  refine ⟨-b / a, hroot, ?_⟩
  intro γ hγ
  apply mul_left_cancel₀ ha
  linear_combination hγ - hroot

end SDitH.Proofs
