import SDitH.Spec.PIOPArithmetic
import SDitH.Spec.Syndrome
import Mathlib.Tactic

namespace SDitH.Proofs.PIOPEncodingDiscrepancies

open Spec Spec.PIOPArithmetic Polynomial
open scoped BigOperators

/-- A valid stored arity-three selector represents the first elementary vector. -/
theorem selector_example :
    completeSelector (F := ZMod 2) ![1, 0] = ![1, 0, 0] := by
  ext i
  fin_cases i <;> decide

/-- The printed mux returns the second coordinate for the very same selector.
This refutes the claimed equality with the tensor-factor dot product unless an
additional coordinate permutation is specified. -/
theorem mux_disagrees_with_tensor_factor :
    mux (R := ZMod 2) ![1, 0] ![1, 0, 0] ≠
      dotProduct (completeSelector (F := ZMod 2) ![1, 0]) ![1, 0, 0] := by
  rw [selector_example]
  norm_num [mux, dotProduct, Fin.sum_univ_succ]

variable {F : Type*} [Field F]

/-- Algorithm 15 applied to two degree-at-most-one polynomials with valid zero
witness bits produces `X²-X`, not a degree-at-most-one polynomial. -/
theorem unitary_example (ξ : F) :
    unitaryCheck (C ξ) ![(X : F[X]), 0] = X ^ 2 - X := by
  simp [unitaryCheck, Fin.sum_univ_succ, pow_two]

/-- The annotation in Algorithm 15 is false even though both witness bits are
zero and the output constant term is zero. -/
theorem unitary_degree_annotation_counterexample (ξ : F) :
    (∀ i : Fin 2, (![(X : F[X]), 0] i).eval 0 = 0) ∧
    (unitaryCheck (C ξ) ![(X : F[X]), 0]).eval 0 = 0 ∧
    (unitaryCheck (C ξ) ![(X : F[X]), 0]).natDegree = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp
  · rw [unitary_example]
    simp
  · rw [unitary_example, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp

end SDitH.Proofs.PIOPEncodingDiscrepancies
