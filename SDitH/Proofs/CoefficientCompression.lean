import SDitH.Spec.CoefficientCompression
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

namespace SDitH.Proofs.CoefficientCompression

open Spec Spec.CoefficientCompression Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

theorem hashed_succ (n : Nat) (p : F[X]) (j : Fin n) :
    hashedCoefficients n p j.succ = transmittedCoefficients n p j := rfl

theorem evaluation_split (n : Nat) (p : F[X]) (hp : p.natDegree ≤ n + 1) (delta : F) :
    p.eval delta = p.coeff 0 + p.coeff 1 * delta +
      higherEvaluation (transmittedCoefficients n p) delta := by
  rw [eval_eq_sum_range' (show p.natDegree < n + 1 + 1 by omega)]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, mul_one, zero_add, pow_one]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [higherEvaluation, transmittedCoefficients]
  ring

/-- Recovery exposes the omitted constant term: the reconstructed alpha_1
differs by delta^(-1)*alpha_0. This is exact for every degree-bounded polynomial. -/
theorem restored_first (n : Nat) (p : F[X]) (hp : p.natDegree ≤ n + 1)
    (delta : F) (hdelta : delta ≠ 0) :
    restoredCoefficients delta (p.eval delta) (transmittedCoefficients n p) 0 =
      p.coeff 1 + delta⁻¹ * p.coeff 0 := by
  simp only [restoredCoefficients, Fin.cons_zero, recoverAlphaOne, evaluation_split n p hp delta]
  field_simp
  ring

/-- The exact condition for Algorithms 3/4 to hash the same coefficient tuple
when their polynomial evaluations agree. No collision property is assumed. -/
theorem restored_eq_hashed_iff (n : Nat) (p : F[X]) (hp : p.natDegree ≤ n + 1)
    (delta : F) (hdelta : delta ≠ 0) :
    restoredCoefficients delta (p.eval delta) (transmittedCoefficients n p) =
      hashedCoefficients n p ↔ p.coeff 0 = 0 := by
  constructor
  · intro h
    have he := congrFun h 0
    rw [restored_first n p hp delta hdelta] at he
    change p.coeff 1 + delta⁻¹ * p.coeff 0 = p.coeff 1 at he
    have hz : delta⁻¹ * p.coeff 0 = 0 := add_left_cancel
      (show p.coeff 1 + delta⁻¹ * p.coeff 0 = p.coeff 1 + 0 by simpa using he)
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hdelta)
  · intro hz
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [restored_first n p hp delta hdelta, hz, mul_zero, add_zero]
      rfl
    · rfl

theorem coefficientPolynomial_zero {d : Nat} (coefficients : Fin d → F) :
    (coefficientPolynomial coefficients).eval 0 = 0 := by
  simp [coefficientPolynomial, eval_finset_sum]

/-- Hashing/transmitting only positive-degree coefficients represents p with
its constant term removed, assuming the stated source degree limit. -/
theorem coefficientPolynomial_hashed (n : Nat) (p : F[X]) (hp : p.natDegree ≤ n + 1) :
    coefficientPolynomial (hashedCoefficients n p) = p - C (p.coeff 0) := by
  conv_rhs =>
    lhs
    rw [p.as_sum_range_C_mul_X_pow' (show p.natDegree < n + 1 + 1 by omega)]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one, ← Fin.sum_univ_eq_sum_range]
  simp only [coefficientPolynomial, hashedCoefficients]
  ring

end SDitH.Proofs.CoefficientCompression
