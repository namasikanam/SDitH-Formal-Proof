import SDitH.Spec.PIOP
import Mathlib.Tactic

namespace SDitH.Proofs

open Polynomial SDitH.Spec.PIOP
open scoped BigOperators

variable {F : Type*} [CommRing F] {n m : ℕ}

/-- Polynomial substitution commutes with evaluation. -/
theorem eval_substitute (f : MvPolynomial (Fin n) F) (P : Fin n → F[X]) (Δ : F) :
    (substitute f P).eval Δ = MvPolynomial.eval (fun i => (P i).eval Δ) f := by
  unfold substitute
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i hp => simp [MvPolynomial.eval₂_mul, hp]

/-- The evaluation identity that actually follows from equation (1).
Unlike literal equation (2), its left side has no extra factor `Δ`.
This lemma does not silently redefine the literal verifier. -/
theorem prover_evaluation (f : Fin m → MvPolynomial (Fin n) F)
    (γ : Fin m → F) (P : Fin n → F[X]) (P₀ : F[X]) (Δ : F) :
    (proverPolynomial f γ P P₀).eval Δ =
      verifierRhs f γ Δ (P₀.eval Δ) (fun i => (P i).eval Δ) := by
  simp [proverPolynomial, verifierRhs, Polynomial.eval_finset_sum, eval_substitute]

/-- Equation (3): a valid witness makes the honest constant coefficient zero. -/
theorem prover_constant_zero (f : Fin m → MvPolynomial (Fin n) F)
    (γ : Fin m → F) (P : Fin n → F[X]) (P₀ : F[X])
    (h : ValidWitness f (fun i => (P i).eval 0)) :
    (proverPolynomial f γ P P₀).eval 0 = 0 := by
  rw [prover_evaluation]
  simp [verifierRhs, ValidWitness] at h ⊢
  exact Finset.sum_eq_zero (fun j _ => by rw [h j, mul_zero])

end SDitH.Proofs
