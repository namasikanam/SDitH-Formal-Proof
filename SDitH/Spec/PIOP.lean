import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
Literal mathematical definitions from SDitH v3.0 §2.1, printed pp. 3–4.
The mismatch between equations (1) and (2) is intentionally preserved.
This module contains definitions, not security assumptions or proof claims.
-/

namespace SDitH.Spec.PIOP

open Polynomial
open scoped BigOperators

variable {F : Type*} [CommRing F] {n m : ℕ}

/-- The public polynomial constraints `fj(w) = 0` on printed p. 3. -/
def ValidWitness (f : Fin m → MvPolynomial (Fin n) F) (w : Fin n → F) : Prop :=
  ∀ j, MvPolynomial.eval w (f j) = 0

/-- Admissibility of honest algebraic inputs on printed p. 3: positive protocol
degree, binary valid witness, degree-at-most-one committed lines with the prescribed
constant coefficients, degree-at-most-d constraints, and the masking degree bound.
Randomness and commitment realizations are not assumed by this predicate. -/
def HonestInputs (d : Nat) (f : Fin m → MvPolynomial (Fin n) F)
    (w : Fin n → F) (P : Fin n → F[X]) (P₀ : F[X]) : Prop :=
  0 < d ∧ ValidWitness f w ∧
  (∀ i, w i = 0 ∨ w i = 1) ∧
  (∀ i, (P i).eval 0 = w i) ∧
  (∀ i, (P i).natDegree ≤ 1) ∧
  (∀ j, (f j).totalDegree ≤ d) ∧
  P₀.natDegree ≤ d - 1

/-- Substitute the committed univariate polynomials into a public constraint. -/
noncomputable def substitute (f : MvPolynomial (Fin n) F)
    (P : Fin n → F[X]) : F[X] :=
  MvPolynomial.eval₂ Polynomial.C P f

/-- Equation (1), with the factor `X` on the masking polynomial. -/
noncomputable def proverPolynomial (f : Fin m → MvPolynomial (Fin n) F)
    (γ : Fin m → F) (P : Fin n → F[X]) (P₀ : F[X]) : F[X] :=
  P₀ * X + ∑ j, C (γ j) * substitute (f j) P

/-- The right side of the second check in equation (2). -/
def verifierRhs (f : Fin m → MvPolynomial (Fin n) F) (γ : Fin m → F)
    (Δ v₀ : F) (v : Fin n → F) : F :=
  v₀ * Δ + ∑ j, γ j * MvPolynomial.eval v (f j)

/-- Equation (2) literally, including the extra factor `Δ` on the left. -/
def literalVerifier (f : Fin m → MvPolynomial (Fin n) F) (γ : Fin m → F)
    (Pα : F[X]) (Δ v₀ : F) (v : Fin n → F) : Prop :=
  Pα.eval 0 = 0 ∧ Pα.eval Δ * Δ = verifierRhs f γ Δ v₀ v

/-- Honest openings of exactly the polynomials in equation (1). -/
noncomputable def honestLiteralAccepts (f : Fin m → MvPolynomial (Fin n) F)
    (γ : Fin m → F) (P : Fin n → F[X]) (P₀ : F[X]) (Δ : F) : Prop :=
  literalVerifier f γ (proverPolynomial f γ P P₀) Δ (P₀.eval Δ)
    (fun i => (P i).eval Δ)

end SDitH.Spec.PIOP
