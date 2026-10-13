import SDitH.Spec.PIOPArithmetic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! The binary-selector polynomial D(Y) on printed p. 32 and its packed
polynomial on pp. 32–33. The variable here is Y, not the witness-line variable X
of Algorithms 15/16. No basis or soundness property is assumed. -/

namespace SDitH.Spec.UnitaryPolynomial

open Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable def check {r : Nat} (bits : Fin r → R) : R[X] :=
  PIOPArithmetic.unitaryCheck X (fun k => C (bits k))

def exponent {r : Nat} (p : Fin r × Fin (r - 1)) : Nat := p.1.val + r * p.2.val

noncomputable def crossTerms {r : Nat} (bits : Fin r → R) : R[X] :=
  ∑ p : Fin r × Fin (r - 1),
    monomial (exponent p) (bits p.1 * bits (p.2.castLE (Nat.sub_le r 1)))

noncomputable def diagonalTerms {r : Nat} (bits : Fin r → R) : R[X] :=
  ∑ j : Fin (r - 1), monomial ((r + 1) * j.val) (bits (j.castLE (Nat.sub_le r 1)))

def PairwiseZero {r : Nat} (bits : Fin r → R) : Prop :=
  ∀ i j, i ≠ j → bits i * bits j = 0

def AtMostOne {r : Nat} (bits : Fin r → R) : Prop :=
  ∀ i j, bits i ≠ 0 → bits j ≠ 0 → i = j

/-- The polynomial whose evaluation is equation (6), with disjoint blocks of
32 coefficients. The zero-based exponent matches the source's 32*(j-1). -/
noncomputable def packed {d : Nat} (checks : Fin d → R[X]) : R[X] :=
  ∑ j, X ^ (32 * j.val) * checks j

/-- Read one of the actual parsed selector rows, with its dependent length. -/
def selectorAt : (widths : List Nat) → PIOPArithmetic.Selectors R widths →
    (j : Fin widths.length) → (Fin (widths.get j) → R)
  | [], _, j => Fin.elim0 j
  | _ :: rest, selectors, j =>
    Fin.cases selectors.1 (fun k => selectorAt rest selectors.2 k) j

/-- Equation (6), using the actual unitaryCheck body and the stated scalar
embedding into the extension algebra. -/
def packedEvaluation {A : Type*} [CommRing A] [Algebra R A] {d : Nat}
    (xi : A) (width : Fin d → Nat) (bits : (j : Fin d) → Fin (width j) → R) : A :=
  ∑ j, xi ^ (32 * j.val) *
    PIOPArithmetic.unitaryCheck xi (fun k => algebraMap R A (bits j k))

end SDitH.Spec.UnitaryPolynomial
