import SDitH.Spec.LineAlgebra
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fin.VecNotation

/-! Algorithms 3/4, printed pp. 13–14: hashing coefficients alpha_1 through
alpha_d, transmitting alpha_2 through alpha_d, and recovering alpha_1 from
an evaluation. `higherCount = d-1`, so the total degree limit is higherCount+1.
This module specifies field-element arrays, not an unstated byte serialization.
No zero-constant or degree property of the computed polynomial is assumed by
these definitions. -/

namespace SDitH.Spec.CoefficientCompression

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

/-- The d coefficients hashed in Algorithm 3 line 7, in increasing order. -/
def hashedCoefficients (higherCount : Nat) (p : F[X]) : Fin (higherCount + 1) → F :=
  fun j => p.coeff (j.val + 1)

/-- The d-1 coefficients transmitted in Algorithm 3 line 9. -/
def transmittedCoefficients (higherCount : Nat) (p : F[X]) : Fin higherCount → F :=
  fun j => p.coeff (j.val + 2)

/-- The explicit higher-degree sum in Algorithm 4 line 9. -/
def higherEvaluation {higherCount : Nat} (higher : Fin higherCount → F) (delta : F) : F :=
  ∑ j, higher j * delta ^ (j.val + 2)

/-- Algorithm 4 lines 9–10 rebuild the full coefficient tuple used by Hashpiop.
At delta=0 this retains Lean's total field inverse; successful source headers
must separately establish delta is nonzero. -/
def restoredCoefficients {higherCount : Nat} (delta value : F)
    (higher : Fin higherCount → F) : Fin (higherCount + 1) → F :=
  Fin.cons (recoverAlphaOne delta value (higherEvaluation higher delta)) higher

/-- The polynomial represented by the hashed nonconstant coefficients. Its
constant term is zero by construction, even if an input polynomial's is not. -/
noncomputable def coefficientPolynomial {d : Nat} (coefficients : Fin d → F) : F[X] :=
  ∑ j, C (coefficients j) * X ^ (j.val + 1)

end SDitH.Spec.CoefficientCompression
