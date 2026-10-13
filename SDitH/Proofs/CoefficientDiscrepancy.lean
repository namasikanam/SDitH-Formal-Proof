import SDitH.Proofs.CoefficientCompression
import SDitH.Proofs.WitnessPIOPDiscrepancy
import SDitH.Proofs.PIOPDegree
import Mathlib.Algebra.Polynomial.Eval.Coeff

namespace SDitH.Proofs.CoefficientDiscrepancy

open Spec.PIOPArithmetic Spec.CoefficientCompression Polynomial WitnessPIOPDiscrepancy

variable {F : Type*} [Field F]

/-- The valid small SD witness already constructed in WitnessPIOPDiscrepancy
also causes Algorithm 4's coefficient recovery to disagree with Algorithm 3's
hashed tuple at every nonzero challenge, even with exact polynomial evaluations.
This is a coefficient-input discrepancy, not a claim of unequal hash outputs,
a reachable BLC distribution or a full signature execution. -/
theorem valid_witness_coefficients_disagree (xi : F) (gamma : Fin 1 → F)
    (delta : F) (hdelta : delta ≠ 0) :
    let p := proverArithmeticFlat (lambda := 128) [2, 2] xi 1 gamma
      (fun j => C (flatWitness j)) (fun _ => 0) columns
    restoredCoefficients delta (p.eval delta) (transmittedCoefficients 1 p) ≠
      hashedCoefficients 1 p := by
  let p := proverArithmeticFlat (lambda := 128) [2, 2] xi 1 gamma
    (fun j => C (flatWitness j)) (fun _ => 0) columns
  have hp : p.natDegree ≤ 1 + 1 := PIOPDegree.proverArithmeticFlat_degree
    [2, 2] (by decide) xi 1 gamma _ _ columns (fun _ => by simp) (fun _ => by simp)
  have hzero : p.coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact detailed_prover_nonzero_constant xi gamma
  exact (CoefficientCompression.restored_eq_hashed_iff 1 p hp delta hdelta).not.mpr hzero

end SDitH.Proofs.CoefficientDiscrepancy
