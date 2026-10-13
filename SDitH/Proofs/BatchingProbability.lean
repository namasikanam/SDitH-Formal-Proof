import SDitH.Proofs.UniformChallenges
import SDitH.Proofs.ConcreteEncodings
import SDitH.Proofs.FieldIrreducibility

/-! The uniform-challenge batching claim following equation (7), printed p. 34.
The residual is fixed before the coefficient vector is sampled. These results
do not replace concrete challenge generation by an ideal uniform oracle. -/

namespace SDitH.Proofs.BatchingProbability

open Spec.FieldRepresentation Spec.UniformChallenges
open scoped BigOperators ENNReal Classical

theorem packVector_ne_zero (category : Category) {r : Nat}
    (v : Fin r → ZMod 2) (hv : v ≠ 0) :
    Spec.Batching.packVector (lambda := width category) (generator category) v ≠ 0 := by
  intro h
  have hz : Spec.Batching.packVector (r := r) (lambda := width category)
      (generator category) (0 : Fin r → ZMod 2) = 0 := by
    funext block
    exact map_zero (Spec.Batching.packBlockLinear (generator category) block)
  exact hv (ConcreteEncodings.packVector_injective category (h.trans hz.symm))

/-- Exact cancellation probability for the actual full zero-padded Phi map,
including a partial final block, in each submitted Table-2 field. -/
theorem batch_probability (category : Category) {r : Nat}
    (v : Fin r → ZMod 2) (hv : v ≠ 0) :
    probability (fun gamma : Fin (Spec.Batching.blockCount r (width category)) →
      QuotientRing category =>
        Spec.Batching.batchLinearMap (generator category) gamma v = 0) =
      ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹ := by
  have h := UniformChallenges.linear_batch_probability
    (Spec.Batching.packVector (lambda := width category) (generator category) v)
    (packVector_ne_zero category v hv)
  simpa only [Batching.batch_formula, linearBatch, FieldIrreducibility.quotient_card] using h

/-- The scalar equation returned by Algorithm 21 has precisely the same
cancellation event as batching the true systematic syndrome residual. -/
theorem algorithm21_probability (category : Category) {r k : Nat}
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (x : Fin (r + k) → ZMod 2)
    (y : Fin r → ZMod 2) (hbad : (Spec.Batching.systematicLeft H').mulVec x ≠ y) :
    probability (fun gamma : Fin (Spec.Batching.blockCount r (width category)) →
      QuotientRing category =>
        let output := Spec.Batching.batchLinearEquations (generator category) gamma H' y
        (∑ j, algebraMap (ZMod 2) (QuotientRing category) (x j) * output.1 j) = output.2) =
      ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹ := by
  have h := batch_probability category
    ((Spec.Batching.systematicLeft H').mulVec x - y) (sub_ne_zero.mpr hbad)
  simpa only [Batching.batch_residual, sub_eq_zero, Spec.Batching.batchLinearEquations] using h

end SDitH.Proofs.BatchingProbability
