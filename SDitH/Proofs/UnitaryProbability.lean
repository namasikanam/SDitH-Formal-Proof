import SDitH.Proofs.UnitaryPacking
import SDitH.Proofs.UniformChallenges
import SDitH.Proofs.FieldIrreducibility

/-! Exact uniform batching probabilities for equation (6), printed p. 33,
and its contribution to Algorithms 19/20. The binary selectors and the other
batch's output are fixed before the unitary challenge is sampled. These are
statements about explicit uniform sampling, not concrete hash outputs. -/

namespace SDitH.Proofs.UnitaryProbability

open Spec.FieldRepresentation Spec.UniformChallenges Spec.UnitaryPolynomial
open Spec.PIOPArithmetic Polynomial
open scoped BigOperators ENNReal Classical

theorem loop_vector_zero_iff (category : Category) {w : Nat}
    (widths : List Nat) (selectors : Fin w → Selectors (ZMod 2) widths)
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3) :
    (fun i => unitaryLayers (generator category) widths
      (mapSelectors (algebraMap (ZMod 2) (QuotientRing category)) widths (selectors i)) 0) = 0 ↔
      ∀ i (j : Fin widths.length), AtMostOne (selectorAt widths (selectors i) j) := by
  rw [funext_iff]
  exact forall_congr' fun i => UnitaryPacking.submitted_unitary_loop category widths
    (selectors i) hd hw

/-- The exact error probability in the unitary-batching claim. The premise
states that at least one of the actual parsed binary selector rows is invalid. -/
theorem invalid_selector_probability (category : Category) {w : Nat}
    (widths : List Nat) (selectors : Fin w → Selectors (ZMod 2) widths)
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3)
    (hbad : ¬ ∀ i (j : Fin widths.length), AtMostOne (selectorAt widths (selectors i) j)) :
    probability (fun gamma : Fin w → QuotientRing category =>
      (∑ i, gamma i * unitaryLayers (generator category) widths
        (mapSelectors (algebraMap (ZMod 2) (QuotientRing category)) widths (selectors i)) 0) = 0) =
      ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹ := by
  have hne := (loop_vector_zero_iff category widths selectors hd hw).not.mpr hbad
  simpa only [linearBatch, FieldIrreducibility.quotient_card] using
    UniformChallenges.linear_batch_probability _ hne

/-- At zero, the literal arithmetic is an affine function of the unitary
challenge. This identity does not assert that the mux implements the source's
omitted-last-coordinate witness encoding. -/
theorem run_zero_eq_affine {F : Type*} [CommRing F] {w : Nat}
    (widths : List Nat) (xi mask syndrome : F) (gamma : Fin w → F)
    (selectors : Fin w → Selectors F widths)
    (columns : Fin w → Fin (leafCount widths) → F) :
    runArithmetic widths xi 0 mask syndrome gamma selectors columns =
      (-syndrome + ∑ i, muxTree widths (selectors i) (columns i)) +
        linearBatch (fun i => unitaryLayers xi widths (selectors i) 0) gamma := by
  simp [runArithmetic, linearBatch, Finset.sum_add_distrib, add_assoc]

/-- The syndrome/mux offset can be arbitrary, provided it is fixed before
the fresh uniform unitary challenge. Invalid binary selectors still have
exactly the stated cancellation probability in the actual arithmetic. -/
theorem run_zero_probability (category : Category) {w : Nat}
    (widths : List Nat) (selectors : Fin w → Selectors (ZMod 2) widths)
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3)
    (hbad : ¬ ∀ i (j : Fin widths.length), AtMostOne (selectorAt widths (selectors i) j))
    (mask syndrome : QuotientRing category)
    (columns : Fin w → Fin (leafCount widths) → QuotientRing category) :
    probability (fun gamma : Fin w → QuotientRing category =>
      runArithmetic widths (generator category) 0 mask syndrome gamma
        (fun i => mapSelectors (algebraMap (ZMod 2) (QuotientRing category)) widths (selectors i))
        columns = 0) = ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹ := by
  simp_rw [run_zero_eq_affine]
  have hne := (loop_vector_zero_iff category widths selectors hd hw).not.mpr hbad
  simpa only [FieldIrreducibility.quotient_card] using
    UniformChallenges.affine_batch_probability _ hne _

/-- The probability statement includes the actual flat parser and polynomial
computation of Algorithms 13 and 19. Polynomial constant terms are explicitly
required to be the submitted binary witness bits. No honest-witness constant
term claim or degree annotation is presumed. -/
theorem prover_constant_probability (category : Category) {w lambda : Nat}
    (widths : List Nat) (bits : Fin (selectorCount widths * w) → ZMod 2)
    (witness : Fin (selectorCount widths * w) → (QuotientRing category)[X])
    (hconstants : ∀ k, (witness k).eval 0 = algebraMap (ZMod 2) (QuotientRing category) (bits k))
    (randomness : Fin (lambda * (widths.length - 1)) → (QuotientRing category)[X])
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3)
    (hbad : ¬ ∀ i (j : Fin widths.length),
      AtMostOne (selectorAt widths (formatWitness widths bits i) j))
    (syndrome : QuotientRing category)
    (columns : Fin w → Fin (leafCount widths) → QuotientRing category) :
    probability (fun gamma : Fin w → QuotientRing category =>
      (proverArithmeticFlat widths (generator category) syndrome gamma witness randomness columns).eval 0 = 0) =
      ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹ := by
  simp_rw [PIOPArithmetic.verifier_evaluates_prover_flat, hconstants]
  unfold verifierArithmeticFlat verifierArithmetic
  rw [← PIOPArithmetic.map_formatWitness]
  exact run_zero_probability category widths (formatWitness widths bits) hd hw hbad _ syndrome columns

end SDitH.Proofs.UnitaryProbability
