import SDitH.Spec.PIOPComposition
import SDitH.Proofs.UnitaryProbability
import SDitH.Proofs.ChallengeMixtures
import SDitH.Proofs.MuxLinearity
import SDitH.Proofs.PIOPDegree
import SDitH.Proofs.BatchingProbability

namespace SDitH.Proofs.PIOPComposition

open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Spec.FieldRepresentation
open Spec.UnitaryPolynomial Spec.UniformChallenges Polynomial
open scoped BigOperators ENNReal Classical

/-- The actual composed routines agree under evaluation, including their
shared Algorithm-21 computation and their flat parser. This is an arithmetic
identity, independent of witness validity or a protocol soundness assumption. -/
theorem verifier_evaluates_prover {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
    {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (xi delta : F) (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F[X])
    (randomness : Fin (lambda * (widths.length - 1)) → F[X]) :
    (proverRun widths hsize xi gamma gammaPrime H' y witness randomness).eval delta =
      verifierRun widths hsize xi delta gamma gammaPrime H' y
        (fun j => (witness j).eval delta) (fun j => (randomness j).eval delta) := by
  exact PIOPArithmetic.verifier_evaluates_prover_flat _ _ _ _ _ _ _ _

theorem prover_degree {K F : Type*} [CommRing K] [Field F] [Algebra K F]
    {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (hd : 2 ≤ widths.length) (xi : F)
    (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F[X])
    (randomness : Fin (lambda * (widths.length - 1)) → F[X])
    (hw : ∀ j, (witness j).natDegree ≤ 1) (hr : ∀ j, (randomness j).natDegree ≤ 1) :
    (proverRun widths hsize xi gamma gammaPrime H' y witness randomness).natDegree ≤
      widths.length := by
  exact PIOPDegree.proverArithmeticFlat_degree widths hd xi _ gammaPrime witness randomness _ hw hr

/-- Exact constant term, with both independently batched residuals computed
from the literal routines. No correctness of the intended SD encoding is used. -/
theorem constant_eq_batches {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
    {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (xi : F) (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (bits : Fin (selectorCount widths * w) → K)
    (witness : Fin (selectorCount widths * w) → F[X])
    (hconstants : ∀ j, (witness j).eval 0 = algebraMap K F (bits j))
    (randomness : Fin (lambda * (widths.length - 1)) → F[X]) :
    (proverRun widths hsize xi gamma gammaPrime H' y witness randomness).eval 0 =
      batchLinearMap xi gamma (muxSyndromeResidual widths hsize H' y bits) +
        linearBatch (fun i => unitaryLayers xi widths
          (mapSelectors (algebraMap K F) widths (formatWitness widths bits i)) 0) gammaPrime := by
  rw [verifier_evaluates_prover]
  simp_rw [hconstants]
  unfold verifierRun verifierArithmeticFlat verifierArithmetic
  rw [← PIOPArithmetic.map_formatWitness, UnitaryProbability.run_zero_eq_affine,
    MuxLinearity.batch_mux_residual]

/-- Equation (6)'s unitary error probability after executing the actual
Algorithm 21. The first challenge can be any fixed vector. -/
theorem conditional_constant_probability (category : Category) {r k w : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (bits : Fin (selectorCount widths * w) → ZMod 2)
    (witness : Fin (selectorCount widths * w) → (QuotientRing category)[X])
    (hconstants : ∀ j, (witness j).eval 0 = algebraMap (ZMod 2) (QuotientRing category) (bits j))
    (randomness : Fin (width category * (widths.length - 1)) → (QuotientRing category)[X])
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3)
    (hbad : ¬ ∀ i (j : Fin widths.length),
      AtMostOne (selectorAt widths (formatWitness widths bits i) j))
    (gamma : Fin (blockCount r (width category)) → QuotientRing category)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2) :
    probability (fun gammaPrime : Fin w → QuotientRing category =>
      (proverRun widths hsize (generator category) gamma gammaPrime H' y witness randomness).eval 0 = 0) =
      ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹ := by
  exact UnitaryProbability.prover_constant_probability category widths bits witness hconstants
    randomness hd hw hbad _ _

/-- With fresh uniform gamma and gamma-prime, the same exact bound holds for
the composed constant-term experiment. This neither establishes the omitted
coordinate/mux correspondence nor asserts that a Fiat-Shamir hash is uniform. -/
theorem constant_experiment_probability (category : Category) {r k w : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (bits : Fin (selectorCount widths * w) → ZMod 2)
    (witness : Fin (selectorCount widths * w) → (QuotientRing category)[X])
    (hconstants : ∀ j, (witness j).eval 0 = algebraMap (ZMod 2) (QuotientRing category) (bits j))
    (randomness : Fin (width category * (widths.length - 1)) → (QuotientRing category)[X])
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3)
    (hbad : ¬ ∀ i (j : Fin widths.length),
      AtMostOne (selectorAt widths (formatWitness widths bits i) j))
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2) :
    constantExperiment widths hsize (generator category) H' y witness randomness true =
      ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹ := by
  unfold constantExperiment
  apply ChallengeMixtures.bind_true_eq
  intro gamma _
  rw [ChallengeMixtures.eventOutcome_true]
  exact conditional_constant_probability category widths hsize bits witness hconstants
    randomness hd hw hbad gamma H' y

/-- When all binary unitary checks hold, the actual constant-term experiment
reduces to sampling the linear batch of the literal mux residual. -/
theorem valid_unitary_experiment (category : Category) {r k w : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (bits : Fin (selectorCount widths * w) → ZMod 2)
    (witness : Fin (selectorCount widths * w) → (QuotientRing category)[X])
    (hconstants : ∀ j, (witness j).eval 0 = algebraMap (ZMod 2) (QuotientRing category) (bits j))
    (randomness : Fin (width category * (widths.length - 1)) → (QuotientRing category)[X])
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3)
    (hgood : ∀ i (j : Fin widths.length),
      AtMostOne (selectorAt widths (formatWitness widths bits i) j))
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2) :
    constantExperiment widths hsize (generator category) H' y witness randomness =
      eventOutcome (PMF.uniformOfFintype (Fin (blockCount r (width category)) → QuotientRing category))
        (fun gamma => batchLinearMap (generator category) gamma
          (muxSyndromeResidual widths hsize H' y bits) = 0) := by
  have hz := (UnitaryProbability.loop_vector_zero_iff category widths
    (formatWitness widths bits) hd hw).mpr hgood
  unfold constantExperiment eventOutcome
  simp_rw [constant_eq_batches widths hsize _ _ _ H' y bits witness hconstants randomness, hz]
  simp only [linearBatch, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  change (PMF.uniformOfFintype _).bind _ = (PMF.uniformOfFintype _).bind _
  congr 1
  funext gamma
  exact PMF.map_const _ _

/-- Exact cancellation probability whenever either computed constraint vector
is nonzero. The syndrome vector is explicitly the literal mux residual, not an
assumed encoding of the intended SD witness. -/
theorem invalid_constant_experiment (category : Category) {r k w : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (bits : Fin (selectorCount widths * w) → ZMod 2)
    (witness : Fin (selectorCount widths * w) → (QuotientRing category)[X])
    (hconstants : ∀ j, (witness j).eval 0 = algebraMap (ZMod 2) (QuotientRing category) (bits j))
    (randomness : Fin (width category * (widths.length - 1)) → (QuotientRing category)[X])
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (hbad : muxSyndromeResidual widths hsize H' y bits ≠ 0 ∨
      ¬ ∀ i (j : Fin widths.length), AtMostOne (selectorAt widths (formatWitness widths bits i) j)) :
    constantExperiment widths hsize (generator category) H' y witness randomness true =
      ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹ := by
  by_cases hgood : ∀ i (j : Fin widths.length),
      AtMostOne (selectorAt widths (formatWitness widths bits i) j)
  · rw [valid_unitary_experiment category widths hsize bits witness hconstants randomness hd hw hgood,
      ChallengeMixtures.eventOutcome_true]
    exact BatchingProbability.batch_probability category _ (hbad.resolve_right (not_not.mpr hgood))
  · exact constant_experiment_probability category widths hsize bits witness hconstants
      randomness hd hw hgood H' y

theorem valid_constant_experiment (category : Category) {r k w : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (bits : Fin (selectorCount widths * w) → ZMod 2)
    (witness : Fin (selectorCount widths * w) → (QuotientRing category)[X])
    (hconstants : ∀ j, (witness j).eval 0 = algebraMap (ZMod 2) (QuotientRing category) (bits j))
    (randomness : Fin (width category * (widths.length - 1)) → (QuotientRing category)[X])
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3)
    (hgood : ∀ i (j : Fin widths.length),
      AtMostOne (selectorAt widths (formatWitness widths bits i) j))
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (hresidual : muxSyndromeResidual widths hsize H' y bits = 0) :
    constantExperiment widths hsize (generator category) H' y witness randomness true = 1 := by
  rw [valid_unitary_experiment category widths hsize bits witness hconstants randomness hd hw hgood,
    ChallengeMixtures.eventOutcome_true]
  simp only [hresidual, map_zero]
  exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (fun _ _ => trivial)

end SDitH.Proofs.PIOPComposition
