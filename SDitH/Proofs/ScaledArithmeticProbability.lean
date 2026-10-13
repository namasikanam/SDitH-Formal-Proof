import SDitH.Proofs.ScaledArithmetic
import SDitH.Proofs.UniformChallenges
import SDitH.Proofs.ChallengeMixtures
import SDitH.Proofs.DetailedPIOPChallenges

namespace SDitH.Proofs.ScaledArithmeticProbability

open Polynomial Spec.PIOPArithmetic Spec.Batching Spec.ScaledArithmetic Spec.UniformChallenges
open scoped BigOperators ENNReal Classical

variable {K F : Type*} [CommRing K] [Field F] [Algebra K F] [Fintype F]

/-- A nonzero actual unitary vector gives the exact cancellation probability,
even with the scaled syndrome offset and an arbitrary fixed first challenge. -/
theorem conditional_constant_probability {r k w lambda packingWidth degree : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r packingWidth) → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positionValues : Fin (selectorCount widths * w) → K) (amplitudeValues : Fin w → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (hp : ∀ i, (positions i).eval 0 = algebraMap K F (positionValues i))
    (ha : ∀ i, (amplitudes i).eval 0 = algebraMap K F (amplitudeValues i))
    (randomness : Fin (lambda * (degree - 1)) → F[X])
    (hu : (fun i => unitaryLayers xi widths
      (mapSelectors (algebraMap K F) widths (formatWitness widths positionValues i)) 0) ≠ 0) :
    probability (fun gammaPrime : Fin w → F =>
      (proverRun widths hsize xi gamma gammaPrime H' y positions amplitudes randomness).eval 0 = 0) =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  simp_rw [ScaledArithmetic.constant_eq_batches widths hsize xi gamma _ H' y
    positionValues amplitudeValues positions amplitudes hp ha randomness]
  exact UniformChallenges.affine_batch_probability _ hu _

theorem zero_unitary_experiment {r k w lambda packingWidth degree : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positionValues : Fin (selectorCount widths * w) → K) (amplitudeValues : Fin w → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (hp : ∀ i, (positions i).eval 0 = algebraMap K F (positionValues i))
    (ha : ∀ i, (amplitudes i).eval 0 = algebraMap K F (amplitudeValues i))
    (randomness : Fin (lambda * (degree - 1)) → F[X])
    (hu : (fun i => unitaryLayers xi widths
      (mapSelectors (algebraMap K F) widths (formatWitness widths positionValues i)) 0) = 0) :
    constantExperiment (packingWidth := packingWidth) widths hsize xi H' y positions amplitudes
      randomness = eventOutcome (PMF.uniformOfFintype (Fin (blockCount r packingWidth) → F))
        (fun gamma => batchLinearMap xi gamma
          (scaledResidual widths hsize H' y positionValues amplitudeValues) = 0) := by
  unfold constantExperiment eventOutcome
  simp_rw [ScaledArithmetic.constant_eq_batches widths hsize xi _ _ H' y
    positionValues amplitudeValues positions amplitudes hp ha randomness, hu]
  simp only [linearBatch, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  change (PMF.uniformOfFintype _).bind _ = (PMF.uniformOfFintype _).bind _
  congr 1
  funext gamma
  exact PMF.map_const _ _

/-- For the actual two-stage experiment, either computed constraint vector
being nonzero gives 1/|F| cancellation. Crucially the syndrome premise is
nonzeroness AFTER packing; injectivity for F256 is not inserted as a premise
about the whole routine or silently inherited from the binary proof. -/
theorem invalid_constant_experiment {r k w lambda packingWidth degree : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positionValues : Fin (selectorCount widths * w) → K) (amplitudeValues : Fin w → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (hp : ∀ i, (positions i).eval 0 = algebraMap K F (positionValues i))
    (ha : ∀ i, (amplitudes i).eval 0 = algebraMap K F (amplitudeValues i))
    (randomness : Fin (lambda * (degree - 1)) → F[X])
    (hbad : packVector (lambda := packingWidth) xi
        (scaledResidual widths hsize H' y positionValues amplitudeValues) ≠ 0 ∨
      (fun i => unitaryLayers xi widths
        (mapSelectors (algebraMap K F) widths (formatWitness widths positionValues i)) 0) ≠ 0) :
    constantExperiment (packingWidth := packingWidth) widths hsize xi H' y positions amplitudes
      randomness true = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  by_cases hu : (fun i => unitaryLayers xi widths
      (mapSelectors (algebraMap K F) widths (formatWitness widths positionValues i)) 0) = 0
  · have hv := hbad.resolve_right (not_not.mpr hu)
    rw [zero_unitary_experiment widths hsize xi H' y positionValues amplitudeValues
      positions amplitudes hp ha randomness hu, ChallengeMixtures.eventOutcome_true]
    simpa only [probability, Batching.batch_formula, linearBatch] using
      UniformChallenges.linear_batch_probability _ hv
  · unfold constantExperiment
    apply ChallengeMixtures.bind_true_eq
    intro gamma _
    rw [ChallengeMixtures.eventOutcome_true]
    exact conditional_constant_probability widths hsize xi gamma H' y positionValues
      amplitudeValues positions amplitudes hp ha randomness hu

/-- When both computed vectors vanish, the constant-term arithmetic accepts
with certainty. This does not imply that the candidate values are nonzero. -/
theorem valid_constant_experiment {r k w lambda packingWidth degree : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positionValues : Fin (selectorCount widths * w) → K) (amplitudeValues : Fin w → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (hp : ∀ i, (positions i).eval 0 = algebraMap K F (positionValues i))
    (ha : ∀ i, (amplitudes i).eval 0 = algebraMap K F (amplitudeValues i))
    (randomness : Fin (lambda * (degree - 1)) → F[X])
    (hv : packVector (lambda := packingWidth) xi
      (scaledResidual widths hsize H' y positionValues amplitudeValues) = 0)
    (hu : (fun i => unitaryLayers xi widths
      (mapSelectors (algebraMap K F) widths (formatWitness widths positionValues i)) 0) = 0) :
    constantExperiment (packingWidth := packingWidth) widths hsize xi H' y positions amplitudes
      randomness true = 1 := by
  unfold constantExperiment
  apply ChallengeMixtures.bind_true_eq
  intro gamma _
  rw [ChallengeMixtures.eventOutcome_true]
  simp_rw [ScaledArithmetic.constant_eq_batches widths hsize xi gamma _ H' y
    positionValues amplitudeValues positions amplitudes hp ha randomness, hu,
    Batching.batch_formula, hv]
  simp only [linearBatch, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (fun _ _ => trivial)

/-- The comparison's first-stage marginal is the defined constant experiment,
with the same two independent draws in the same order. -/
theorem constant_mass {r k w lambda packingWidth degree : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (randomness : Fin (lambda * (degree - 1)) → F[X]) :
    (Spec.DetailedPIOPChallenges.batchingChallenges F r w packingWidth).toOuterMeasure
      {challenges | (proverRun widths hsize xi challenges.1 challenges.2 H' y positions
        amplitudes randomness).eval 0 = 0} =
      constantExperiment (packingWidth := packingWidth) widths hsize xi H' y positions
        amplitudes randomness true := by
  rw [← ChallengeMixtures.eventOutcome_true]
  unfold eventOutcome Spec.DetailedPIOPChallenges.batchingChallenges constantExperiment
  rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, eventOutcome]

/-- The scaled arithmetic's algebraic bound with adaptive randomized response
polynomials. The actual prover degree and constant-term probability are proved
above. Packing and unitary residuals are the literal computed vectors; neither
is assumed to characterize regular SD witnesses, and no Fiat-Shamir law is used. -/
theorem comparison_experiment_bound {r k w lambda packingWidth degree : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positionValues : Fin (selectorCount widths * w) → K) (amplitudeValues : Fin w → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (hp : ∀ i, (positions i).eval 0 = algebraMap K F (positionValues i))
    (ha : ∀ i, (amplitudes i).eval 0 = algebraMap K F (amplitudeValues i))
    (randomness : Fin (lambda * (degree - 1)) → F[X])
    (hd : 2 ≤ degree) (hlength : widths.length + 1 ≤ degree)
    (hpd : ∀ i, (positions i).natDegree ≤ 1) (had : ∀ i, (amplitudes i).natDegree ≤ 1)
    (hr : ∀ i, (randomness i).natDegree ≤ 1)
    (hbad : packVector (lambda := packingWidth) xi
        (scaledResidual widths hsize H' y positionValues amplitudeValues) ≠ 0 ∨
      (fun i => unitaryLayers xi widths
        (mapSelectors (algebraMap K F) widths (formatWitness widths positionValues i)) 0) ≠ 0)
    (response : Spec.DetailedPIOPChallenges.Challenges F r w packingWidth → PMF F[X])
    (hresponse : ∀ challenges answer,
      answer ∈ (response challenges).support → answer.natDegree ≤ degree)
    (sample : Finset F) (hne : sample.Nonempty) :
    comparisonExperiment widths hsize xi H' y positions amplitudes randomness response sample hne true ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * ((degree : ℝ≥0∞) / sample.card) := by
  have hmass := constant_mass (packingWidth := packingWidth) widths hsize xi H' y positions
    amplitudes randomness
  rw [invalid_constant_experiment widths hsize xi H' y positionValues amplitudeValues
    positions amplitudes hp ha randomness hbad] at hmass
  unfold comparisonExperiment
  rw [← hmass]
  apply ChallengeMixtures.bind_true_bound
  intro challenges hnonzero
  apply ChallengeMixtures.bind_true_le
  intro answer hanswer
  rw [ChallengeMixtures.eventOutcome_true]
  simp_rw [← ScaledArithmetic.verifierRun_evaluates_proverRun]
  exact DetailedPIOPChallenges.comparison_probability _ answer hnonzero degree
    (ScaledArithmetic.proverRun_degree widths hd hlength hsize xi _ _ H' y positions
      amplitudes randomness hpd had hr) (hresponse challenges answer hanswer) sample hne

end SDitH.Proofs.ScaledArithmeticProbability
