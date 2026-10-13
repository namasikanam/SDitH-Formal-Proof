import SDitH.Spec.DetailedPIOPChallenges
import SDitH.Proofs.PIOPComposition

namespace SDitH.Proofs.DetailedPIOPChallenges

open Spec.DetailedPIOPChallenges Spec.PIOPComposition Spec.PIOPArithmetic
open Spec.FieldRepresentation Spec.UnitaryPolynomial Spec.UniformChallenges Polynomial
open scoped ENNReal Classical

/-- A zero-constant response cannot be identical to an expected polynomial
with nonzero constant term. Their agreement is bounded by the degree of their
difference, with no extra multiplication by the evaluation point. -/
theorem comparison_probability {F : Type*} [Field F] (expected answer : F[X])
    (hconstant : expected.eval 0 ≠ 0) (d : Nat)
    (hp : expected.natDegree ≤ d) (ha : answer.natDegree ≤ d)
    (sample : Finset F) (hne : sample.Nonempty) :
    subsetProbability sample hne
      (fun delta => answer.eval 0 = 0 ∧ answer.eval delta = expected.eval delta) ≤
        (d : ℝ≥0∞) / sample.card := by
  by_cases hz : answer.eval 0 = 0
  · have hnepoly : answer - expected ≠ 0 := by
      intro h
      have he := congrArg (Polynomial.eval 0) h
      simp only [eval_sub, eval_zero, hz, zero_sub, neg_eq_zero] at he
      exact hconstant he
    apply le_trans (UniformChallenges.subset_probability_mono sample hne _
      (fun delta => (answer - expected).eval delta = 0) (fun delta h => by simp [h.2]))
    exact UniformChallenges.polynomial_root_probability (answer - expected) hnepoly sample hne d
      ((natDegree_sub_le _ _).trans (max_le ha hp))
  · rw [UniformChallenges.subset_probability_card]
    simp [hz]

/-- The first-stage law in comparisonExperiment is exactly the two sampling
steps in constantExperiment, not an assumed marginal distribution. -/
theorem constant_mass {K F : Type*} [CommRing K] [Field F] [Algebra K F] [Fintype F]
    {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F[X])
    (randomness : Fin (lambda * (widths.length - 1)) → F[X]) :
    (batchingChallenges F r w lambda).toOuterMeasure
      {challenges | (proverRun widths hsize xi challenges.1 challenges.2 H' y witness randomness).eval 0 = 0} =
      constantExperiment widths hsize xi H' y witness randomness true := by
  rw [← ChallengeMixtures.eventOutcome_true]
  unfold eventOutcome batchingChallenges constantExperiment
  rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, eventOutcome]

/-- The detailed, consistent-opening algebraic comparison bound with randomized
responses depending on both batching challenges. All polynomial degrees and
the first-stage error probability are derived from the actual composed routines.
This is not a signature unforgeability or knowledge-extraction theorem. -/
theorem comparison_experiment_bound (category : Category) {r k w : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (bits : Fin (selectorCount widths * w) → ZMod 2)
    (witness : Fin (selectorCount widths * w) → (QuotientRing category)[X])
    (hconstants : ∀ j, (witness j).eval 0 = algebraMap (ZMod 2) (QuotientRing category) (bits j))
    (randomness : Fin (width category * (widths.length - 1)) → (QuotientRing category)[X])
    (hd : 2 ≤ widths.length) (hd' : widths.length ≤ 4)
    (hwidths : ∀ j : Fin widths.length, widths.get j ≤ 3)
    (hw : ∀ j, (witness j).natDegree ≤ 1) (hr : ∀ j, (randomness j).natDegree ≤ 1)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (hbad : muxSyndromeResidual widths hsize H' y bits ≠ 0 ∨
      ¬ ∀ i (j : Fin widths.length), AtMostOne (selectorAt widths (formatWitness widths bits i) j))
    (response : Challenges (QuotientRing category) r w (width category) → PMF (QuotientRing category)[X])
    (hresponse : ∀ challenges answer, answer ∈ (response challenges).support → answer.natDegree ≤ widths.length)
    (sample : Finset (QuotientRing category)) (hne : sample.Nonempty) :
    comparisonExperiment widths hsize (generator category) H' y witness randomness response sample hne true ≤
      ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹ +
        (1 - ((2 ^ width category : Nat) : ℝ≥0∞)⁻¹) * ((widths.length : ℝ≥0∞) / sample.card) := by
  have hmass := constant_mass widths hsize (generator category) H' y witness randomness
  rw [PIOPComposition.invalid_constant_experiment category widths hsize bits witness hconstants
    randomness hd' hwidths H' y hbad] at hmass
  unfold comparisonExperiment
  rw [← hmass]
  apply ChallengeMixtures.bind_true_bound
  intro challenges hnonzero
  apply ChallengeMixtures.bind_true_le
  intro answer hanswer
  rw [ChallengeMixtures.eventOutcome_true]
  simp_rw [← PIOPComposition.verifier_evaluates_prover]
  exact comparison_probability _ answer hnonzero widths.length
    (PIOPComposition.prover_degree widths hsize hd _ _ _ H' y witness randomness hw hr)
    (hresponse challenges answer hanswer) sample hne

end SDitH.Proofs.DetailedPIOPChallenges
