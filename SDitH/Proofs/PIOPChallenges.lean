import SDitH.Spec.PIOPChallenges
import SDitH.Proofs.UniformChallenges
import SDitH.Proofs.ChallengeMixtures
import SDitH.Proofs.PIOPAlgebra
import Mathlib.Algebra.Polynomial.BigOperators

namespace SDitH.Proofs.PIOPChallenges

open Polynomial Spec.PIOP Spec.PIOPChallenges Spec.UniformChallenges
open scoped BigOperators ENNReal Classical

variable {F : Type*} [Field F] {n m : Nat}

/-- Degree does not increase when each variable is replaced by a linear
univariate polynomial. This derives the source's degree premise. -/
theorem substitute_degree (f : MvPolynomial (Fin n) F) (P : Fin n → F[X])
    (hP : ∀ i, (P i).natDegree ≤ 1) :
    (substitute f P).natDegree ≤ f.totalDegree := by
  unfold substitute
  rw [MvPolynomial.eval₂_eq]
  apply natDegree_sum_le_of_forall_le
  intro s hs
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  apply le_trans _ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.sum
  apply Finset.sum_le_sum
  intro i _
  simpa using natDegree_pow_le_of_le (s i) (hP i)

theorem proverPolynomial_degree (f : Fin m → MvPolynomial (Fin n) F)
    (gamma : Fin m → F) (P : Fin n → F[X]) (P₀ : F[X]) (d : Nat)
    (hd : 0 < d) (hP : ∀ i, (P i).natDegree ≤ 1)
    (hf : ∀ j, (f j).totalDegree ≤ d) (hP₀ : P₀.natDegree ≤ d - 1) :
    (proverPolynomial f gamma P P₀).natDegree ≤ d := by
  unfold proverPolynomial
  apply natDegree_add_le_of_degree_le
  · have h := natDegree_mul_le_of_le hP₀ (natDegree_X_le (R := F))
    exact h.trans (by omega)
  · apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_C_mul_le _ _).trans ((substitute_degree (f j) P hP).trans (hf j))

theorem constant_eq_batch (f : Fin m → MvPolynomial (Fin n) F)
    (gamma : Fin m → F) (P : Fin n → F[X]) (P₀ : F[X]) :
    (proverPolynomial f gamma P P₀).eval 0 =
      linearBatch (fun j => MvPolynomial.eval (fun i => (P i).eval 0) (f j)) gamma := by
  rw [prover_evaluation]
  simp [verifierRhs, linearBatch]

/-- The exact probability statement for equation (3), for a witness fixed
before the uniform coefficient challenge and violating at least one constraint. -/
theorem constant_zero_probability [Fintype F]
    (f : Fin m → MvPolynomial (Fin n) F) (P : Fin n → F[X]) (P₀ : F[X])
    (hbad : ¬ ValidWitness f (fun i => (P i).eval 0)) :
    probability (fun gamma => (proverPolynomial f gamma P P₀).eval 0 = 0) =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have hv : (fun j => MvPolynomial.eval (fun i => (P i).eval 0) (f j)) ≠ 0 := by
    intro h
    apply hbad
    intro j
    exact congrFun h j
  simpa only [constant_eq_batch] using UniformChallenges.linear_batch_probability _ hv

theorem literalResidual_eval (f : Fin m → MvPolynomial (Fin n) F)
    (gamma : Fin m → F) (P : Fin n → F[X]) (P₀ answer : F[X]) (delta : F) :
    (literalResidual f gamma P P₀ answer).eval delta =
      answer.eval delta * delta - verifierRhs f gamma delta (P₀.eval delta)
        (fun i => (P i).eval delta) := by
  simp only [literalResidual, eval_sub, eval_mul, eval_X, prover_evaluation]

theorem literal_acceptance_iff (f : Fin m → MvPolynomial (Fin n) F)
    (gamma : Fin m → F) (P : Fin n → F[X]) (P₀ answer : F[X]) (delta : F) :
    literalVerifier f gamma answer delta (P₀.eval delta) (fun i => (P i).eval delta) ↔
      answer.eval 0 = 0 ∧ (literalResidual f gamma P P₀ answer).eval delta = 0 := by
  simp only [literalVerifier, literalResidual_eval, sub_eq_zero]

theorem literalResidual_ne_zero (f : Fin m → MvPolynomial (Fin n) F)
    (gamma : Fin m → F) (P : Fin n → F[X]) (P₀ answer : F[X])
    (hbatch : linearBatch (fun j => MvPolynomial.eval (fun i => (P i).eval 0) (f j)) gamma ≠ 0) :
    literalResidual f gamma P P₀ answer ≠ 0 := by
  intro h
  have he := congrArg (fun p : F[X] => p.eval 0) h
  simp only [literalResidual, eval_sub, eval_mul, eval_X, mul_zero, zero_sub,
    constant_eq_batch, eval_zero, neg_eq_zero] at he
  exact hbatch he

/-- The printed extra factor X raises the degree bound to d+1. This proves
a bound for the literal verifier; it does not assert the text's d/|S| bound. -/
theorem literalResidual_degree (f : Fin m → MvPolynomial (Fin n) F)
    (gamma : Fin m → F) (P : Fin n → F[X]) (P₀ answer : F[X]) (d : Nat)
    (hd : 0 < d) (hP : ∀ i, (P i).natDegree ≤ 1)
    (hf : ∀ j, (f j).totalDegree ≤ d) (hP₀ : P₀.natDegree ≤ d - 1)
    (ha : answer.natDegree ≤ d) : (literalResidual f gamma P P₀ answer).natDegree ≤ d + 1 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le_of_le ha natDegree_X_le
  · exact (proverPolynomial_degree f gamma P P₀ d hd hP hf hP₀).trans (by omega)

theorem conditional_literal_acceptance_bound (f : Fin m → MvPolynomial (Fin n) F)
    (gamma : Fin m → F) (P : Fin n → F[X]) (P₀ answer : F[X]) (d : Nat)
    (hd : 0 < d) (hP : ∀ i, (P i).natDegree ≤ 1)
    (hf : ∀ j, (f j).totalDegree ≤ d) (hP₀ : P₀.natDegree ≤ d - 1)
    (ha : answer.natDegree ≤ d)
    (hbatch : linearBatch (fun j => MvPolynomial.eval (fun i => (P i).eval 0) (f j)) gamma ≠ 0)
    (sample : Finset F) (hne : sample.Nonempty) :
    sampledLiteralAcceptance f gamma P P₀ answer sample hne ≤
      ((d + 1 : Nat) : ℝ≥0∞) / sample.card := by
  apply le_trans (UniformChallenges.subset_probability_mono sample hne _
    (fun delta => (literalResidual f gamma P P₀ answer).eval delta = 0) ?_)
  · exact UniformChallenges.polynomial_root_probability _
      (literalResidual_ne_zero f gamma P P₀ answer hbatch) sample hne (d + 1)
      (literalResidual_degree f gamma P P₀ answer d hd hP hf hP₀ ha)
  · intro delta h
    exact ((literal_acceptance_iff f gamma P P₀ answer delta).mp h).2

/-- A bound for the exact two-challenge algebraic experiment, allowing the
response polynomial to depend on gamma. The committed polynomials are fixed
before gamma, openings are consistent evaluations, and delta is sampled after
the response. This is not a commitment-binding or signature-security theorem. -/
theorem literal_experiment_bound [Fintype F]
    (f : Fin m → MvPolynomial (Fin n) F) (P : Fin n → F[X]) (P₀ : F[X])
    (response : (Fin m → F) → F[X]) (d : Nat)
    (hd : 0 < d) (hP : ∀ i, (P i).natDegree ≤ 1)
    (hf : ∀ j, (f j).totalDegree ≤ d) (hP₀ : P₀.natDegree ≤ d - 1)
    (ha : ∀ gamma, (response gamma).natDegree ≤ d)
    (hbad : ¬ ValidWitness f (fun i => (P i).eval 0))
    (sample : Finset F) (hne : sample.Nonempty) :
    literalExperiment f P P₀ response sample hne true ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (((d + 1 : Nat) : ℝ≥0∞) / sample.card) := by
  have hb : (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
      {gamma | (proverPolynomial f gamma P P₀).eval 0 = 0} =
        (Fintype.card F : ℝ≥0∞)⁻¹ := constant_zero_probability f P P₀ hbad
  unfold literalExperiment
  apply le_trans (ChallengeMixtures.bind_true_bound _ _
    (fun gamma => (proverPolynomial f gamma P P₀).eval 0 = 0)
    (((d + 1 : Nat) : ℝ≥0∞) / sample.card) ?_)
  · rw [hb]
  · intro gamma hgamma
    rw [ChallengeMixtures.eventOutcome_true]
    exact conditional_literal_acceptance_bound f gamma P P₀ (response gamma) d
      hd hP hf hP₀ (ha gamma) (by simpa only [constant_eq_batch] using hgamma) sample hne

/-- Randomized, gamma-dependent responses obey the same algebraic bound when
every response in their support has the protocol's degree bound. -/
theorem randomized_literal_experiment_bound [Fintype F]
    (f : Fin m → MvPolynomial (Fin n) F) (P : Fin n → F[X]) (P₀ : F[X])
    (response : (Fin m → F) → PMF F[X]) (d : Nat)
    (hd : 0 < d) (hP : ∀ i, (P i).natDegree ≤ 1)
    (hf : ∀ j, (f j).totalDegree ≤ d) (hP₀ : P₀.natDegree ≤ d - 1)
    (ha : ∀ gamma answer, answer ∈ (response gamma).support → answer.natDegree ≤ d)
    (hbad : ¬ ValidWitness f (fun i => (P i).eval 0))
    (sample : Finset F) (hne : sample.Nonempty) :
    randomizedLiteralExperiment f P P₀ response sample hne true ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (((d + 1 : Nat) : ℝ≥0∞) / sample.card) := by
  have hb : (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure
      {gamma | (proverPolynomial f gamma P P₀).eval 0 = 0} =
        (Fintype.card F : ℝ≥0∞)⁻¹ := constant_zero_probability f P P₀ hbad
  unfold randomizedLiteralExperiment
  apply le_trans (ChallengeMixtures.bind_true_bound _ _
    (fun gamma => (proverPolynomial f gamma P P₀).eval 0 = 0)
    (((d + 1 : Nat) : ℝ≥0∞) / sample.card) ?_)
  · rw [hb]
  · intro gamma hgamma
    apply ChallengeMixtures.bind_true_le
    intro answer hs
    rw [ChallengeMixtures.eventOutcome_true]
    exact conditional_literal_acceptance_bound f gamma P P₀ answer d
      hd hP hf hP₀ (ha gamma answer hs)
      (by simpa only [constant_eq_batch] using hgamma) sample hne

end SDitH.Proofs.PIOPChallenges
