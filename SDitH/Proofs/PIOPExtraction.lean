import SDitH.Proofs.SlopeConsistencyLink
import SDitH.Proofs.PIOPComposition
import SDitH.Proofs.CoefficientCompression

/-! The deterministic PIOP step of the extraction. With a common slope the
candidate middle's witness and randomness values are the evaluations, at
the inverted challenge, of explicit degree-one lines whose constant terms
are the extracted witness coordinates and the common randomness slopes.
The composed verifier's recomputation is then the evaluation of the
composed prover polynomial of those lines, so an accepting transcript,
whose restored coefficient tuple is the hashed one, forces the difference
between that polynomial and the hashed coefficient polynomial to vanish
at the challenge. The probability that a nonzero difference vanishes at
the challenge is the Schwartz–Zippel step, charged separately. -/

namespace SDitH.Proofs.PIOPExtraction

open Spec.DomainSeparation Spec.BLCSeedLines Spec.BLCSeedFold Spec.CoefficientCompression Spec.PIOPComposition
open Spec.PIOPArithmetic Spec.Batching Polynomial
open scoped BigOperators
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- With a common slope, the candidate randomness value is affine in the
inverted challenge, with constant term the common slope coordinate. -/
theorem candidate_randomness_constant_slope {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (hidden : Fin tau → Fin (2 ^ kappa)) (encode : (Fin tau → Fin (2 ^ kappa)) → F) (j : Fin rnd) (u : ZMod 2)
    (hu : ∀ e, Spec.BLCSeedFold.slope p salt full randomCount enough aux e (Spec.BLC.randomnessIndex j) = u)
    (hencode : encode = fun hidden => Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hnz : encode hidden ≠ 0) :
    (encode hidden)⁻¹ * Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.randomnessIndex j)) =
      algebraMap (ZMod 2) F u +
        (encode hidden)⁻¹ * Spec.BLC.psi xi (interceptMatrix p salt full randomCount enough (Spec.BLC.randomnessIndex j)) := by
  have hQ : shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.randomnessIndex j) =
      fun e j' => u * Spec.GrayCode.grayFieldRow (hidden e) j' +
        interceptMatrix p salt full randomCount enough (Spec.BLC.randomnessIndex j) e j' := by
    funext e j'
    show Spec.BLCSeedFold.slope p salt full randomCount enough aux e (Spec.BLC.randomnessIndex j) * _ + _ = _
    rw [hu]
    rfl
  have hmerge : (encode hidden)⁻¹ * Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden) = 1 := by
    have hd : Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden) ≠ 0 := by
      rw [hencode] at hnz
      exact hnz
    rw [hencode]
    exact inv_mul_cancel₀ hd
  rw [hQ, BLCSeedLines.psi_affine_constant, mul_add, ← mul_assoc, mul_comm ((encode hidden)⁻¹) (algebraMap (ZMod 2) F u),
    mul_assoc, hmerge, mul_one]

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- The extracted witness coordinates: corrections plus the common slope. -/
def extractedWitness (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (u : Fin (s + (wit + rnd)) → ZMod 2) :
    Fin wit → ZMod 2 :=
  fun j => aux.witnessCorrection j + u (Spec.BLC.witnessIndex j)

/-- The extracted witness line of a coordinate. -/
def witnessLine (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (u : Fin (s + (wit + rnd)) → ZMod 2) (j : Fin wit) : F[X] :=
  C (algebraMap (ZMod 2) F (extractedWitness aux u j)) +
    C (Spec.BLC.psi xi (interceptMatrix p salt full randomCount enough (Spec.BLC.witnessIndex j))) * X

/-- The extracted randomness line of a coordinate. -/
def randomnessLine (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (u : Fin (s + (wit + rnd)) → ZMod 2) (j : Fin rnd) : F[X] :=
  C (algebraMap (ZMod 2) F (u (Spec.BLC.randomnessIndex j))) +
    C (Spec.BLC.psi xi (interceptMatrix p salt full randomCount enough (Spec.BLC.randomnessIndex j))) * X

theorem witnessLine_constant (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (u : Fin (s + (wit + rnd)) → ZMod 2) (j : Fin wit) :
    (witnessLine xi p salt full randomCount enough aux u j).eval 0 = algebraMap (ZMod 2) F (extractedWitness aux u j) := by
  simp [witnessLine]

omit [Algebra (ZMod 2) F] in
theorem line_degree (a b : F) : (C a + C b * X : F[X]).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
  exact (natDegree_C_mul_le _ _).trans (by simp)

/-- The candidate middle's values are the lines evaluated at the inverted
challenge, so the composed verifier's recomputation is the composed prover
polynomial of the lines evaluated there. -/
theorem verifier_eq_prover_lines {r k w : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (xi : F) (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (salt : Bits lambda) (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (selectorCount widths * w + lambda * (widths.length - 1)) ≤ 8 * randomCount)
    (aux : Spec.BLCCommit.Auxiliary tau s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hidden : Fin tau → Fin (2 ^ kappa)) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (u : Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2)
    (hu : ∀ e c, Spec.BLCSeedFold.slope p salt full randomCount enough aux e c = u c)
    (hencode : encode = fun hidden => Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hnz : encode hidden ≠ 0) :
    verifierRun widths hsize xi (encode hidden)⁻¹ gamma gammaPrime H' y
      (fun j => algebraMap (ZMod 2) F (aux.witnessCorrection j) + (encode hidden)⁻¹ *
        Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.witnessIndex j)))
      (fun j => (encode hidden)⁻¹ *
        Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.randomnessIndex j))) =
    (proverRun widths hsize xi gamma gammaPrime H' y (witnessLine xi p salt full randomCount enough aux u)
      (randomnessLine xi p salt full randomCount enough u)).eval (encode hidden)⁻¹ := by
  rw [PIOPComposition.verifier_evaluates_prover]
  congr 1
  · funext j
    rw [SlopeConsistencyLink.candidate_witness_constant_slope xi p salt full randomCount enough aux hidden encode j
      (u (Spec.BLC.witnessIndex j)) (fun e => hu e _) hencode hnz]
    simp only [witnessLine, extractedWitness, eval_add, eval_mul, eval_C, eval_X]
    ring
  · funext j
    rw [candidate_randomness_constant_slope xi p salt full randomCount enough aux hidden encode j
      (u (Spec.BLC.randomnessIndex j)) (fun e => hu e _) hencode hnz]
    simp only [randomnessLine, eval_add, eval_mul, eval_C, eval_X]
    ring

omit [Algebra (ZMod 2) F] in
/-- Equal restored and hashed tuples: the transmitted higher coefficients are
the hashed tail and the recomputed value is the hashed polynomial's value. -/
theorem restored_identity {n : Nat} (delta value : F) (hdelta : delta ≠ 0) (higher : Fin n → F)
    (coefficients : Fin (n + 1) → F) (h : restoredCoefficients delta value higher = coefficients) :
    higher = Fin.tail coefficients ∧ value = coefficients 0 * delta + higherEvaluation (Fin.tail coefficients) delta := by
  have htail : higher = Fin.tail coefficients := by
    funext j
    have := congrFun h j.succ
    simpa [restoredCoefficients, Fin.cons_succ, Fin.tail] using this
  have h0 := congrFun h 0
  simp only [restoredCoefficients, Fin.cons_zero, Spec.recoverAlphaOne] at h0
  refine ⟨htail, ?_⟩
  rw [← htail, ← h0]
  field_simp
  ring

omit [Algebra (ZMod 2) F] in
theorem coefficientPolynomial_eval {n : Nat} (coefficients : Fin (n + 1) → F) (delta : F) :
    (coefficientPolynomial coefficients).eval delta =
      coefficients 0 * delta + higherEvaluation (Fin.tail coefficients) delta := by
  simp only [coefficientPolynomial, Fin.sum_univ_succ, eval_add, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X,
    Fin.val_zero, zero_add, pow_one, higherEvaluation, Fin.tail, Fin.val_succ]

/-- An accepting transcript with the extracted lines: the difference between
the composed prover polynomial of the lines and the hashed coefficient
polynomial vanishes at the inverted challenge. -/
theorem difference_vanishes {r k w higherCount : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (xi : F) (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (salt : Bits lambda) (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (selectorCount widths * w + lambda * (widths.length - 1)) ≤ 8 * randomCount)
    (aux : Spec.BLCCommit.Auxiliary tau s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hidden : Fin tau → Fin (2 ^ kappa)) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (u : Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2)
    (hu : ∀ e c, Spec.BLCSeedFold.slope p salt full randomCount enough aux e c = u c)
    (hencode : encode = fun hidden => Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hnz : encode hidden ≠ 0) (higher : Fin higherCount → F) (coefficients : Fin (higherCount + 1) → F)
    (haccept : restoredCoefficients (encode hidden)⁻¹
      (verifierRun widths hsize xi (encode hidden)⁻¹ gamma gammaPrime H' y
        (fun j => algebraMap (ZMod 2) F (aux.witnessCorrection j) + (encode hidden)⁻¹ *
          Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.witnessIndex j)))
        (fun j => (encode hidden)⁻¹ *
          Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.randomnessIndex j))))
      higher = coefficients) :
    (proverRun widths hsize xi gamma gammaPrime H' y (witnessLine xi p salt full randomCount enough aux u)
        (randomnessLine xi p salt full randomCount enough u) - coefficientPolynomial coefficients).eval (encode hidden)⁻¹ = 0 := by
  rw [verifier_eq_prover_lines widths hsize xi gamma gammaPrime H' y p salt full randomCount enough aux hidden encode u hu
    hencode hnz] at haccept
  obtain ⟨_, hvalue⟩ := restored_identity _ _ (inv_ne_zero hnz) higher coefficients haccept
  rw [eval_sub, hvalue, coefficientPolynomial_eval, sub_self]

end
end SDitH.Proofs.PIOPExtraction
