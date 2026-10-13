import SDitH.Spec.VariantParameters
import Mathlib.Tactic

namespace SDitH.Proofs.VariantParameters

open Spec Spec.RSDParameters Spec.VariantParameters

theorem ceilMultiple_covers (granularity bits : Nat) (hg : 0 < granularity) :
    bits ≤ ceilMultiple granularity bits := by
  have hr := Nat.mod_lt (bits + granularity - 1) hg
  have hd := Nat.mod_add_div (bits + granularity - 1) granularity
  unfold ceilMultiple
  omega

theorem ceilMultiple_lt_next (granularity bits : Nat) (hg : 0 < granularity) :
    ceilMultiple granularity bits < bits + granularity := by
  have hd := Nat.mod_add_div (bits + granularity - 1) granularity
  unfold ceilMultiple
  omega

theorem ceilMultiple_minimal (granularity bits k : Nat) (hg : 0 < granularity)
    (h : bits ≤ granularity * k) : ceilMultiple granularity bits ≤ granularity * k := by
  unfold ceilMultiple
  apply Nat.mul_le_mul_left
  apply Nat.lt_succ_iff.mp
  apply (Nat.div_lt_iff_lt_mul hg).mpr
  rw [Nat.succ_mul]
  have he : bits + granularity - 1 < bits + granularity := by omega
  nlinarith

theorem ceilMultiple_eight (bits : Nat) : ceilMultiple 8 bits = ceil8 bits := by
  simp [ceilMultiple, ceil8, ceilBytes, show bits + 8 - 1 = bits + 7 by omega]

theorem vole_budget_iff_error (lambda degree kappa tau grindingBits : Nat) :
    VoleBudget lambda degree kappa tau grindingBits ↔
      voleError degree kappa tau grindingBits ≤ 1 / (2 ^ lambda : Rat) := by
  unfold VoleBudget voleError
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  norm_cast

theorem tc_budget_iff_error (lambda degree kappa tau grindingBits : Nat) :
    TCBudget lambda degree kappa tau grindingBits ↔
      tcError degree kappa tau grindingBits ≤ 1 / (2 ^ lambda : Rat) := by
  unfold TCBudget tcError
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  norm_cast

theorem voleError_factorization (degree kappa tau grindingBits : Nat) :
    voleError degree kappa tau grindingBits =
      ((degree : Rat) / ((2 : Rat) ^ kappa) ^ tau) / (2 : Rat) ^ grindingBits := by
  simp [voleError, pow_add, pow_mul, div_div]

theorem tcError_factorization (degree kappa tau grindingBits : Nat) :
    tcError degree kappa tau grindingBits =
      (((degree : Rat) / (2 : Rat) ^ kappa) ^ tau) / (2 : Rat) ^ grindingBits := by
  simp [tcError, div_pow, pow_add, pow_mul, div_div]

theorem simple_opening_substitution (p : RSDParameters) (s : SimpleParameters) (B : Nat) :
    simpleSignatureBits p s B p.arities.length =
      signatureBits p ⟨s.kappa, s.tau, 0, s.tau * s.kappa, B⟩ := by
  simp [simpleSignatureBits, signatureBits, Nat.mul_assoc]

/-- All F256 key and signature sizes agree at constraint degree four. -/
theorem table8_sizes : ∀ row ∈ table8,
    scaledPublicKeyBytes row.rsd 8 = row.publicBytes ∧
    scaledSecretKeyBytes row.rsd 8 = row.secretBytes ∧
    ceilBytes (scaledSignatureBits row.rsd row.proof 8 4) = row.signatureBytes := by decide

theorem table8_same_proof_parameters : table8.map ScaledRow.proof = hashProofParameters := by decide

/-- Using the tensor depth as the constraint degree would not reproduce the
table. The scaling-degree theorem explains the extra degree. -/
theorem table8_tensor_depth_not_signature_degree : ∀ row ∈ table8,
    row.rsd.arities.length = 3 ∧
    ceilBytes (scaledSignatureBits row.rsd row.proof 8 row.rsd.arities.length) < row.signatureBytes := by
  decide

theorem table9_sizes : ∀ row ∈ table9,
    ceilBytes (tcSignatureBits row.rsd row.proof 4) = row.signatureBytes := by decide

/-- Table 10 at the main construction's B=16 and degree four. Both choices
are explicit here rather than silently made fields of the printed table. -/
theorem table10_sizes : ∀ row ∈ table10,
    ceilBytes (simpleSignatureBits row.rsd row.proof 16 4) = row.signatureBytes := by decide

/-- Each printed percentage is within half a percentage point of the exact
reduction relative to the variant's size. No unstated rounding rule is required. -/
theorem table9_percentage_intervals : ∀ row ∈ table9,
    (2 * row.reportedReductionPercent - 1) * row.signatureBytes ≤
      200 * (row.signatureBytes - row.baselineBytes) ∧
    200 * (row.signatureBytes - row.baselineBytes) ≤
      (2 * row.reportedReductionPercent + 1) * row.signatureBytes := by decide

theorem table10_percentage_intervals : ∀ row ∈ table10,
    (2 * row.reportedReductionPercent - 1) * row.signatureBytes ≤
      200 * (row.signatureBytes - row.baselineBytes) ∧
    200 * (row.signatureBytes - row.baselineBytes) ≤
      (2 * row.reportedReductionPercent + 1) * row.signatureBytes := by decide

theorem main_consistency_slack : ∀ s ∈ hashProofParameters, s.consistencySlack = 16 := by decide

theorem table8_degree_budget : ∀ row ∈ table8,
    row.proof.kappa * row.proof.tau + row.proof.grindingBits = row.rsd.lambda + 2 := by decide

theorem table9_degree_budget : ∀ row ∈ table9,
    row.proof.tau * (row.proof.kappa - 2) + row.proof.grindingBits = row.rsd.lambda := by decide

theorem table10_degree_budget : ∀ row ∈ table10,
    row.rsd.lambda + 2 ≤ row.proof.kappa * row.proof.tau := by decide

theorem vole_budget_of_exponents {lambda kappa tau grindingBits : Nat}
    (h : lambda + 2 ≤ kappa * tau + grindingBits) :
    VoleBudget lambda 4 kappa tau grindingBits := by
  unfold VoleBudget
  calc
    4 * 2 ^ lambda = 2 ^ (lambda + 2) := by rw [pow_add]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) h

theorem tc_budget_of_exponents {lambda kappa tau grindingBits : Nat}
    (hk : 2 ≤ kappa) (h : lambda ≤ tau * (kappa - 2) + grindingBits) :
    TCBudget lambda 4 kappa tau grindingBits := by
  unfold TCBudget
  calc
    4 ^ tau * 2 ^ lambda = 2 ^ (2 * tau + lambda) := by
      rw [pow_add, pow_mul]
      norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      have he : tau * kappa = tau * (kappa - 2) + 2 * tau := by
        have ht := congrArg (fun v => tau * v) (Nat.sub_add_cancel hk)
        simpa [Nat.mul_add, Nat.mul_comm] using ht.symm
      nlinarith)

/-- These verify only the displayed numerical budgets. They do not turn the
heuristic or omitted security arguments into proved protocol soundness. -/
theorem table8_vole_budgets : ∀ row ∈ table8,
    VoleBudget row.rsd.lambda 4 row.proof.kappa row.proof.tau row.proof.grindingBits := by
  intro row hrow
  apply vole_budget_of_exponents
  exact (table8_degree_budget row hrow).ge

theorem table9_tc_budgets : ∀ row ∈ table9,
    TCBudget row.rsd.lambda 4 row.proof.kappa row.proof.tau row.proof.grindingBits := by
  intro row hrow
  apply tc_budget_of_exponents
  · have h : ∀ row ∈ table9, 2 ≤ row.proof.kappa := by decide
    exact h row hrow
  · exact (table9_degree_budget row hrow).ge

theorem table10_vole_budgets : ∀ row ∈ table10,
    VoleBudget row.rsd.lambda 4 row.proof.kappa row.proof.tau 0 := by
  intro row hrow
  apply vole_budget_of_exponents
  simpa using table10_degree_budget row hrow

end SDitH.Proofs.VariantParameters
