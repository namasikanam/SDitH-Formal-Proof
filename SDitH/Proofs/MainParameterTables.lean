import SDitH.Spec.MainParameterTables
import SDitH.Spec.ReportedBenchmarks
import SDitH.Proofs.VariantParameters
import SDitH.Proofs.KeySizeBoundary

namespace SDitH.Proofs.MainParameterTables

open Spec Spec.MainParameterTables Spec.RSDParameters

theorem table4_proof_parameters : table4.map Row.proof = hashProofParameters := by decide
theorem table5_proof_parameters : table5.map Row.proof = cipherProofParameters := by decide

/-- Every published binary key and signature size matches the displayed
formula. This proves arithmetic agreement, not actual codec length or protocol
correctness for the inconsistent tensor dimensions. -/
theorem table4_sizes : ∀ row ∈ table4,
    publicKeyBytes row.rsd = row.publicBytes ∧ secretKeyBytes row.rsd = row.secretBytes ∧
      signatureBits row.rsd row.proof = 8 * row.signatureBytes := by decide

theorem table5_sizes : ∀ row ∈ table5,
    publicKeyBytes row.rsd = row.publicBytes ∧ secretKeyBytes row.rsd = row.secretBytes ∧
      signatureBits row.rsd row.proof = 8 * row.signatureBytes := by decide

theorem table4_5_key_sizes_match :
    table4.map (fun row => (row.rsd, row.publicBytes, row.secretBytes)) =
      table5.map (fun row => (row.rsd, row.publicBytes, row.secretBytes)) := by decide

theorem binary_exponent_budgets : ∀ row ∈ table4 ++ table5,
    row.proof.kappa * row.proof.tau + row.proof.grindingBits = row.rsd.lambda + 2 := by decide

/-- Only the numerical degree-four budget is proved. The actual protocol
bound, oracle assumptions and grinding argument are separate obligations. -/
theorem binary_vole_budgets : ∀ row ∈ table4 ++ table5,
    Spec.VariantParameters.VoleBudget row.rsd.lambda 4 row.proof.kappa row.proof.tau
      row.proof.grindingBits := by
  intro row hr
  exact VariantParameters.vole_budget_of_exponents (binary_exponent_budgets row hr).ge

theorem table4_short_kappas_disagree :
    ((rowsFor .short table4).map (fun row => row.proof.kappa)) = [11,11,11] ∧
      ((rowsFor .short table4).map (fun row => row.proof.kappa)) ≠ proseShortKappas := by decide

theorem table4_fast_kappas_disagree : ∀ row ∈ rowsFor .fast table4,
    row.proof.kappa = 7 ∧ row.proof.kappa ≠ proseFastKappa := by decide

theorem table4_fast_grinding_disagrees : ∀ row ∈ rowsFor .fast table4,
    row.proof.grindingBits ≠ proseFastGrinding := by decide

theorem table4_short_grinding_disagrees :
    ∃ row ∈ rowsFor .short table4, row.proof.grindingBits ∉ proseShortGrindingValues := by decide

/-- The row labels correspond; the timing values themselves remain reported
empirical data, with no runtime theorem or generated benchmark evidence. -/
theorem benchmark_row_labels :
    ReportedBenchmarks.table6.map (fun row => (row.lambda, row.tradeoff)) =
      table4.map (fun row => (row.rsd.lambda, row.tradeoff)) ∧
    ReportedBenchmarks.table6.map (fun row => (row.lambda, row.tradeoff)) =
      table5.map (fun row => (row.rsd.lambda, row.tradeoff)) := by decide

theorem table_key_capacity : ∀ row ∈ table4 ++ table5,
    ceilBytes (row.rsd.lambda + row.rsd.codimension) = row.publicBytes ∧
    ceilBytes (row.rsd.lambda + row.rsd.codimension + row.rsd.witnessBits) = row.secretBytes := by decide

/-- The table's public-key byte count is the necessary lower bound for an
injective fixed-width encoding of every parsed public value. No injectivity or
length law is asserted about the source's unprovided Serialize implementation. -/
theorem public_encoding_minimum (row : Row) (hr : row ∈ table4 ++ table5)
    (encoding : KeyGeneration.Serialization row.rsd.lambda row.rsd.codimension) (bytes : Nat)
    (hlength : KeySizeBoundary.HasBitLength encoding.encodePublic (8 * bytes))
    (hinj : Function.Injective encoding.encodePublic) : row.publicBytes ≤ bytes := by
  rw [← (table_key_capacity row hr).1]
  exact KeySizeBoundary.public_serialization_byte_lower_bound encoding bytes hlength hinj

theorem secret_encoding_minimum (row : Row) (hr : row ∈ table4 ++ table5)
    (encoding : KeyGeneration.Serialization row.rsd.lambda row.rsd.codimension) (bytes : Nat)
    (hlength : KeySizeBoundary.HasBitLength
      (fun key : KeySizeBoundary.SizedSecretKey row.rsd.lambda row.rsd.codimension row.rsd.witnessBits =>
        encoding.encodeSecret key.val) (8 * bytes))
    (hinj : Function.Injective
      (fun key : KeySizeBoundary.SizedSecretKey row.rsd.lambda row.rsd.codimension row.rsd.witnessBits =>
        encoding.encodeSecret key.val)) : row.secretBytes ≤ bytes := by
  rw [← (table_key_capacity row hr).2]
  exact KeySizeBoundary.secret_serialization_byte_lower_bound encoding bytes hlength hinj

end SDitH.Proofs.MainParameterTables
