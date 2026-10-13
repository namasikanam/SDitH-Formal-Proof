import SDitH.Spec.Parameters

namespace SDitH.Proofs

open Spec Spec.RSDParameters

/-- All three Table 3 rows violate the exact tensor dimension equation in §2.2.
This does not exclude an unstated padding convention; it records the literal mismatch. -/
theorem table3_tensor_dimensions_fail :
    ¬ TensorDimensionsMatch categoryI ∧
    ¬ TensorDimensionsMatch categoryIII ∧
    ¬ TensorDimensionsMatch categoryV := by decide

/-- The analogous equation does hold for all three Table 7 F256 rows. -/
theorem table7_tensor_dimensions_match :
    TensorDimensionsMatch categoryI256 ∧
    TensorDimensionsMatch categoryIII256 ∧
    TensorDimensionsMatch categoryV256 := by decide

/-- Table 4's binary key sizes agree with §4.2. -/
theorem binary_key_sizes :
    (publicKeyBytes categoryI, secretKeyBytes categoryI) = (70, 147) ∧
    (publicKeyBytes categoryIII, secretKeyBytes categoryIII) = (98, 208) ∧
    (publicKeyBytes categoryV, secretKeyBytes categoryV) = (132, 275) := by decide

/-- Category III's 256-bit Enc output cannot be parsed losslessly into the
192-bit-per-block byte tuple printed on Algorithm 6 line 5. This identifies a
shape discrepancy; no truncation or alternative parsing rule is supplied. -/
theorem categoryIII_prg_parse_width_mismatch (blocks : Nat) (hb : 0 < blocks) :
    prgCiphertextBits 256 blocks ≠ 8 * prgDeclaredParseBytes 192 blocks := by
  simp only [prgCiphertextBits, prgDeclaredParseBytes]
  omega

end SDitH.Proofs
