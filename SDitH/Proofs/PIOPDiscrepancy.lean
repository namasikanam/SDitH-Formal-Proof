import SDitH.Spec.PIOP
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

/-! Kernel-checked investigation of the literal equations (1) and (2).
This is a source discrepancy, not an attack on an implementation. -/

namespace SDitH.Proofs

open Polynomial
open SDitH.Spec.PIOP

variable {F : Type*} [Field F]

/-- With one zero constraint, `P₀ = X` gives the honest output `Pα = X²`. -/
theorem zero_constraint_prover :
    proverPolynomial (F := F) (n := 1) (m := 1) (fun _ => 0) (fun _ => 1)
      (fun _ => X) X = X ^ 2 := by
  simp [proverPolynomial, substitute, pow_two]

/-- At any nonzero challenge other than one, the literal verifier rejects it. -/
theorem literal_rejects_honest (Δ : F) (h₀ : Δ ≠ 0) (h₁ : Δ ≠ 1) :
    ¬ honestLiteralAccepts (n := 1) (m := 1) (fun _ => 0) (fun _ => 1)
      (fun _ => X) X Δ := by
  intro h
  have heq : Δ ^ 2 * Δ = Δ ^ 2 := by
    simpa [honestLiteralAccepts, literalVerifier, zero_constraint_prover,
      verifierRhs, pow_two] using h.2
  have hz : Δ ^ 2 ≠ 0 := pow_ne_zero _ h₀
  apply h₁
  exact (mul_left_cancel₀ hz) (by simpa using heq)

/-- Every finite field with more than two elements has a challenge for the example. -/
theorem exists_nonbinary_element [Fintype F] (hcard : 2 < Fintype.card F) :
    ∃ Δ : F, Δ ≠ 0 ∧ Δ ≠ 1 := by
  classical
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [h x hx]
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_univ, Finset.card_pair (zero_ne_one : (0 : F) ≠ 1)] at hc
  omega

/-- The counterexample occurs over the actual Category-I field size `2^128`.
The witness is zero, its one public constraint is zero, the committed witness
polynomial is `X`, and the masking polynomial is `X` (the degree-2 protocol).
No commitment failure or inconsistent opening is involved. -/
theorem categoryI_literal_completeness_counterexample :
    ∃ Δ : GaloisField 2 128,
      Δ ≠ 0 ∧
      HonestInputs (F := GaloisField 2 128) (n := 1) (m := 1) 2
        (fun _ => 0) (fun _ => 0) (fun _ => X) X ∧
      ¬ honestLiteralAccepts (n := 1) (m := 1) (fun _ => 0) (fun _ => 1)
        (fun _ => X) X Δ := by
  letI : Fintype (GaloisField 2 128) := Fintype.ofFinite _
  have hc : 2 < Fintype.card (GaloisField 2 128) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 128 (by decide)]
    norm_num
  obtain ⟨Δ, h₀, h₁⟩ := exists_nonbinary_element hc
  refine ⟨Δ, h₀, ?_, literal_rejects_honest Δ h₀ h₁⟩
  simp [HonestInputs, ValidWitness]

end SDitH.Proofs
