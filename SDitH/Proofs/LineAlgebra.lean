import SDitH.Spec.LineAlgebra
import Mathlib.Tactic

namespace SDitH.Proofs

open scoped BigOperators
open Spec

variable {F I : Type*} [Field F] [Fintype I]

/-- The hidden seed's coefficient is zero, so all other seeds determine this
evaluation, exactly as on printed p. 5. This is correctness algebra only. -/
theorem avc_open_evaluates (φ r : I → F) (hidden : I) :
    avcOpen φ r hidden = avcLine φ r (φ hidden) := by
  classical
  have h : (∑ i ∈ Finset.univ.erase hidden, (φ hidden - φ i) * r i) =
      ∑ i, (φ hidden - φ i) * r i := by
    simp
  unfold avcOpen avcLine
  rw [h]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The reciprocal encoding on printed p. 7, for a nonzero opening challenge. -/
theorem reciprocal_line (w r Δ : F) (hΔ : Δ ≠ 0) :
    Δ * (w * Δ⁻¹ + r) = w + r * Δ := by
  field_simp

/-- Algorithm 4 recovers the omitted coefficient on an honest evaluation.
No hash-security or BLC-correctness claim is assumed here. -/
theorem recover_alpha_one (α₁ Δ higher : F) (hΔ : Δ ≠ 0) :
    recoverAlphaOne Δ (α₁ * Δ + higher) higher = α₁ := by
  simp [recoverAlphaOne, hΔ, mul_comm]

end SDitH.Proofs
