import Mathlib.Algebra.BigOperators.Field

/-! Algebraic definitions used on printed pp. 5–7 and Algorithm 4 line 9. -/

namespace SDitH.Spec

open scoped BigOperators

variable {F I : Type*} [Field F] [Fintype I]

/-- The degree-one polynomial of §2.1 evaluated at `x`. -/
def avcLine (φ r : I → F) (x : F) : F :=
  (∑ i, r i) * x - ∑ i, φ i * r i

/-- Opening with the hidden contribution omitted. -/
noncomputable def avcOpen (φ r : I → F) (hidden : I) : F := by
  classical
  exact ∑ i ∈ Finset.univ.erase hidden, (φ hidden - φ i) * r i

/-- Algorithm 4 line 9, with the higher-degree contribution already summed. -/
def recoverAlphaOne (Δ pα higher : F) : F := Δ⁻¹ * (pα - higher)

end SDitH.Spec
