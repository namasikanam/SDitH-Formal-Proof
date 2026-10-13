import SDitH.Spec.Parameters
import SDitH.Proofs.Batching

/-! Section 6.1 does not specify the F256 packing map. These statements show
why reusing the binary width lambda unchanged cannot supply an injective
packing for Table 7. They do not identify this adaptation with a specified
F256 protocol, and do not choose a field representation or embedding.
-/

namespace SDitH.Proofs.ScaledPackingBoundary

open Spec Spec.RSDParameters Spec.Batching

/-- Every Table-7 syndrome contains more information than a single element
of the retained large field. The unchanged binary block count is one. -/
theorem unchanged_packing_cardinality (p : RSDParameters)
    (hp : p ∈ [categoryI256, categoryIII256, categoryV256]) :
    (2 ^ p.lambda) ^ blockCount p.codimension p.lambda < 256 ^ p.codimension := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    norm_num [categoryI256, categoryIII256, categoryV256, blockCount]

/-- This obstruction applies to every map with the unchanged binary shape,
not only to the particular powers-of-xi formula. -/
theorem unchanged_packing_not_injective {K F : Type*} [Fintype K] [Fintype F]
    (p : RSDParameters) (hp : p ∈ [categoryI256, categoryIII256, categoryV256])
    (hK : Fintype.card K = 256) (hF : Fintype.card F = 2 ^ p.lambda)
    (packing : (Fin p.codimension → K) → (Fin (blockCount p.codimension p.lambda) → F)) :
    ¬ Function.Injective packing := by
  apply Fintype.not_injective_of_card_lt
  simpa only [Fintype.card_fun, Fintype.card_fin, hK, hF] using
    unchanged_packing_cardinality p hp

/-- Even three large-field elements have insufficient capacity in every row. -/
theorem three_element_capacity (p : RSDParameters)
    (hp : p ∈ [categoryI256, categoryIII256, categoryV256]) :
    (2 ^ p.lambda) ^ 3 < 256 ^ p.codimension := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    norm_num [categoryI256, categoryIII256, categoryV256]

/-- Any injective encoding of the Table-7 syndrome into large-field elements
needs at least four elements. This is a necessary size condition, not a choice
of the unspecified encoding or a proof of a particular four-element map. -/
theorem injective_packing_requires_four {K F : Type*} [Fintype K] [Fintype F]
    (p : RSDParameters) (hp : p ∈ [categoryI256, categoryIII256, categoryV256])
    (hK : Fintype.card K = 256) (hF : Fintype.card F = 2 ^ p.lambda) (blocks : Nat)
    (packing : (Fin p.codimension → K) → (Fin blocks → F))
    (hinj : Function.Injective packing) : 4 ≤ blocks := by
  have hc := Fintype.card_le_of_injective packing hinj
  simp only [Fintype.card_fun, Fintype.card_fin, hK, hF] at hc
  by_contra h
  have hb : blocks ≤ 3 := by omega
  have hpow : (2 ^ p.lambda) ^ blocks ≤ (2 ^ p.lambda) ^ 3 :=
    Nat.pow_le_pow_right (by positivity) hb
  exact (not_lt_of_ge (hc.trans hpow)) (three_element_capacity p hp)

/-- For the actual linear formula this yields a nonzero vector whose packed
value is zero. No hardness assumption or special representation is used. -/
theorem unchanged_packVector_nonzero_kernel {K F : Type*}
    [Field K] [Field F] [Algebra K F] [Fintype K] [Fintype F]
    (p : RSDParameters) (hp : p ∈ [categoryI256, categoryIII256, categoryV256])
    (hK : Fintype.card K = 256) (hF : Fintype.card F = 2 ^ p.lambda) (xi : F) :
    ∃ v : Fin p.codimension → K, v ≠ 0 ∧
      packVector (lambda := p.lambda) xi v = 0 := by
  have hn := unchanged_packing_not_injective p hp hK hF
    (packVector (r := p.codimension) (lambda := p.lambda) xi)
  obtain ⟨x, y, he, hne⟩ := Function.not_injective_iff.mp hn
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  funext block
  change packBlockLinear xi block (x - y) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun he block)

/-- Such a residual is missed by every batching challenge if one reuses the
binary packing width. This is not a claim that the outline specifies that
reuse, nor that this vector is a forged full-protocol transcript. -/
theorem unchanged_batch_nonzero_kernel {K F : Type*}
    [Field K] [Field F] [Algebra K F] [Fintype K] [Fintype F]
    (p : RSDParameters) (hp : p ∈ [categoryI256, categoryIII256, categoryV256])
    (hK : Fintype.card K = 256) (hF : Fintype.card F = 2 ^ p.lambda) (xi : F) :
    ∃ v : Fin p.codimension → K, v ≠ 0 ∧
      ∀ gamma : Fin (blockCount p.codimension p.lambda) → F,
        batchLinearMap xi gamma v = 0 := by
  obtain ⟨v, hv, hpv⟩ := unchanged_packVector_nonzero_kernel p hp hK hF xi
  refine ⟨v, hv, fun gamma => ?_⟩
  rw [Batching.batch_formula, hpv]
  simp

end SDitH.Proofs.ScaledPackingBoundary
