import SDitH.Proofs.FieldRepresentation
import SDitH.Proofs.FieldCertificates.CategoryI
import SDitH.Proofs.FieldCertificates.CategoryIII
import SDitH.Proofs.FieldCertificates.CategoryV

/-! Irreducibility of the exact Table-2 moduli, obtained from proved algebra
and kernel-checked binary-polynomial certificates. -/

namespace SDitH.Proofs.FieldIrreducibility

open Polynomial Spec.FieldRepresentation FieldRepresentation BinaryIrreducibility

set_option maxRecDepth 4096

def checkIndices : Category → List Nat
  | .i => [64]
  | .iii => [64, 96]
  | .v => [128]

theorem check_coverage (category : Category) (d : Nat) (hd : 0 < d)
    (hle : d ≤ (modulus category).natDegree / 2) (hdiv : d ∣ (modulus category).natDegree) :
    ∃ m ∈ checkIndices category, d ∣ m := by
  rw [modulus_degree] at hle hdiv
  cases category with
  | i =>
    have hc : ∀ d : Fin 65, 0 < d.val → d.val ∣ 128 → d.val ∣ 64 := by decide
    exact ⟨64, by simp [checkIndices], hc ⟨d, by simpa [width] using Nat.lt_succ_of_le hle⟩ hd hdiv⟩
  | iii =>
    have hc : ∀ d : Fin 97, 0 < d.val → d.val ∣ 192 → d.val ∣ 64 ∨ d.val ∣ 96 := by decide
    rcases hc ⟨d, by simpa [width] using Nat.lt_succ_of_le hle⟩ hd hdiv with h | h
    · exact ⟨64, by simp [checkIndices], h⟩
    · exact ⟨96, by simp [checkIndices], h⟩
  | v =>
    have hc : ∀ d : Fin 129, 0 < d.val → d.val ∣ 256 → d.val ∣ 128 := by decide
    exact ⟨128, by simp [checkIndices], hc ⟨d, by simpa [width] using Nat.lt_succ_of_le hle⟩ hd hdiv⟩

/-- Transfer a checked certificate through the proved equality with the source
polynomial. Keeping the exponent symbolic here avoids evaluating enormous
polynomial powers while Lean compares equivalent algebra instances. -/
theorem irreducible_from_certificate (category : Category)
    (f : BinaryPolynomialCertificate.Bits) (n : Nat)
    (heq : BinaryPolynomialCertificate.polynomial f = modulus category)
    (hdeg : (modulus category).natDegree = n)
    (hfull : BinaryPolynomialCertificate.polynomial f ∣
      (X ^ (2 ^ n) - X : (ZMod 2)[X]))
    (hchecks : ∀ m ∈ checkIndices category,
      IsCoprime (BinaryPolynomialCertificate.polynomial f) (X ^ (2 ^ m) - X)) :
    Irreducible (modulus category) := by
  apply (congrArg Irreducible heq).mp
  apply irreducible_of_frobenius_checks (BinaryPolynomialCertificate.polynomial f)
    (by rw [heq]; exact (modulus_monic category).ne_zero)
    (by
      rw [heq, modulus_degree]
      exact lt_of_lt_of_le (by decide : 0 < 128) (width_ge_128 category)) (checkIndices category)
  · have hd : (BinaryPolynomialCertificate.polynomial f).natDegree = n := by rw [heq, hdeg]
    rw [hd]
    exact hfull
  · intro d hd hle hdiv
    apply check_coverage category d hd
    · simpa only [heq] using hle
    · simpa only [heq] using hdiv
  · exact hchecks

theorem modulus_irreducible (category : Category) : Irreducible (modulus category) := by
  cases category with
  | i =>
    apply irreducible_from_certificate .i FieldCertificates.CategoryI.modulusBits 128
      FieldCertificates.CategoryI.polynomial_modulusBits (modulus_degree .i)
      FieldCertificates.CategoryI.full
    intro m hm
    simp only [checkIndices, List.mem_singleton] at hm
    subst m
    exact FieldCertificates.CategoryI.coprime64
  | iii =>
    apply irreducible_from_certificate .iii FieldCertificates.CategoryIII.modulusBits 192
      FieldCertificates.CategoryIII.polynomial_modulusBits (modulus_degree .iii)
      FieldCertificates.CategoryIII.full
    intro m hm
    simp only [checkIndices, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact FieldCertificates.CategoryIII.coprime64
    · exact FieldCertificates.CategoryIII.coprime96
  | v =>
    apply irreducible_from_certificate .v FieldCertificates.CategoryV.modulusBits 256
      FieldCertificates.CategoryV.polynomial_modulusBits (modulus_degree .v)
      FieldCertificates.CategoryV.full
    intro m hm
    simp only [checkIndices, List.mem_singleton] at hm
    subst m
    exact FieldCertificates.CategoryV.coprime128

/-- The field structure is installed only in this proof module, after the exact
submitted polynomial's irreducibility has been discharged. -/
instance modulusIrreducible (category : Category) : Fact (Irreducible (modulus category)) :=
  ⟨modulus_irreducible category⟩

noncomputable instance quotientField (category : Category) : Field (QuotientRing category) :=
  inferInstanceAs (Field (AdjoinRoot (modulus category)))

noncomputable instance quotientFintype (category : Category) : Fintype (QuotientRing category) :=
  Fintype.ofEquiv _ (AdjoinRoot.powerBasis' (modulus_monic category)).basis.equivFun.toEquiv.symm

theorem quotient_card (category : Category) :
    Fintype.card (QuotientRing category) = 2 ^ width category := by
  have h := Fintype.card_congr
    (AdjoinRoot.powerBasis' (modulus_monic category)).basis.equivFun.toEquiv
  simpa only [Fintype.card_fun, ZMod.card, Fintype.card_fin, AdjoinRoot.powerBasis'_dim,
    modulus_degree] using h

end SDitH.Proofs.FieldIrreducibility
