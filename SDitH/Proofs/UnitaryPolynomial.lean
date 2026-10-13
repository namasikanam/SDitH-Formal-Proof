import SDitH.Spec.UnitaryPolynomial
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace SDitH.Proofs.UnitaryPolynomial

open Spec.UnitaryPolynomial Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem exponent_injective {r : Nat} : Function.Injective (@exponent r) := by
  intro p q h
  have he : finProdFinEquiv (p.2, p.1) = finProdFinEquiv (q.2, q.1) := Fin.ext h
  have hp := finProdFinEquiv.injective he
  exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)

theorem diagonal_exponent {r : Nat} (j : Fin (r - 1)) :
    exponent (j.castLE (Nat.sub_le r 1), j) = (r + 1) * j.val := by
  simp only [exponent, Fin.val_castLE]
  ring

/-- Expand the actual printed arithmetic, keeping its missing final index in
the second and third sums. -/
theorem check_expansion {r : Nat} (bits : Fin r → R) :
    check bits = crossTerms bits - diagonalTerms bits := by
  unfold check Spec.PIOPArithmetic.unitaryCheck crossTerms diagonalTerms
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [exponent, ← C_mul_X_pow_eq_monomial, map_mul, pow_add]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [← C_mul_X_pow_eq_monomial, mul_comm]

theorem crossTerms_coeff {r : Nat} (bits : Fin r → R) (p : Fin r × Fin (r - 1)) :
    (crossTerms bits).coeff (exponent p) = bits p.1 * bits (p.2.castLE (Nat.sub_le r 1)) := by
  classical
  simp only [crossTerms, finset_sum_coeff, coeff_monomial]
  have he (q : Fin r × Fin (r - 1)) : exponent q = exponent p ↔ q = p :=
    exponent_injective.eq_iff
  simp only [he]
  exact Finset.sum_ite_eq_of_mem' Finset.univ p
    (fun q => bits q.1 * bits (q.2.castLE (Nat.sub_le r 1))) (Finset.mem_univ p)

/-- Every off-diagonal coefficient is exactly the corresponding bit product;
neither cancellation nor evaluation in an extension field is assumed here. -/
theorem off_diagonal_coeff {r : Nat} (bits : Fin r → R)
    (i : Fin r) (j : Fin (r - 1)) (hne : i ≠ j.castLE (Nat.sub_le r 1)) :
    (check bits).coeff (exponent (i, j)) = bits i * bits (j.castLE (Nat.sub_le r 1)) := by
  rw [check_expansion, coeff_sub, crossTerms_coeff]
  have hd : (diagonalTerms bits).coeff (exponent (i, j)) = 0 := by
    simp only [diagonalTerms, finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro k _
    have he : (r + 1) * k.val ≠ exponent (i, j) := by
      intro h
      rw [← diagonal_exponent k] at h
      have hp := exponent_injective h
      have hi := congrArg Prod.fst hp
      have hj := congrArg Prod.snd hp
      change k = j at hj
      subst k
      exact hne hi.symm
    simp [coeff_monomial, he]
  rw [hd, sub_zero]

theorem check_zero_implies_pairwise {r : Nat} (bits : Fin r → R) (h : check bits = 0) :
    PairwiseZero bits := by
  intro i j hij
  have hshort (a : Fin r) (b : Fin (r - 1)) (hab : a ≠ b.castLE (Nat.sub_le r 1)) :
      bits a * bits (b.castLE (Nat.sub_le r 1)) = 0 := by
    have hc := congrArg (fun p : R[X] => p.coeff (exponent (a, b))) h
    simpa only [off_diagonal_coeff bits a b hab, coeff_zero] using hc
  by_cases hj : j.val < r - 1
  · exact hshort i ⟨j.val, hj⟩ hij
  · have hi : i.val < r - 1 := by
      have hi' := i.isLt
      have hj' := j.isLt
      have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
      omega
    simpa [mul_comm] using hshort j ⟨i.val, hi⟩ (Ne.symm hij)

theorem pairwise_implies_check_zero {r : Nat} (bits : Fin r → R)
    (hid : ∀ i, bits i * bits i = bits i) (hpair : PairwiseZero bits) : check bits = 0 := by
  classical
  rw [check_expansion, sub_eq_zero]
  unfold crossTerms diagonalTerms
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (j.castLE (Nat.sub_le r 1))]
  · rw [hid, diagonal_exponent]
  · intro i _ hne
    rw [hpair i _ hne]
    simp
  · simp

theorem check_zero_iff_pairwise {r : Nat} (bits : Fin r → R)
    (hid : ∀ i, bits i * bits i = bits i) : check bits = 0 ↔ PairwiseZero bits :=
  ⟨check_zero_implies_pairwise bits, pairwise_implies_check_zero bits hid⟩

theorem binary_check_zero_iff_pairwise {r : Nat} (bits : Fin r → ZMod 2) :
    check bits = 0 ↔ PairwiseZero bits := by
  apply check_zero_iff_pairwise
  intro i
  simpa only [pow_two] using ZMod.pow_card (bits i)

theorem binary_check_zero_iff_atMostOne {r : Nat} (bits : Fin r → ZMod 2) :
    check bits = 0 ↔ AtMostOne bits := by
  rw [binary_check_zero_iff_pairwise]
  constructor
  · intro h i j hi hj
    by_contra hne
    exact (mul_ne_zero hi hj) (h i j hne)
  · intro h i j hij
    by_cases hi : bits i = 0
    · simp [hi]
    · have hj : bits j = 0 := by
        by_contra hj
        exact hij (h i j hi hj)
      simp [hj]

/-- All stored selector widths in the binary tables are at most three, so
every D(Y) occupies fewer than 32 coefficients. This is an upper bound; the
printed exact-degree equality need not hold for a zero polynomial. -/
theorem check_degree_lt_32 {r : Nat} (bits : Fin r → R) (hr : r ≤ 3) :
    (check bits).natDegree < 32 := by
  have hc : (crossTerms bits).natDegree ≤ 31 := by
    unfold crossTerms
    apply natDegree_sum_le_of_forall_le
    intro p _
    apply (natDegree_monomial_le _).trans
    have hi := p.1.isLt
    have hj := p.2.isLt
    have hm : r * p.2.val ≤ 3 * 1 := Nat.mul_le_mul hr (by omega)
    dsimp [exponent]
    omega
  have hd : (diagonalTerms bits).natDegree ≤ 31 := by
    unfold diagonalTerms
    apply natDegree_sum_le_of_forall_le
    intro j _
    apply (natDegree_monomial_le _).trans
    have hj := j.isLt
    have hm : (r + 1) * j.val ≤ 4 * 1 := Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [check_expansion]
  exact lt_of_le_of_lt ((natDegree_sub_le _ _).trans (max_le hc hd)) (by decide)

end SDitH.Proofs.UnitaryPolynomial
