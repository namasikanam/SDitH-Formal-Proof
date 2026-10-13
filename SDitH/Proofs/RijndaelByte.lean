import SDitH.Spec.RijndaelByte
import SDitH.Proofs.RijndaelByteCertificates
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic

namespace SDitH.Proofs.RijndaelByte

open Spec.RijndaelByte Polynomial
open scoped BigOperators

set_option maxRecDepth 512

instance byteFintype : Fintype Byte := Fintype.ofEquiv (Fin (2 ^ 8)) (BitVec.equivFin (m := 8)).toEquiv.symm

theorem modulus_monic : modulus.Monic := by
  dsimp [modulus]
  monicity <;> norm_num

theorem modulus_degree : modulus.natDegree = 8 := by
  dsimp [modulus]
  compute_degree <;> norm_num

instance quotientNontrivial : Nontrivial QuotientRing :=
  AdjoinRoot.nontrivial modulus (by
    intro h
    have hn := Polynomial.natDegree_eq_of_degree_eq_some h
    rw [modulus_degree] at hn
    contradiction)

instance quotientCharP : CharP QuotientRing 2 :=
  CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) QuotientRing) 2 (by decide)

noncomputable def byteBasis : Module.Basis (Fin 8) (ZMod 2) QuotientRing :=
  (AdjoinRoot.powerBasis' modulus_monic).basis.reindex (finCongr modulus_degree)

theorem byteBasis_apply (i : Fin 8) : byteBasis i = generator ^ i.val := by
  rw [byteBasis, Module.Basis.reindex_apply]
  change (AdjoinRoot.powerBasis' modulus_monic).basis
    ((finCongr modulus_degree).symm i) = _
  rw [PowerBasis.coe_basis]
  rfl

theorem coefficient_injective : Function.Injective coefficient := by
  intro a b h
  cases a <;> cases b <;> simp_all [coefficient]

theorem coefficients_bijective : Function.Bijective coefficients := by
  apply (Fintype.bijective_iff_injective_and_card coefficients).mpr
  constructor
  · intro a b hab
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact coefficient_injective (congrFun hab ⟨i, hi⟩)
  · rw [Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]

noncomputable def decodeEquiv : Byte ≃ QuotientRing :=
  (Equiv.ofBijective coefficients coefficients_bijective).trans byteBasis.equivFun.symm.toEquiv

theorem decodeEquiv_apply (b : Byte) : decodeEquiv b = decode b := by
  simp only [decodeEquiv, Equiv.trans_apply, Equiv.ofBijective_apply,
    LinearEquiv.coe_toEquiv, Module.Basis.equivFun_symm_apply, byteBasis_apply,
    Algebra.smul_def, decode]

theorem decode_bijective : Function.Bijective decode := by
  have he : decode = decodeEquiv := by funext b; exact (decodeEquiv_apply b).symm
  rw [he]
  exact decodeEquiv.bijective

theorem coefficient_xor (a b : Bool) : coefficient (a ^^ b) = coefficient a + coefficient b := by
  cases a <;> cases b <;> decide

theorem decode_xor (a b : Byte) : decode (a ^^^ b) = decode a + decode b := by
  simp only [decode, coefficients, BitVec.getLsbD_xor, coefficient_xor, map_add,
    add_mul, Finset.sum_add_distrib]

theorem decode_zero : decode (0#8) = 0 := by
  simp only [decode, coefficients, BitVec.getLsbD_zero, coefficient, Bool.false_eq_true,
    if_false, map_zero, zero_mul, Finset.sum_const_zero]

theorem decode_one : decode (1#8) = 1 := by
  have hc : coefficients (1#8) = fun i : Fin 8 => if i = 0 then 1 else 0 := by
    funext i
    fin_cases i <;> decide
  simp only [decode, hc, apply_ite, map_one, map_zero, ite_mul, zero_mul, one_mul]
  simp

theorem decode_reductionConstant :
    decode (0x1b#8) = generator ^ 4 + generator ^ 3 + generator + 1 := by
  have hc : coefficients (0x1b#8) = ![1, 1, 0, 1, 1, 0, 0, 0] := by
    funext i
    fin_cases i <;> decide
  simp only [decode, hc, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring

theorem generator_eighth : generator ^ 8 = generator ^ 4 + generator ^ 3 + generator + 1 := by
  have h := AdjoinRoot.eval₂_root modulus
  change eval₂ (algebraMap (ZMod 2) QuotientRing) generator modulus = 0 at h
  simp only [modulus, eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  have hc : generator ^ 8 + (generator ^ 4 + generator ^ 3 + generator + 1) = 0 := by
    linear_combination h
  exact (CharTwo.add_eq_zero.mp hc)

theorem decode_xtime (b : Byte) : decode (xtime b) = generator * decode b := by
  rw [xtime, decode_xor]
  cases hb : b.getLsbD 7 with
  | true =>
    simp only [if_true, decode_reductionConstant]
    simp only [decode, Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num only [coefficients, Fin.val_zero, Fin.val_succ, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, decide_true, decide_false, Nat.testBit, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      Bool.not_false, Bool.not_true, hb, coefficient, if_true, if_false, Bool.false_eq_true,
      map_one, map_zero, zero_mul, one_mul, zero_add, add_zero, pow_zero, pow_one]
    linear_combination -generator_eighth
  | false =>
    simp only [Bool.false_eq_true, if_false, decode_zero, add_zero]
    simp only [decode, Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num only [coefficients, Fin.val_zero, Fin.val_succ, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, decide_true, decide_false, Nat.testBit, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      Bool.not_false, Bool.not_true, hb, coefficient, if_true, if_false, Bool.false_eq_true,
      map_one, map_zero, zero_mul, one_mul, zero_add, add_zero, pow_zero, pow_one]
    ring

theorem decode_xtime_iterate (n : Nat) (b : Byte) :
    decode (xtime^[n] b) = generator ^ n * decode b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', decode_xtime, ih, pow_succ]
    ring

theorem decode_mulThrough (a b : Byte) (n : Nat) :
    decode (mulThrough a b n) =
      (∑ i ∈ Finset.range n,
        algebraMap (ZMod 2) QuotientRing (coefficient (a.getLsbD i)) * generator ^ i) * decode b := by
  induction n with
  | zero => simp [mulThrough, decode_zero]
  | succ n ih =>
    rw [mulThrough, decode_xor, ih, Finset.sum_range_succ, add_mul]
    congr 1
    cases h : a.getLsbD n <;> simp only [coefficient, Bool.false_eq_true,
      if_false, if_true, map_zero, map_one, zero_mul, one_mul, decode_zero, decode_xtime_iterate]

theorem decode_mul (a b : Byte) : decode (mul a b) = decode a * decode b := by
  rw [mul, decode_mulThrough]
  apply congrArg (· * decode b)
  exact (Fin.sum_univ_eq_sum_range
    (fun i => algebraMap (ZMod 2) QuotientRing (coefficient (a.getLsbD i)) * generator ^ i) 8).symm

/-- Every nonzero element of the actual polynomial quotient has an inverse.
The witness table was checked for all bytes, and decode is already proved
surjective and multiplicative. No field property is assumed in this argument. -/
theorem quotient_isField : IsField QuotientRing where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {a} ha := by
    obtain ⟨b, rfl⟩ := decode_bijective.surjective a
    have hb : b ≠ 0#8 := by
      intro h
      exact ha (h ▸ decode_zero)
    refine ⟨decode (RijndaelByteCertificates.inverse b), ?_⟩
    rw [← decode_mul, RijndaelByteCertificates.inverse_checked b hb]
    exact decode_one

noncomputable instance quotientField : Field QuotientRing := quotient_isField.toField

noncomputable instance quotientFintype : Fintype QuotientRing :=
  Fintype.ofEquiv Byte decodeEquiv

theorem quotient_card : Fintype.card QuotientRing = 256 := by
  rw [← Fintype.card_congr decodeEquiv,
    Fintype.card_congr (BitVec.equivFin (m := 8)).toEquiv, Fintype.card_fin]
  rfl

theorem decode_ne_zero {b : Byte} (hb : b ≠ 0#8) : decode b ≠ 0 := by
  intro h
  exact hb (decode_bijective.injective (h.trans decode_zero.symm))

theorem sbox_relation (b : Byte) : SboxRelation b (sbox b) := by
  unfold SboxRelation
  by_cases hb : b = 0#8
  · subst b
    change sbox (0#8) = affine (0#8)
    decide
  · rw [if_neg hb]
    refine ⟨RijndaelByteCertificates.inverse b, ?_, RijndaelByteCertificates.sbox_checked b⟩
    rw [← decode_mul, RijndaelByteCertificates.inverse_checked b hb]
    exact decode_one

/-- The literal table is exactly the unique output of the inverse-and-affine
specification, including its exceptional zero case. -/
theorem sbox_relation_iff (b out : Byte) : SboxRelation b out ↔ out = sbox b := by
  constructor
  · intro h
    have hs := sbox_relation b
    unfold SboxRelation at h hs
    by_cases hb : b = 0#8
    · rw [if_pos hb] at h hs
      exact h.trans hs.symm
    · rw [if_neg hb] at h hs
      obtain ⟨u, hu, hout⟩ := h
      obtain ⟨v, hv, hsbox⟩ := hs
      have huv : u = v := decode_bijective.injective
        (mul_left_cancel₀ (decode_ne_zero hb) (hu.trans hv.symm))
      exact hout.trans ((congrArg affine huv).trans hsbox.symm)
  · rintro rfl
    exact sbox_relation b

theorem sbox_bijective : Function.Bijective sbox :=
  ⟨Function.LeftInverse.injective RijndaelByteCertificates.inverse_sbox_checked,
   Function.RightInverse.surjective RijndaelByteCertificates.sbox_inverse_checked⟩

set_option maxRecDepth 4096 in
/-- Bit-for-bit agreement with FIPS 197 equation (5.3), for every byte. -/
theorem affine_bits : ∀ (b : Byte) (i : Fin 8),
    (affine b).getLsbD i.val =
      b.getLsbD i.val ^^ b.getLsbD ((i.val + 4) % 8) ^^
      b.getLsbD ((i.val + 5) % 8) ^^ b.getLsbD ((i.val + 6) % 8) ^^
      b.getLsbD ((i.val + 7) % 8) ^^ (0x63#8).getLsbD i.val := by
  decide +kernel

theorem mul_assoc (a b c : Byte) : mul (mul a b) c = mul a (mul b c) := by
  apply decode_bijective.injective
  simp only [decode_mul]
  exact _root_.mul_assoc _ _ _

theorem mul_comm (a b : Byte) : mul a b = mul b a := by
  apply decode_bijective.injective
  simp only [decode_mul]
  exact _root_.mul_comm _ _

theorem mul_xor (a b c : Byte) : mul a (b ^^^ c) = mul a b ^^^ mul a c := by
  apply decode_bijective.injective
  simp only [decode_mul, decode_xor, mul_add]

theorem xor_mul (a b c : Byte) : mul (a ^^^ b) c = mul a c ^^^ mul b c := by
  apply decode_bijective.injective
  simp only [decode_mul, decode_xor, add_mul]

end SDitH.Proofs.RijndaelByte
