import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-! An algebraic irreducibility criterion for checking binary-polynomial
certificates. This module does not assume that any submitted modulus is a field.
The auxiliary quotient field below is used only after an arbitrary factor has
been proved irreducible. -/

namespace SDitH.Proofs.BinaryIrreducibility

open Polynomial

theorem irreducible_dvd_frobenius_iff {q : (ZMod 2)[X]} (hq : Irreducible q) (n : Nat) :
    q ∣ X ^ (2 ^ n) - X ↔ q.natDegree ∣ n := by
  letI : Fact (Irreducible q) := ⟨hq⟩
  let basis := (AdjoinRoot.powerBasis hq.ne_zero).basis
  letI : Fintype (AdjoinRoot q) := Fintype.ofEquiv _ basis.equivFun.toEquiv.symm
  have hdim : Module.finrank (ZMod 2) (AdjoinRoot q) = q.natDegree :=
    (AdjoinRoot.powerBasis hq.ne_zero).finrank
  rw [← hdim, ← FiniteField.orderOf_frobeniusAlgHom (ZMod 2) (AdjoinRoot q),
    orderOf_dvd_iff_pow_eq_one]
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
  constructor
  · intro h
    apply AdjoinRoot.algHom_ext
    simpa only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate,
      ZMod.card, AlgHom.one_apply] using h
  · intro h
    simpa only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate,
      ZMod.card, AlgHom.one_apply] using DFunLike.congr_fun h (AdjoinRoot.root q)

/-- A finite collection of Frobenius coprimality checks suffices when it covers
every possible proper factor degree dividing the degree of the modulus. -/
theorem irreducible_of_frobenius_checks (f : (ZMod 2)[X]) (hf : f ≠ 0)
    (hpos : 0 < f.natDegree) (checks : List Nat)
    (hfull : f ∣ X ^ (2 ^ f.natDegree) - X)
    (hcover : ∀ d, 0 < d → d ≤ f.natDegree / 2 → d ∣ f.natDegree →
      ∃ m ∈ checks, d ∣ m)
    (hchecks : ∀ m ∈ checks, IsCoprime f (X ^ (2 ^ m) - X)) : Irreducible f := by
  apply (irreducible_iff_lt_natDegree_lt hf (not_isUnit_of_natDegree_pos f hpos)).mpr
  intro p hp hdeg hpf
  obtain ⟨hpl, hpu⟩ := Finset.mem_Ioc.mp hdeg
  obtain ⟨q, hq, hqp⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos p hpl) hp.ne_zero
  have hqf : q ∣ f := hqp.trans hpf
  have hd : q.natDegree ∣ f.natDegree :=
    (irreducible_dvd_frobenius_iff hq _).mp (hqf.trans hfull)
  obtain ⟨m, hm, hdm⟩ := hcover q.natDegree hq.natDegree_pos
    ((natDegree_le_of_dvd hqp hp.ne_zero).trans hpu) hd
  exact hq.not_isUnit ((hchecks m hm).isUnit_of_dvd' hqf
    ((irreducible_dvd_frobenius_iff hq m).mpr hdm))

end SDitH.Proofs.BinaryIrreducibility
