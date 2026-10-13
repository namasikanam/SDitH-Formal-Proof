import SDitH.Spec.FieldRepresentation
import Mathlib.Tactic

namespace SDitH.Proofs.FieldRepresentation

open Spec.FieldRepresentation Polynomial
open scoped BigOperators

theorem modulus_monic (category : Category) : (modulus category).Monic := by
  cases category <;> dsimp [modulus] <;> monicity <;> norm_num

theorem modulus_degree (category : Category) : (modulus category).natDegree = width category := by
  cases category <;> dsimp [modulus, width] <;> compute_degree <;> norm_num

theorem width_ge_128 (category : Category) : 128 ≤ width category := by
  cases category <;> decide

/-- The stated powers form a basis of the actual submitted quotient ring.
This follows from monicity, without assuming irreducibility or a field instance. -/
theorem submitted_power_basis (category : Category) :
    ∃ basis : PowerBasis (ZMod 2) (QuotientRing category),
      basis.gen = generator category ∧ basis.dim = width category := by
  refine ⟨AdjoinRoot.powerBasis' (modulus_monic category), rfl, ?_⟩
  exact modulus_degree category

theorem generator_powers_independent (category : Category) :
    LinearIndependent (ZMod 2) (fun i : Fin (width category) => generator category ^ i.val) := by
  obtain ⟨basis, hg, hd⟩ := submitted_power_basis category
  have h : LinearIndependent (ZMod 2) (fun i : Fin basis.dim => basis.gen ^ i.val) := by
    simpa only [PowerBasis.coe_basis] using basis.basis.linearIndependent
  simpa [hg] using h.comp (Fin.cast hd.symm) (Fin.cast_injective hd.symm)

/-- Independent indexed powers determine every binary coefficient, even when
only a subset of the full basis is used. -/
theorem indexed_power_sum_injective (category : Category) {I : Type*} [Fintype I]
    (index : I → Fin (width category)) (hinj : Function.Injective index) :
    Function.Injective (fun coefficients : I → ZMod 2 =>
      ∑ i, algebraMap (ZMod 2) (QuotientRing category) (coefficients i) *
        generator category ^ (index i).val) := by
  intro a b hab
  have hli := (generator_powers_independent category).comp index hinj
  have hz : (∑ i, (a i - b i) • generator category ^ (index i).val) = 0 := by
    simp only [Algebra.smul_def, map_sub, sub_mul, Finset.sum_sub_distrib, hab, sub_self]
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => a i - b i) hz
  funext i
  exact sub_eq_zero.mp (hc i)

theorem encodeCoefficients_injective (category : Category) {n : Nat}
    (hn : n ≤ width category) : Function.Injective (encodeCoefficients category (n := n)) := by
  exact indexed_power_sum_injective category (Fin.castLE hn) (Fin.castLE_injective hn)

/-- No nonzero polynomial below the submitted modulus degree can vanish at
the quotient generator. This is the precise algebraic property used by packing. -/
theorem aeval_zero_iff (category : Category) (p : (ZMod 2)[X])
    (hp : p.natDegree < width category) :
    aeval (generator category) p = 0 ↔ p = 0 := by
  change aeval (AdjoinRoot.root (modulus category)) p = 0 ↔ p = 0
  rw [AdjoinRoot.aeval_eq]
  constructor
  · intro h
    by_contra hn
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (modulus_monic category) hn
      (by simpa only [modulus_degree] using hp) h
  · rintro rfl
    exact map_zero _

end SDitH.Proofs.FieldRepresentation
