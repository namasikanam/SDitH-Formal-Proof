import SDitH.Proofs.UnitaryPolynomial
import SDitH.Proofs.FieldRepresentation
import SDitH.Proofs.PIOPArithmetic

namespace SDitH.Proofs.UnitaryPacking

open Spec.UnitaryPolynomial Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem aeval_check {A : Type*} [CommRing A] [Algebra R A]
    (xi : A) {r : Nat} (bits : Fin r → R) :
    aeval xi (check bits) = Spec.PIOPArithmetic.unitaryCheck xi
      (fun k => algebraMap R A (bits k)) := by
  simpa [check] using PIOPArithmetic.map_unitaryCheck (aeval xi).toRingHom
    (X : R[X]) (fun k => C (bits k))

theorem aeval_packed_checks {A : Type*} [CommRing A] [Algebra R A]
    (xi : A) {d : Nat} (width : Fin d → Nat) (bits : (j : Fin d) → Fin (width j) → R) :
    aeval xi (packed (fun j => check (bits j))) = packedEvaluation xi width bits := by
  simp [packed, packedEvaluation, aeval_check]

/-- The recursive loop in Algorithms 19/20 has precisely the displayed sum's
order and powers. No independent implementation is assumed correct. -/
theorem unitaryLayers_sum (xi : R) (widths : List Nat)
    (selectors : Spec.PIOPArithmetic.Selectors R widths) (layer : Nat) :
    Spec.PIOPArithmetic.unitaryLayers xi widths selectors layer =
      ∑ j : Fin widths.length, xi ^ (32 * (layer + j.val)) *
        Spec.PIOPArithmetic.unitaryCheck xi (selectorAt widths selectors j) := by
  induction widths generalizing layer with
  | nil => simp [Spec.PIOPArithmetic.unitaryLayers]
  | cons r rest ih =>
    simp only [Spec.PIOPArithmetic.unitaryLayers, List.length_cons, Fin.sum_univ_succ,
      selectorAt, Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show layer + 1 + j.val = layer + (j.val + 1) by omega]

omit [CommRing R] in
theorem selectorAt_map {A : Type*} (f : R → A)
    (widths : List Nat) (selectors : Spec.PIOPArithmetic.Selectors R widths)
    (j : Fin widths.length) :
    selectorAt widths (Spec.PIOPArithmetic.mapSelectors f widths selectors) j =
      fun k => f (selectorAt widths selectors j k) := by
  induction widths with
  | nil => exact Fin.elim0 j
  | cons r rest ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact ih selectors.2 k

theorem unitaryLayers_eq_packedEvaluation {A : Type*} [CommRing A] [Algebra R A]
    (xi : A) (widths : List Nat) (selectors : Spec.PIOPArithmetic.Selectors R widths) :
    Spec.PIOPArithmetic.unitaryLayers xi widths
      (Spec.PIOPArithmetic.mapSelectors (algebraMap R A) widths selectors) 0 =
      packedEvaluation xi (fun j : Fin widths.length => widths.get j)
        (selectorAt widths selectors) := by
  rw [unitaryLayers_sum]
  simp only [packedEvaluation, Nat.zero_add, selectorAt_map]

/-- Each polynomial's coefficients occupy its own 32-coordinate block. -/
theorem packed_coeff {d : Nat} (checks : Fin d → R[X])
    (hdeg : ∀ j, (checks j).natDegree < 32) (j : Fin d) (k : Nat) (hk : k < 32) :
    (packed checks).coeff (32 * j.val + k) = (checks j).coeff k := by
  classical
  rw [packed, finset_sum_coeff, Finset.sum_eq_single j]
  · simpa only [Nat.add_comm] using coeff_X_pow_mul (checks j) (32 * j.val) k
  · intro i _ hij
    rw [coeff_X_pow_mul']
    by_cases hi : 32 * i.val ≤ 32 * j.val + k
    · rw [if_pos hi]
      apply coeff_eq_zero_of_natDegree_lt
      have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
      have hd := hdeg i
      omega
    · rw [if_neg hi]
  · simp

theorem packed_zero_iff {d : Nat} (checks : Fin d → R[X])
    (hdeg : ∀ j, (checks j).natDegree < 32) :
    packed checks = 0 ↔ ∀ j, checks j = 0 := by
  constructor
  · intro h j
    ext k
    by_cases hk : k < 32
    · have he := packed_coeff checks hdeg j k hk
      rw [h, coeff_zero] at he
      exact he.symm
    · simpa only [coeff_zero] using coeff_eq_zero_of_natDegree_lt ((hdeg j).trans_le (by omega))
  · intro h
    simp [packed, h]

theorem packed_degree_lt {d bound : Nat} (checks : Fin d → R[X])
    (hdeg : ∀ j, (checks j).natDegree < 32) (hsize : 32 * d ≤ bound) (hb : 0 < bound) :
    (packed checks).natDegree < bound := by
  have h : (packed checks).natDegree ≤ bound - 1 := by
    unfold packed
    apply natDegree_sum_le_of_forall_le
    intro j _
    apply le_trans natDegree_mul_le
    have hx : (X ^ (32 * j.val) : R[X]).natDegree ≤ 32 * j.val := natDegree_X_pow_le _
    have hd := hdeg j
    have hj := j.isLt
    omega
  omega

/-- The packed-check equivalence in the literal Table-2 quotient construction.
The source's d<=4 bound fits all three moduli. No field irreducibility or
evaluation-injectivity assumption is passed to this theorem. -/
theorem submitted_packed_zero_iff (category : Spec.FieldRepresentation.Category)
    {d : Nat} (hd : d ≤ 4) (checks : Fin d → (ZMod 2)[X])
    (hdeg : ∀ j, (checks j).natDegree < 32) :
    aeval (Spec.FieldRepresentation.generator category) (packed checks) = 0 ↔
      ∀ j, checks j = 0 := by
  have hw := FieldRepresentation.width_ge_128 category
  rw [FieldRepresentation.aeval_zero_iff category (packed checks)
    (packed_degree_lt checks hdeg (by omega) (by omega)), packed_zero_iff checks hdeg]

/-- Apply that equivalence to the actual D polynomials and their binary
selector constraints, with no abstract correctness contract for the check. -/
theorem submitted_unitary_packing (category : Spec.FieldRepresentation.Category)
    {d : Nat} (width : Fin d → Nat) (bits : (j : Fin d) → Fin (width j) → ZMod 2)
    (hd : d ≤ 4) (hw : ∀ j, width j ≤ 3) :
    aeval (Spec.FieldRepresentation.generator category)
      (packed (fun j => check (bits j))) = 0 ↔ ∀ j, AtMostOne (bits j) := by
  rw [submitted_packed_zero_iff category hd _
    (fun j => UnitaryPolynomial.check_degree_lt_32 (bits j) (hw j))]
  exact forall_congr' (fun j => UnitaryPolynomial.binary_check_zero_iff_atMostOne (bits j))

/-- The actual packed unitary loop on binary selectors, instantiated in every
submitted quotient. Irreducibility is not needed for this direction of use. -/
theorem submitted_unitary_loop (category : Spec.FieldRepresentation.Category)
    (widths : List Nat) (selectors : Spec.PIOPArithmetic.Selectors (ZMod 2) widths)
    (hd : widths.length ≤ 4) (hw : ∀ j : Fin widths.length, widths.get j ≤ 3) :
    Spec.PIOPArithmetic.unitaryLayers (Spec.FieldRepresentation.generator category) widths
      (Spec.PIOPArithmetic.mapSelectors
        (algebraMap (ZMod 2) (Spec.FieldRepresentation.QuotientRing category)) widths selectors) 0 = 0 ↔
      ∀ j : Fin widths.length, AtMostOne (selectorAt widths selectors j) := by
  rw [unitaryLayers_eq_packedEvaluation, ← aeval_packed_checks]
  exact submitted_unitary_packing category _ _ hd hw

end SDitH.Proofs.UnitaryPacking
