import SDitH.Proofs.PIOPChallenges
import SDitH.Proofs.FieldIrreducibility
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! A counterexample to the introductory PIOP's printed soundness bound.
It concerns the stated generic protocol with an allowed public set S, not a
signature execution or the actual BLC challenge-image set. -/

namespace SDitH.Proofs.PIOPSoundnessDiscrepancy

open Polynomial Spec.PIOP Spec.PIOPChallenges Spec.UniformChallenges
open Spec.FieldRepresentation
open scoped BigOperators ENNReal Classical

noncomputable def constraints (F : Type*) [Field F] : Fin 1 → MvPolynomial (Fin 1) F :=
  fun _ => 1

noncomputable def lines (F : Type*) [Field F] : Fin 1 → F[X] := fun _ => X

noncomputable def response {F : Type*} [Field F] (gamma : Fin 1 → F) : F[X] :=
  C (gamma 0) * X ^ 2 + X

noncomputable def sample (F : Type*) [Field F] : Finset F := nthRootsFinset 3 1

theorem sample_nonempty (F : Type*) [Field F] : (sample F).Nonempty :=
  ⟨1, one_mem_nthRootsFinset (by decide)⟩

theorem no_valid_witness (F : Type*) [Field F] (w : Fin 1 → F) :
    ¬ ValidWitness (constraints F) w := by
  intro h
  have := h 0
  simp [constraints] at this

theorem binary_constant_terms (F : Type*) [Field F] :
    ∀ i, (lines F i).eval 0 = 0 ∨ (lines F i).eval 0 = 1 := by
  intro i
  exact Or.inl (by simp [lines])

theorem constraints_from_binary (category : Category) (j : Fin 1) :
    MvPolynomial.map (algebraMap (ZMod 2) (QuotientRing category)) (constraints (ZMod 2) j) =
      constraints (QuotientRing category) j := by
  simp [constraints]

theorem admissible_degrees (F : Type*) [Field F] :
    (∀ i, (lines F i).natDegree ≤ 1) ∧
    (∀ j, (constraints F j).totalDegree ≤ 2) ∧
    (X : F[X]).natDegree ≤ 2 - 1 ∧
    ∀ gamma : Fin 1 → F, (response gamma).natDegree ≤ 2 := by
  refine ⟨fun _ => natDegree_X_le, ?_, by simp, ?_⟩
  · intro j
    simp [constraints]
  · intro gamma
    exact natDegree_add_le_of_degree_le
      ((natDegree_C_mul_le _ _).trans (natDegree_X_pow_le 2))
      (natDegree_X_le.trans (by decide))

theorem accepts_cube_root {F : Type*} [Field F] (gamma : Fin 1 → F)
    (delta : F) (hdelta : delta ^ 3 = 1) :
    literalVerifier (constraints F) gamma (response gamma) delta
      ((X : F[X]).eval delta) (fun i => (lines F i).eval delta) := by
  constructor
  · simp [response]
  · simp only [response, eval_add, eval_mul, eval_C, eval_pow, eval_X,
      verifierRhs, constraints, map_one, mul_one, Fin.sum_univ_one]
    calc
      (gamma 0 * delta ^ 2 + delta) * delta = gamma 0 * delta ^ 3 + delta * delta := by ring
      _ = delta * delta + gamma 0 := by rw [hdelta]; ring

theorem acceptance_probability_one (F : Type*) [Field F] [Fintype F] :
    literalExperiment (constraints F) (lines F) X response (sample F) (sample_nonempty F) true = 1 := by
  have h : ∀ gamma : Fin 1 → F,
      eventOutcome (PMF.uniformOfFinset (sample F) (sample_nonempty F))
        (fun delta => literalVerifier (constraints F) gamma (response gamma) delta
          ((X : F[X]).eval delta) (fun i => (lines F i).eval delta)) true = 1 := by
    intro gamma
    rw [ChallengeMixtures.eventOutcome_true]
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro delta hdelta
    apply accepts_cube_root
    exact (mem_nthRootsFinset (by decide : 0 < 3) 1).mp
      ((PMF.mem_support_uniformOfFinset_iff _ _).mp hdelta)
  unfold literalExperiment
  simp only [PMF.bind_apply, h, mul_one, PMF.tsum_coe]

/-- Every submitted field contains exactly three cube roots of one. This is
derived from the proved field cardinality and cyclicity of its unit group. -/
theorem submitted_sample_card (category : Category) :
    (sample (QuotientRing category)).card = 3 := by
  have hd : 3 ∣ Fintype.card (QuotientRing category)ˣ := by
    rw [Fintype.card_units, FieldIrreducibility.quotient_card]
    cases category <;> decide
  have hc := IsCyclic.card_orderOf_eq_totient (α := (QuotientRing category)ˣ) hd
  have hp : 0 < ({g : (QuotientRing category)ˣ | orderOf g = 3} : Finset _).card := by
    rw [hc]
    decide
  obtain ⟨g, hg⟩ := Finset.card_pos.mp hp
  have ho : orderOf g = 3 := (Finset.mem_filter.mp hg).2
  have hr : IsPrimitiveRoot (g : QuotientRing category) 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr ho)
  exact hr.card_nthRootsFinset

theorem printed_bound_lt_one (category : Category) :
    (Fintype.card (QuotientRing category) : ℝ≥0∞)⁻¹ +
      (1 - (Fintype.card (QuotientRing category) : ℝ≥0∞)⁻¹) *
        (2 / (sample (QuotientRing category)).card) < 1 := by
  rw [submitted_sample_card]
  have ha : (Fintype.card (QuotientRing category) : ℝ≥0∞)⁻¹ < 1 := by
    apply ENNReal.inv_lt_one.mpr
    exact_mod_cast (Fintype.one_lt_card (α := QuotientRing category))
  have hat : (Fintype.card (QuotientRing category) : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ne_of_lt (ha.trans ENNReal.one_lt_top)
  have hs : 1 - (Fintype.card (QuotientRing category) : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top)
  have h23 : (2 : ℝ≥0∞) / 3 < 1 := by
    apply (ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by simp))).mpr
    norm_num
  exact (ENNReal.add_lt_add_left hat
    (ENNReal.mul_lt_mul_right (ne_of_gt (tsub_pos_iff_lt.mpr ha)) hs h23)).trans_eq
      (by simpa only [mul_one] using add_tsub_cancel_of_le ha.le)

/-- The printed d/|S| expression is strictly smaller than the actual acceptance
probability on a constraint system with no witness, for d=2 and |S|=3. -/
theorem submitted_printed_bound_fails (category : Category) :
    ¬ literalExperiment (constraints (QuotientRing category)) (lines (QuotientRing category))
        X response (sample (QuotientRing category)) (sample_nonempty (QuotientRing category)) true ≤
      (Fintype.card (QuotientRing category) : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card (QuotientRing category) : ℝ≥0∞)⁻¹) *
          (2 / (sample (QuotientRing category)).card) := by
  rw [acceptance_probability_one]
  exact not_le_of_gt (printed_bound_lt_one category)

end SDitH.Proofs.PIOPSoundnessDiscrepancy
