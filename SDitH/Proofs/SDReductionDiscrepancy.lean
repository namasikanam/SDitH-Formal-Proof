import SDitH.Proofs.SDReductionProbability

/-! The source identifies the fixed-witness regularization probability with
the probability that an instance has some regular solution. This explicit
solvable binary instance separates those events. It does not refute the final
Theorem-5.1 bound by itself, nor concern a seed-generated systematic public key.
-/

namespace SDitH.Proofs.SDReductionDiscrepancy

open Spec.SDReduction Spec.UniformChallenges
open SDReduction
open scoped Classical ENNReal

def zeroInstance : Spec.SDInstance (ZMod 2) (2 * 2) 1 := ⟨0, 0⟩

noncomputable def regularWitness : Fin (2 * 2) → ZMod 2 :=
  fun j => Spec.elementary (0 : Fin 2) (finProdFinEquiv.symm j).2

theorem witness_regular : regularFlat (w := 2) (m := 2) regularWitness := by
  intro i
  refine ⟨0, 1, one_ne_zero, ?_⟩
  funext j
  simp [regularWitness]

theorem witness_solution : Spec.SDSolution zeroInstance 2 regularWitness := by
  constructor
  · simp [zeroInstance]
  · exact regularFlat_weight regularWitness witness_regular

theorem every_permutation_has_regular_solution (sigma : Equiv.Perm (Fin (2 * 2))) :
    ∃ x, RSDSolution (permuteInstance sigma zeroInstance) x := by
  refine ⟨regularWitness, ?_, witness_regular⟩
  change (0 : Matrix (Fin (2 * 2 - 1)) (Fin (2 * 2)) (ZMod 2)).mulVec regularWitness = 0
  exact Matrix.zero_mulVec regularWitness

theorem instance_probability_one :
    probability (fun sigma : Equiv.Perm (Fin (2 * 2)) =>
      ∃ x, RSDSolution (permuteInstance sigma zeroInstance) x) = 1 := by
  have hevent : (fun sigma : Equiv.Perm (Fin (2 * 2)) =>
      ∃ x, RSDSolution (permuteInstance sigma zeroInstance) x) = fun _ => True := by
    funext sigma
    exact propext (iff_true_intro (every_permutation_has_regular_solution sigma))
  rw [hevent]
  unfold probability
  exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (by intro sigma _; trivial)

/-- For this valid SD instance, the instance event has probability one,
strictly larger than the fixed-witness ratio 4/6. -/
theorem instance_event_strictly_larger :
    (2 ^ 2 : ℝ≥0∞) / Nat.choose (2 * 2) 2 <
      probability (fun sigma : Equiv.Perm (Fin (2 * 2)) =>
        ∃ x, RSDSolution (permuteInstance sigma zeroInstance) x) := by
  rw [instance_probability_one]
  norm_num [Nat.choose]
  exact (ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by simp))).mpr (by norm_num)

theorem fixed_witness_probability :
    probability (fun sigma : Equiv.Perm (Fin (2 * 2)) =>
      regularFlat (w := 2) (m := 2) (permuteVector sigma regularWitness)) =
      (2 ^ 2 : ℝ≥0∞) / Nat.choose (2 * 2) 2 :=
  SDReductionProbability.regular_permutation_probability regularWitness witness_solution.2
    (by decide)

end SDitH.Proofs.SDReductionDiscrepancy
