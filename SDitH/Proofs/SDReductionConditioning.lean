import SDitH.Proofs.SDReductionGame
import SDitH.Proofs.SDReductionDiscrepancy
import SDitH.Assumptions
import SDitH.Spec.ParameterSelection

/-! The conditional-uniqueness heuristic in §5.1 is not a universal bound for
arbitrary correct solvers. An explicit solver returns only on the zero instance,
where multiple regular solutions exist. Its successful event has positive mass
under the candidate planted-uniform SD model. This refutes that intermediate
conditional estimate, not the final existential security theorem. In this example
no rows are removed, so the displayed reduction itself succeeds whenever the
solver returns. -/

namespace SDitH.Proofs.SDReductionConditioning

open Spec Spec.SDReduction Spec.SDReductionGame
open SDReductionGame SDReductionDiscrepancy
open scoped Classical ENNReal
noncomputable section

abbrev Instance := SDInstance (ZMod 2) (2 * 2) 1

def alternateWitness : Fin (2 * 2) → ZMod 2 :=
  fun j => elementary (1 : Fin 2) (finProdFinEquiv.symm j).2

theorem alternate_regular : regularFlat (w := 2) (m := 2) alternateWitness := by
  intro i
  refine ⟨1, 1, one_ne_zero, ?_⟩
  funext j
  simp [alternateWitness]

theorem witnesses_distinct : regularWitness ≠ alternateWitness := by
  intro he
  have h := congrFun he (finProdFinEquiv (0, 0))
  norm_num [regularWitness, alternateWitness, elementary] at h

/-- A fully specified correct (but highly selective) RSD solver. No running
time or relation to a practical attack is asserted. -/
def selectiveSolver (inst : Instance) : PMF (Option (Fin (2 * 2) → ZMod 2)) :=
  if inst.H = 0 ∧ inst.y = 0 then PMF.pure (some regularWitness) else PMF.pure none

theorem selective_return_only_zero (inst : Instance) (z : Fin (2 * 2) → ZMod 2)
    (hz : some z ∈ (selectiveSolver inst).support) : inst.H = 0 ∧ inst.y = 0 := by
  unfold selectiveSolver at hz
  split at hz
  · assumption
  · simp at hz

theorem selective_solver_correct : ∀ (inst : Instance) (z : Fin (2 * 2) → ZMod 2),
    some z ∈ (selectiveSolver inst).support → RSDSolution (w := 2) (m := 2) inst z := by
  intro inst z hz
  have hzero := selective_return_only_zero inst z hz
  simp only [selectiveSolver, if_pos hzero, PMF.mem_support_pure_iff, Option.some.injEq] at hz
  subst z
  refine ⟨?_, witness_regular⟩
  rw [hzero.1, hzero.2, Matrix.zero_mulVec]

def exactWeightErrors : Finset (Fin (2 * 2) → ZMod 2) :=
  Finset.univ.filter (fun x => hammingWeight x = 2)

theorem exactWeightErrors_nonempty : exactWeightErrors.Nonempty :=
  ⟨regularWitness, by simp [exactWeightErrors, witness_solution.2]⟩

theorem exactWeightErrors_exact : Assumptions.ExactWeightSampleSpace 2 exactWeightErrors := by
  intro x
  simp [exactWeightErrors]

/-- The already-separated candidate planted SD model: uniform full matrix and
independent uniform exact-weight vector. This is not seed-based key generation. -/
def inputs : PMF Instance :=
  Assumptions.plantedSD exactWeightErrors exactWeightErrors_nonempty

def game : PMF (Outcome (ZMod 2) (2 * 2) 1) :=
  experiment (le_refl 1) inputs selectiveSolver

def zeroOutcome : Outcome (ZMod 2) (2 * 2) 1 :=
  ⟨zeroInstance, Equiv.refl _, some regularWitness⟩

theorem zero_input_supported : zeroInstance ∈ inputs.support := by
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨0, PMF.mem_support_uniformOfFintype _, ?_⟩
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨regularWitness, ?_, ?_⟩
  · exact (PMF.mem_support_uniformOfFinset_iff _ _).mpr
      (by simp [exactWeightErrors, witness_solution.2])
  · simp [zeroInstance]

theorem zero_outcome_supported : zeroOutcome ∈ game.support := by
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨zeroInstance, zero_input_supported, ?_⟩
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨Equiv.refl _, PMF.mem_support_uniformOfFintype _, ?_⟩
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨some regularWitness, ?_, rfl⟩
  change some regularWitness ∈ (selectiveSolver zeroInstance).support
  simp [selectiveSolver, zeroInstance]

theorem zero_outcome_regular_return :
    FullRegular (w := 2) (m := 2) zeroOutcome ∧ Returned zeroOutcome := by
  refine ⟨?_, rfl⟩
  exact every_permutation_has_regular_solution (Equiv.refl _)

theorem regular_return_positive :
    0 < eventMass game (fun o => FullRegular (w := 2) (m := 2) o ∧ Returned o) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hd := (PMF.toOuterMeasure_apply_eq_zero_iff game _).mp hz
  exact Set.disjoint_left.mp hd zero_outcome_supported zero_outcome_regular_return

theorem returned_not_unique (o : Outcome (ZMod 2) (2 * 2) 1)
    (ho : o ∈ game.support) (hs : Returned o) :
    ¬ UniqueTruncated (w := 2) (m := 2) (le_refl 1) o := by
  obtain ⟨candidate, hc⟩ := Option.isSome_iff_exists.mp hs
  have hsup := (experiment_support (le_refl 1) inputs selectiveSolver o ho).2
  rw [hc] at hsup
  have hz := selective_return_only_zero _ candidate hsup
  intro hu
  apply witnesses_distinct
  apply hu regularWitness alternateWitness
  · exact ⟨by rw [hz.1, hz.2, Matrix.zero_mulVec], witness_regular⟩
  · exact ⟨by rw [hz.1, hz.2, Matrix.zero_mulVec], alternate_regular⟩

theorem conditional_unique_zero :
    conditionalMass game (UniqueTruncated (w := 2) (m := 2) (le_refl 1))
      (fun o => FullRegular (w := 2) (m := 2) o ∧ Returned o) = 0 := by
  have hmass : eventMass game
      (fun o => (FullRegular (w := 2) (m := 2) o ∧ Returned o) ∧
        UniqueTruncated (w := 2) (m := 2) (le_refl 1) o) = 0 := by
    apply (PMF.toOuterMeasure_apply_eq_zero_iff game _).mpr
    apply Set.disjoint_left.mpr
    intro o ho hg
    exact returned_not_unique o ho hg.1.2 hg.2
  simp [conditionalMass, hmass]

/-- The heuristic on printed p. 43 conditions only on the solver's return.
That conditioning event also has positive mass, and uniqueness is still zero. -/
theorem source_conditioning_zero :
    0 < eventMass game Returned ∧
    conditionalMass game (UniqueTruncated (w := 2) (m := 2) (le_refl 1)) Returned = 0 := by
  constructor
  · apply lt_of_lt_of_le regular_return_positive
    exact game.toOuterMeasure.mono (fun _ h => h.2)
  · have hmass : eventMass game
        (fun o => Returned o ∧ UniqueTruncated (w := 2) (m := 2) (le_refl 1) o) = 0 := by
      apply (PMF.toOuterMeasure_apply_eq_zero_iff game _).mpr
      apply Set.disjoint_left.mpr
      intro o ho hg
      exact returned_not_unique o ho hg.1 hg.2
    simp [conditionalMass, hmass]

/-- These positive parameters satisfy the actual Theorem-5.1 dimension
inequality at theta=2, and the regular candidate/syndrome density is 1/2. -/
theorem example_parameter_conditions :
    (0 < 1 ∧ 1 ≤ 1 ∧ 1 ≤ 4 ∧ 0 < 2 ∧ 2 < 4 ∧ 2 ∣ 4) ∧
    (1 : ℝ) ≤ 4 - 2 * Real.logb 2 ((4 : ℝ) / 2) - Real.logb 2 2 ∧
    Spec.ParameterSelection.rsdDensity 2 2 (4 - 1) = 1 / (2 : ℝ) := by
  norm_num [Spec.ParameterSelection.rsdDensity, Spec.ParameterSelection.binaryDensity]

/-- The source's positive exponential estimate cannot be a universal lower
bound on uniqueness conditioned on a correct solver's successful return. -/
theorem conditional_uniqueness_bound_fails :
    ¬ ENNReal.ofReal (Real.exp (-(1 / (2 : ℝ)))) ≤
      conditionalMass game (UniqueTruncated (w := 2) (m := 2) (le_refl 1))
        (fun o => FullRegular (w := 2) (m := 2) o ∧ Returned o) := by
  rw [conditional_unique_zero, not_le]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

end
end SDitH.Proofs.SDReductionConditioning
