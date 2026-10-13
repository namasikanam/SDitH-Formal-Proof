import SDitH.Spec.SDReductionGame
import SDitH.Proofs.SDReductionProbability
import Mathlib.Tactic

namespace SDitH.Proofs.SDReductionGame

open Spec Spec.SDReduction Spec.SDReductionGame
open scoped Classical ENNReal

theorem experiment_output {F : Type*} [Field F] {n ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inputs : PMF (SDInstance F n ksd))
    (solver : SDInstance F n krsd → PMF (Option (Fin n → F))) :
    (experiment hkk inputs solver).map output = inputs.bind (fun inst => run hkk inst solver) := by
  simp only [experiment, PMF.map_bind, PMF.map_comp, Function.comp_def, output, run]

theorem experiment_support {F : Type*} [Field F] {n ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inputs : PMF (SDInstance F n ksd))
    (solver : SDInstance F n krsd → PMF (Option (Fin n → F)))
    (o : Outcome F n ksd) (ho : o ∈ (experiment hkk inputs solver).support) :
    o.input ∈ inputs.support ∧
      o.candidate ∈ (solver (truncate hkk (permuteInstance o.permutation o.input))).support := by
  obtain ⟨inst, hi, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp ho
  obtain ⟨sigma, _, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
  obtain ⟨candidate, hc, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  subst o
  exact ⟨hi, hc⟩

theorem experiment_first_stage {F : Type*} [Field F] {n ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inputs : PMF (SDInstance F n ksd))
    (solver : SDInstance F n krsd → PMF (Option (Fin n → F))) :
    (experiment hkk inputs solver).map (fun o => (o.input, o.permutation)) =
      inputs.bind (fun inst =>
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map (fun sigma => (inst, sigma))) := by
  simp only [experiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext inst
  simp only [PMF.map, Function.comp_def]
  congr 1
  funext sigma
  exact PMF.bind_const _ _

theorem regular_event_mass {F : Type*} [Field F] {w m ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inputs : PMF (SDInstance F (w * m) ksd))
    (solver : SDInstance F (w * m) krsd → PMF (Option (Fin (w * m) → F))) :
    eventMass (experiment hkk inputs solver) (FullRegular (w := w) (m := m)) =
      ∑' inst, inputs inst * Spec.UniformChallenges.probability
        (fun sigma => ∃ z, RSDSolution (w := w) (m := m) (permuteInstance sigma inst) z) := by
  have hmap := PMF.toOuterMeasure_map_apply (fun o : Outcome F (w * m) ksd =>
    (o.input, o.permutation)) (experiment hkk inputs solver)
    {v | ∃ z, RSDSolution (w := w) (m := m) (permuteInstance v.2 v.1) z}
  rw [experiment_first_stage, PMF.toOuterMeasure_bind_apply] at hmap
  change _ = eventMass (experiment hkk inputs solver) (FullRegular (w := w) (m := m)) at hmap
  rw [← hmap]
  apply tsum_congr
  intro inst
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- The exact combinatorial factor lower-bounds the first event for any law
supported on solvable SD instances. This replaces the source's false equality
with its proved direction, without assuming an induced RSD distribution. -/
theorem regular_event_lower {F : Type*} [Field F] {w m ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inputs : PMF (SDInstance F (w * m) ksd))
    (solver : SDInstance F (w * m) krsd → PMF (Option (Fin (w * m) → F)))
    (hinputs : ∀ inst ∈ inputs.support, ∃ x, SDSolution inst w x) (hm : 0 < m) :
    (m ^ w : ℝ≥0∞) / Nat.choose (w * m) w ≤
      eventMass (experiment hkk inputs solver) (FullRegular (w := w) (m := m)) := by
  rw [regular_event_mass]
  calc
    (m ^ w : ℝ≥0∞) / Nat.choose (w * m) w =
        ∑' inst, inputs inst * ((m ^ w : ℝ≥0∞) / Nat.choose (w * m) w) := by
      rw [ENNReal.tsum_mul_right, inputs.tsum_coe, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro inst
      by_cases hi : inst ∈ inputs.support
      · obtain ⟨x, hx⟩ := hinputs inst hi
        exact mul_le_mul_right
          (SDReductionProbability.regular_instance_probability_lower_bound inst x hx hm) _
      · have hz := (PMF.apply_eq_zero_iff inputs inst).mpr hi
        simp [hz]

theorem eventMass_le_one {A : Type*} (p : PMF A) (event : A → Prop) :
    eventMass p event ≤ 1 := by
  apply le_trans (p.toOuterMeasure.mono (Set.subset_univ _))
  exact le_of_eq ((p.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _))

theorem eventMass_ne_top {A : Type*} (p : PMF A) (event : A → Prop) :
    eventMass p event ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (eventMass_le_one p event)

/-- This is the valid conditional-product step with the *same conditioning
events* in all three factors. It does not replace a conditional solver law
with the advertised success on another instance distribution. -/
theorem conditional_product {A : Type*} (p : PMF A) (g s u : A → Prop)
    (hg : eventMass p g ≠ 0) (hgs : eventMass p (fun a => g a ∧ s a) ≠ 0) :
    eventMass p g * conditionalMass p s g *
        conditionalMass p u (fun a => g a ∧ s a) =
      eventMass p (fun a => (g a ∧ s a) ∧ u a) := by
  unfold conditionalMass
  rw [ENNReal.mul_div_cancel hg (eventMass_ne_top p g),
    ENNReal.mul_div_cancel hgs (eventMass_ne_top p _)]

/-- The deterministic uniqueness argument now applies inside the actual
randomized reduction, including the supported solver output. -/
theorem good_return_succeeds {F : Type*} [Field F] {w m ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inputs : PMF (SDInstance F (w * m) ksd))
    (solver : SDInstance F (w * m) krsd → PMF (Option (Fin (w * m) → F)))
    (hsolver : ∀ input z, some z ∈ (solver input).support → RSDSolution input z)
    (o : Outcome F (w * m) ksd) (ho : o ∈ (experiment hkk inputs solver).support)
    (hg : FullRegular (w := w) (m := m) o) (hs : Returned o)
    (hu : UniqueTruncated (w := w) (m := m) hkk o) : Succeeded o := by
  obtain ⟨wit, hwit⟩ := hg
  obtain ⟨candidate, hc⟩ := Option.isSome_iff_exists.mp hs
  have hsup := (experiment_support hkk inputs solver o ho).2
  rw [hc] at hsup
  have hret := SDReduction.unique_truncated_passes hkk o.input o.permutation wit candidate
    hwit (hsolver _ candidate hsup) hu
  simp [Succeeded, output, hc, hret]

theorem good_return_mass_le_success {F : Type*} [Field F] {w m ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inputs : PMF (SDInstance F (w * m) ksd))
    (solver : SDInstance F (w * m) krsd → PMF (Option (Fin (w * m) → F)))
    (hsolver : ∀ input z, some z ∈ (solver input).support → RSDSolution input z) :
    eventMass (experiment hkk inputs solver)
        (fun o => (FullRegular (w := w) (m := m) o ∧ Returned o) ∧
          UniqueTruncated (w := w) (m := m) hkk o) ≤
      eventMass (experiment hkk inputs solver) Succeeded := by
  apply PMF.toOuterMeasure_mono
  intro o ⟨⟨⟨hg, hs⟩, hu⟩, ho⟩
  exact good_return_succeeds hkk inputs solver hsolver o ho hg hs hu

/-- A proved probability lower bound for the displayed reduction. All three
factors are defined by its actual joint experiment; no heuristic uniqueness
estimate or solver-distribution correspondence is assumed. -/
theorem reduction_conditional_bound {F : Type*} [Field F] {w m ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inputs : PMF (SDInstance F (w * m) ksd))
    (solver : SDInstance F (w * m) krsd → PMF (Option (Fin (w * m) → F)))
    (hsolver : ∀ input z, some z ∈ (solver input).support → RSDSolution input z)
    (hg : eventMass (experiment hkk inputs solver) (FullRegular (w := w) (m := m)) ≠ 0)
    (hgs : eventMass (experiment hkk inputs solver)
      (fun o => FullRegular (w := w) (m := m) o ∧ Returned o) ≠ 0) :
    eventMass (experiment hkk inputs solver) (FullRegular (w := w) (m := m)) *
      conditionalMass (experiment hkk inputs solver) Returned (FullRegular (w := w) (m := m)) *
      conditionalMass (experiment hkk inputs solver) (UniqueTruncated (w := w) (m := m) hkk)
        (fun o => FullRegular (w := w) (m := m) o ∧ Returned o) ≤
      (inputs.bind (fun inst => run hkk inst solver)).toOuterMeasure {x | x.isSome} := by
  rw [conditional_product _ _ _ _ hg hgs, ← experiment_output hkk inputs solver,
    PMF.toOuterMeasure_map_apply]
  exact good_return_mass_le_success hkk inputs solver hsolver

/-- The source's combinatorial factor is now connected to the complete
randomized reduction. The remaining conditional factors are actual probabilities,
not the advertised epsilon_rsd or the unsupported exponential estimate. -/
theorem reduction_combinatorial_bound {F : Type*} [Field F] {w m ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inputs : PMF (SDInstance F (w * m) ksd))
    (solver : SDInstance F (w * m) krsd → PMF (Option (Fin (w * m) → F)))
    (hinputs : ∀ inst ∈ inputs.support, ∃ x, SDSolution inst w x) (hm : 0 < m)
    (hsolver : ∀ input z, some z ∈ (solver input).support → RSDSolution input z)
    (hgs : eventMass (experiment hkk inputs solver)
      (fun o => FullRegular (w := w) (m := m) o ∧ Returned o) ≠ 0) :
    ((m ^ w : ℝ≥0∞) / Nat.choose (w * m) w) *
      conditionalMass (experiment hkk inputs solver) Returned (FullRegular (w := w) (m := m)) *
      conditionalMass (experiment hkk inputs solver) (UniqueTruncated (w := w) (m := m) hkk)
        (fun o => FullRegular (w := w) (m := m) o ∧ Returned o) ≤
      (inputs.bind (fun inst => run hkk inst solver)).toOuterMeasure {x | x.isSome} := by
  have hg : eventMass (experiment hkk inputs solver) (FullRegular (w := w) (m := m)) ≠ 0 := by
    intro hz
    apply hgs
    apply le_antisymm
    · rw [← hz]
      exact (experiment hkk inputs solver).toOuterMeasure.mono (fun _ h => h.1)
    · exact zero_le _
  apply le_trans _ (reduction_conditional_bound hkk inputs solver hsolver hg hgs)
  gcongr
  exact regular_event_lower hkk inputs solver hinputs hm

end SDitH.Proofs.SDReductionGame
