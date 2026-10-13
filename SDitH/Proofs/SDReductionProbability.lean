import SDitH.Proofs.SDReduction

/-! Exact facts about the displayed §5.1 reduction. The fixed-witness
regularization event has the combinatorial probability. Existence of some
regular solution is a larger event. Neither fact supplies the source's
heuristic conditional-uniqueness estimate or a solver-distribution reduction. -/

namespace SDitH.Proofs.SDReductionProbability

open Spec.SDReduction Spec.RegularSupport Spec.UniformChallenges
open SDReduction
open scoped Classical ENNReal

theorem regular_permutation_probability {F : Type*} [Field F] {w m : Nat}
    (x : Fin (w * m) → F) (hweight : Spec.hammingWeight x = w) (hm : 0 < m) :
    probability (fun sigma : Equiv.Perm (Fin (w * m)) =>
      regularFlat (permuteVector sigma x)) =
      (m ^ w : ℝ≥0∞) / Nat.choose (w * m) w := by
  let e : Coordinate w m ≃ Fin (w * m) := finProdFinEquiv
  have hc : (vectorSupport (fun ij => x (e ij))).card = w := by
    have hi := congrArg Finset.card (support_comp_equiv e x)
    rw [Finset.card_image_of_injective _ e.injective, support_weight, hweight] at hi
    exact hi
  have hp := PermutationProbability.permuted_regular_probability
    (vectorSupport (fun ij => x (e ij))) hc hm
  have ht := IntegerSamplingProbability.probability_equiv e.permCongr
    (fun sigma => regularFlat (permuteVector sigma x))
  rw [← ht]
  have hevent (sigma : Equiv.Perm (Coordinate w m)) :
      regularFlat (permuteVector (e.permCongr sigma) x) ↔
        Regular (permute sigma (vectorSupport (fun ij => x (e ij)))) := by
    rw [← support_permute, ← regular_iff_support]
    simp [regularFlat, Spec.SDReduction.permuteVector, Equiv.permCongr_def, e]
  simp_rw [hevent]
  exact hp

/-- For a fixed solvable SD instance, regular-solution existence has at least
the fixed-witness probability. Equality is not silently imposed. -/
theorem regular_instance_probability_lower_bound {F : Type*} [Field F] {w m k : Nat}
    (inst : Spec.SDInstance F (w * m) k) (x : Fin (w * m) → F)
    (hsol : Spec.SDSolution inst w x) (hm : 0 < m) :
    (m ^ w : ℝ≥0∞) / Nat.choose (w * m) w ≤
      probability (fun sigma : Equiv.Perm (Fin (w * m)) =>
        ∃ z, RSDSolution (permuteInstance sigma inst) z) := by
  rw [← regular_permutation_probability x hsol.2 hm]
  apply MeasureTheory.measure_mono
  intro sigma hreg
  exact ⟨permuteVector sigma x, (permuted_mulVec inst sigma x).trans hsol.1, hreg⟩

/-- Correctness of every nonfailure result of the full randomized reduction,
provided each possible solver result is an actual RSD solution. This is a
semantic solver premise, not a claim about its conditional success rate. -/
theorem run_returns_solution {F : Type*} [Field F] {w m ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inst : Spec.SDInstance F (w * m) ksd)
    (solver : Spec.SDInstance F (w * m) krsd → PMF (Option (Fin (w * m) → F)))
    (hsolver : ∀ input z, some z ∈ (solver input).support → RSDSolution input z)
    (x : Fin (w * m) → F) (hx : some x ∈ (run hkk inst solver).support) :
    Spec.SDSolution inst w x := by
  obtain ⟨sigma, _, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
  obtain ⟨candidate, hc, hret⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  obtain ⟨xhat, hcandidate, _, _⟩ := (finish_some_iff inst sigma candidate x).mp hret
  subst candidate
  exact finish_correct inst sigma xhat x (hsolver _ xhat hc).2 hret

end SDitH.Proofs.SDReductionProbability
