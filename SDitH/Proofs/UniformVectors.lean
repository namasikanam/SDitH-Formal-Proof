import SDitH.Proofs.PermutationProbability

/-! Selecting distinct positions from a uniform finite vector preserves the
uniform joint law. In particular, discarded or unused sampled bytes do not
bias the coordinates that are used. This is a law of explicit uniform samples,
not a claim that a concrete cryptographic stream is uniformly distributed. -/

namespace SDitH.Proofs.UniformVectors

open Spec.UniformChallenges
open scoped Classical ENNReal

theorem uniform_pair {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] :
    (PMF.uniformOfFintype A).bind
      (fun a => (PMF.uniformOfFintype B).map (fun b => (a, b))) =
      PMF.uniformOfFintype (A × B) := by
  ext ⟨a, b⟩
  simp [PMF.bind_apply, PMF.map_apply, Fintype.card_prod, Nat.cast_mul, ite_and, mul_ite]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))).symm

theorem probability_restrict {I J A : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype A] [Nonempty A] (index : I → J) (hinj : Function.Injective index)
    (event : (I → A) → Prop) :
    probability (fun v : J → A => event (fun i => v (index i))) = probability event := by
  let e : (J → A) ≃ (I → A) × ({j // j ∉ Set.range index} → A) :=
    (Equiv.piEquivPiSubtypeProd (fun j => j ∈ Set.range index) (fun _ => A)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr (Equiv.ofInjective index hinj).symm (Equiv.refl A)) (Equiv.refl _))
  have hp := IntegerSamplingProbability.probability_equiv e (fun pair => event pair.1)
  exact hp.trans (PermutationProbability.probability_first event)

theorem map_uniform_restrict {I J A : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype A] [Nonempty A] (index : I → J) (hinj : Function.Injective index) :
    (PMF.uniformOfFintype (J → A)).map (fun v i => v (index i)) =
      PMF.uniformOfFintype (I → A) := by
  ext v
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  exact probability_restrict index hinj (fun x => x = v)

end SDitH.Proofs.UniformVectors
