import SDitH.Proofs.RegularSupport
import SDitH.Proofs.IntegerSamplingProbability

/-! Uniform permutations send a fixed support uniformly over all supports of
the same cardinality. The proofs construct the equal-fiber equivalences;
uniformity of the resulting support is not an extra hypothesis. -/

namespace SDitH.Proofs.PermutationProbability

open Spec.RegularSupport Spec.UniformChallenges
open RegularSupport IntegerSamplingProbability
open scoped Classical ENNReal

private def firstEventEquiv {A B : Type*} (event : A → Prop) :
    {x : A × B // event x.1} ≃ {a // event a} × B where
  toFun x := (⟨x.val.1, x.property⟩, x.val.2)
  invFun x := ⟨(x.1.val, x.2), x.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem probability_first {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (event : A → Prop) :
    probability (fun x : A × B => event x.1) = probability event := by
  rw [UniformChallenges.probability_card, UniformChallenges.probability_card,
    Fintype.card_congr (firstEventEquiv (B := B) event), Fintype.card_prod,
    Fintype.card_prod, Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right _ _ (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)

/-- Equipotent fibers imply the event law of a uniform image. -/
theorem probability_of_equiv_fibers {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (f : A → B) (b0 : B)
    (hne : Nonempty {a // f a = b0})
    (fibers : ∀ b, {a // f a = b} ≃ {a // f a = b0}) (event : B → Prop) :
    probability (fun a => event (f a)) = probability event := by
  letI := hne
  let e : A ≃ B × {a // f a = b0} :=
    (Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight fibers).trans (Equiv.sigmaEquivProd _ _))
  exact (probability_equiv e (fun x => event x.1)).trans (probability_first event)

/-- Left transport of permutation images gives a bijection of fibers. -/
private noncomputable def imageFiberEquiv {A : Type*}
    (s t u : Finset A) (tau : Equiv.Perm A) (h : permute tau t = u) :
    {sigma : Equiv.Perm A // permute sigma s = t} ≃
      {sigma : Equiv.Perm A // permute sigma s = u} where
  toFun sigma := ⟨sigma.val.trans tau, by rw [← permute_trans, sigma.property, h]⟩
  invFun sigma := ⟨sigma.val.trans tau.symm, by
    rw [← permute_trans, sigma.property, ← h, permute_trans]
    simp⟩
  left_inv sigma := by apply Subtype.ext; ext a; simp
  right_inv sigma := by apply Subtype.ext; ext a; simp

private def fixedWeightEquiv {A : Type*} (s : Finset A) (w : Nat) (hs : s.card = w)
    (t : {t : Finset A // t.card = w}) :
    {sigma : Equiv.Perm A //
      (⟨permute sigma s, (permute_card sigma s).trans hs⟩ :
        {t : Finset A // t.card = w}) = t} ≃
    {sigma : Equiv.Perm A // permute sigma s = t.val} :=
  Equiv.subtypeEquivRight (fun _ => Subtype.ext_iff)

/-- Uniform permutation of any fixed weight-w support is uniform on the
weight-w supports. This holds for every event on those supports. -/
theorem permuted_support_uniform {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (w : Nat) (hs : s.card = w) (event : Finset A → Prop) :
    probability (fun sigma : Equiv.Perm A => event (permute sigma s)) =
      subsetProbability (Finset.univ.powersetCard w)
        (by exact ⟨s, by simp [hs]⟩) event := by
  let B := {t : Finset A // t.card = w}
  let b0 : B := ⟨s, hs⟩
  letI : Nonempty B := ⟨b0⟩
  let f : Equiv.Perm A → B := fun sigma => ⟨permute sigma s, (permute_card sigma s).trans hs⟩
  have hne : Nonempty {sigma // f sigma = b0} :=
    ⟨⟨Equiv.refl A, by apply Subtype.ext; exact permute_refl s⟩⟩
  have hfibers (t : B) : Nonempty ({sigma // f sigma = t} ≃ {sigma // f sigma = b0}) := by
    obtain ⟨tau, htau⟩ := exists_permute_eq t.val s (t.property.trans hs.symm)
    exact ⟨(fixedWeightEquiv s w hs t).trans
      ((imageFiberEquiv s t.val s tau htau).trans (fixedWeightEquiv s w hs b0).symm)⟩
  have hp := probability_of_equiv_fibers f b0 hne (fun t => Classical.choice (hfibers t))
    (fun t => event t.val)
  change probability (fun sigma : Equiv.Perm A => event (permute sigma s)) = _ at hp
  rw [hp, UniformChallenges.probability_card, UniformChallenges.subset_probability_card]
  have e : B ≃ {t // t ∈ Finset.univ.powersetCard w} :=
    Equiv.subtypeEquivRight (fun t => by simp)
  have ee : {t : B // event t.val} ≃
      {t // t ∈ (Finset.univ.powersetCard w).filter event} :=
    { toFun := fun t => ⟨t.val.val, by simp [t.val.property, t.property]⟩
      invFun := fun t => ⟨⟨t.val, by simpa using (Finset.mem_filter.mp t.property).1⟩,
        (Finset.mem_filter.mp t.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_congr ee]
  simp only [Fintype.card_coe]

/-- The exact combinatorial factor in §5.1, for one fixed witness support.
It is not an equality for the existence of any regular solution. -/
theorem permuted_regular_probability {w m : Nat} (support : Finset (Coordinate w m))
    (hweight : support.card = w) (hm : 0 < m) :
    probability (fun sigma : Equiv.Perm (Coordinate w m) => Regular (permute sigma support)) =
      (m ^ w : ℝ≥0∞) / Nat.choose (w * m) w := by
  exact (permuted_support_uniform support w hweight Regular).trans
    (regular_support_probability w m hm)

end SDitH.Proofs.PermutationProbability
