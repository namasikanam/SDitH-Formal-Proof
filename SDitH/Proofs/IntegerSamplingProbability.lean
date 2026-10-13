import SDitH.Proofs.IntegerSampling
import SDitH.Proofs.UniformChallenges

/-! Finite uniform laws for the specified integer-sampling prefix and the
arithmetic of its threshold. The residue theorem concerns v % m as a mathematical
function; it does not bind the source's undefined B to v or claim that the
literal SampleIntegers routine has returned a uniformly sampled position.
Concrete PRG/XOF byte distributions remain outside these laws. -/

namespace SDitH.Proofs.IntegerSamplingProbability

set_option maxRecDepth 4096

open Spec.IntegerSampling Spec.DomainSeparation Spec.UniformChallenges
open scoped BigOperators ENNReal Classical

theorem map_uniform_equiv {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) : (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a ha
    have hn : b ≠ e a := fun h => ha (e.injective (h.symm.trans (e.apply_symm_apply b).symm))
    simp [hn]

/-- Four independent uniform bytes assemble to a uniform 32-bit word. -/
theorem uniform_word32 :
    (PMF.uniformOfFintype (Fin 4 → Byte)).map word32 = PMF.uniformOfFintype Word :=
  map_uniform_equiv wordEquiv

theorem probability_nat_card {A : Type*} [Fintype A] [Nonempty A] (event : A → Prop) :
    probability event = (Nat.card {a // event a} : ℝ≥0∞) / Nat.card A := by
  classical
  rw [UniformChallenges.probability_card]
  simp only [Nat.card_eq_fintype_card]

theorem probability_equiv {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) (event : B → Prop) :
    probability (fun a => event (e a)) = probability event := by
  have h := congrArg (fun p : PMF B => p.toOuterMeasure {b | event b}) (map_uniform_equiv e)
  dsimp only at h
  rw [PMF.toOuterMeasure_map_apply] at h
  exact h

private def prefixEquiv (bound t : Nat) (ht : t ≤ bound) :
    {v : Fin bound // v.val < t} ≃ Fin t where
  toFun v := ⟨v.val.val, v.property⟩
  invFun v := ⟨Fin.castLE ht v, v.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem prefix_card (bound t : Nat) (ht : t ≤ bound) :
    Nat.card {v : Fin bound // v.val < t} = t := by
  simpa using Nat.card_congr (prefixEquiv bound t ht)

/-- Exact acceptance probability for the explicit uniform word law. -/
theorem accepted_probability_at_bound (bound m : Nat) [NeZero bound] :
    probability (fun v : Fin bound => v.val < threshold bound m) =
      (threshold bound m : ℝ≥0∞) / bound := by
  classical
  rw [probability_nat_card, Nat.card_fin,
    prefix_card bound (threshold bound m) (IntegerSampling.threshold_le bound m)]

theorem accepted_probability (m : Nat) :
    probability (fun v : Word => v.val < sourceThreshold m) =
      (sourceThreshold m : ℝ≥0∞) / wordBound :=
  accepted_probability_at_bound wordBound m

theorem accepted_bytes_probability (m : Nat) :
    probability (fun bytes : Fin 4 → Byte => (word32 bytes).val < sourceThreshold m) =
      (sourceThreshold m : ℝ≥0∞) / wordBound := by
  exact (probability_equiv wordEquiv (fun v => v.val < sourceThreshold m)).trans (accepted_probability m)

theorem rejected_probability_at_bound (bound m : Nat) [NeZero bound] :
    probability (fun v : Fin bound => threshold bound m ≤ v.val) =
      ((bound - threshold bound m : Nat) : ℝ≥0∞) / bound := by
  classical
  rw [probability_nat_card, Nat.card_fin]
  congr 1
  have h := Fintype.card_subtype_compl (fun v : Fin bound => v.val < threshold bound m)
  simp only [← Nat.card_eq_fintype_card] at h
  simp only [not_lt, Nat.card_fin, prefix_card bound (threshold bound m)
    (IntegerSampling.threshold_le bound m)] at h
  exact_mod_cast h

theorem rejected_probability (m : Nat) :
    probability (fun v : Word => sourceThreshold m ≤ v.val) =
      ((wordBound - sourceThreshold m : Nat) : ℝ≥0∞) / wordBound :=
  rejected_probability_at_bound wordBound m

/-- The congruence classes below q*m each have exactly q elements. -/
private def residueFiberEquiv (q m : Nat) (j : Fin m) :
    {v : Fin (q * m) // v.val % m = j.val} ≃ Fin q where
  toFun v := (finProdFinEquiv.symm v.val).1
  invFun a := ⟨finProdFinEquiv (a, j), by
    simpa [finProdFinEquiv] using Nat.mod_eq_of_lt j.isLt⟩
  left_inv v := by
    apply Subtype.ext
    apply finProdFinEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact v.property.symm
  right_inv a := by simp

theorem residue_card (bound m : Nat) (j : Fin m) :
    Nat.card {v : Fin (threshold bound m) // v.val % m = j.val} = bound / m := by
  simpa [threshold] using Nat.card_congr (residueFiberEquiv (bound / m) m j)

/-- The modulo of a uniformly selected accepted-range value is uniform.
This arithmetic statement is intentionally separate from the source's
undefined accepted-value assignment and from any claim about PRG randomness. -/
theorem residue_probability (bound m : Nat) (hm : 0 < m) (hmb : m ≤ bound) (j : Fin m) :
    letI : NeZero (threshold bound m) := ⟨ne_of_gt (IntegerSampling.threshold_pos bound m hm hmb)⟩
    probability (fun v : Fin (threshold bound m) => v.val % m = j.val) = (m : ℝ≥0∞)⁻¹ := by
  classical
  letI : NeZero (threshold bound m) := ⟨ne_of_gt (IntegerSampling.threshold_pos bound m hm hmb)⟩
  rw [probability_nat_card, Nat.card_fin,
    residue_card bound m j]
  have hq : 0 < bound / m := (Nat.one_le_div_iff hm).mpr hmb
  have hq0 : ((bound / m : Nat) : ℝ≥0∞) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hqt : ((bound / m : Nat) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  simp only [threshold, Nat.cast_mul, div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hq0) (Or.inl hqt), ← mul_assoc,
    ENNReal.mul_inv_cancel hq0 hqt, one_mul]

end SDitH.Proofs.IntegerSamplingProbability
