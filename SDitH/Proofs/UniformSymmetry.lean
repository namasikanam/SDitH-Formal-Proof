import SDitH.Proofs.IntegerSamplingProbability

namespace SDitH.Proofs.UniformSymmetry

open scoped Classical ENNReal
noncomputable section

theorem equal_mass_uniform {A : Type*} [Fintype A] [Nonempty A] (p : PMF A)
    (h : ∀ a b, p a = p b) : p = PMF.uniformOfFintype A := by
  ext a
  rw [PMF.uniformOfFintype_apply]
  have hs : (Fintype.card A : ℝ≥0∞) * p a = 1 := by
    calc
      _ = ∑ b : A, p a := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ b : A, p b := Finset.sum_congr rfl (fun b _ => h a b)
      _ = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  have hn : (Fintype.card A : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    p a = (Fintype.card A : ℝ≥0∞)⁻¹ * ((Fintype.card A : ℝ≥0∞) * p a) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hn (ENNReal.natCast_ne_top _), one_mul]
    _ = _ := by rw [hs, mul_one]

theorem map_swap_mass {A : Type*} [DecidableEq A] (p : PMF A) (a b : A) : (p.map (Equiv.swap a b)) a = p b := by
  rw [PMF.map_apply, tsum_eq_single b]
  · simp
  · intro x hx
    have hne : a ≠ Equiv.swap a b x := by
      intro he
      have hb : x = b := by simpa using (Equiv.swap_apply_eq_iff.mp he.symm)
      exact hx hb
    simp [hne]

/-- A uniform source has a uniform image when every output transposition is
realized by a source equivalence. Callers must construct these equivalences. -/
theorem uniform_map_of_swaps {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [DecidableEq B]
    (label : A → B) (move : B → B → A ≃ A)
    (hmove : ∀ a b x, label (move a b x) = Equiv.swap a b (label x)) :
    (PMF.uniformOfFintype A).map label = PMF.uniformOfFintype B := by
  apply equal_mass_uniform
  intro a b
  have he := congrArg (fun p : PMF A => p.map label) (IntegerSamplingProbability.map_uniform_equiv (move a b))
  simp only [PMF.map_comp, Function.comp_def, hmove] at he
  have hh : ((PMF.uniformOfFintype A).map label).map (Equiv.swap a b) =
      (PMF.uniformOfFintype A).map label := by
    simpa only [PMF.map_comp, Function.comp_def] using he
  calc
    _ = (((PMF.uniformOfFintype A).map label).map (Equiv.swap a b)) a :=
      (congrArg (fun p : PMF B => p a) hh).symm
    _ = _ := map_swap_mass _ a b

end
end SDitH.Proofs.UniformSymmetry
