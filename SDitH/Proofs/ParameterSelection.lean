import SDitH.Spec.ParameterSelection
import SDitH.Proofs.RegularSupport
import SDitH.Proofs.VariantParameters
import Mathlib.Tactic

namespace SDitH.Proofs.ParameterSelection

open Spec Spec.ParameterSelection
open scoped BigOperators Classical

theorem average_solution_count {A : Type*} (candidates : Finset A) (r : Nat)
    (syndrome : A → (Fin r → Fin 2)) :
    averageSolutionCount candidates r syndrome = binaryDensity candidates.card r := by
  have h : (∑ y : Fin r → Fin 2,
      (candidates.filter (fun x => syndrome x = y)).card) = candidates.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter candidates Finset.univ syndrome
  unfold averageSolutionCount binaryDensity
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  exact_mod_cast h

/-- Density is an exact average over all syndromes, not the probability that
there exists a solution and not a planted-instance distribution. -/
theorem rsd_density_average (w m r : Nat)
    (syndrome : Finset (Spec.RegularSupport.Coordinate w m) → (Fin r → Fin 2)) :
    averageSolutionCount
      ((Spec.RegularSupport.weightSupports w m).filter Spec.RegularSupport.Regular) r syndrome =
        rsdDensity w m r := by
  rw [average_solution_count, RegularSupport.regular_support_count]
  rfl

theorem sd_density_average (n w r : Nat)
    (syndrome : Finset (Fin n) → (Fin r → Fin 2)) :
    averageSolutionCount (Finset.univ.powersetCard w) r syndrome = sdDensity n w r := by
  rw [average_solution_count]
  simp [sdDensity]

theorem density_le_iff_count (count r : Nat) {theta : ℝ} (ht : 0 < theta) :
    binaryDensity count r ≤ 1 / theta ↔ (count : ℝ) * theta ≤ (2 : ℝ) ^ r := by
  rw [binaryDensity, div_le_div_iff₀ (by positivity) ht, one_mul]

theorem density_le_iff_logs {count : Nat} (hc : 0 < count) (r : Nat)
    {theta : ℝ} (ht : 0 < theta) :
    binaryDensity count r ≤ 1 / theta ↔
      Real.logb 2 (count : ℝ) + Real.logb 2 theta ≤ (r : ℝ) := by
  rw [density_le_iff_count count r ht,
    ← Real.logb_mul (by exact_mod_cast hc.ne') ht.ne',
    Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity),
    Real.rpow_natCast]

theorem density_le_iff_required {count : Nat} (hc : 0 < count) (r : Nat)
    {theta : ℝ} (ht : 0 < theta) :
    binaryDensity count r ≤ 1 / theta ↔ requiredCodimension count theta ≤ r := by
  rw [density_le_iff_logs hc r ht, requiredCodimension, Nat.ceil_le]

/-- Exact maximum-dimension characterization when a feasible dimension exists.
This theorem is derived from density, not asserted for the printed floor. -/
theorem density_dimension_iff {count n k : Nat} (hc : 0 < count) (hk : k ≤ n)
    {theta : ℝ} (ht : 0 < theta) (hf : requiredCodimension count theta ≤ n) :
    binaryDensity count (n - k) ≤ 1 / theta ↔ k ≤ n - requiredCodimension count theta := by
  rw [density_le_iff_required hc (n - k) ht]
  omega

theorem source_rsd_product_form (w m : Nat) (hw : 0 < w) (theta : ℝ) :
    sourceRSDMaxDimension (w * m) w theta =
      (w * m : Nat) - ⌊Real.logb 2 ((m ^ w : Nat) : ℝ) - Real.logb 2 theta⌋ := by
  have h : ((w * m : Nat) : ℝ) / w = (m : ℝ) := by
    push_cast
    field_simp
  simp only [sourceRSDMaxDimension, h, Nat.cast_pow, Real.logb_pow]

/-- With the printed floor and minus sign, the resulting density is at least
theta. The equality of the integer floor with r explicitly requires a valid
nonnegative codimension; no truncated subtraction is used. -/
theorem literal_floor_density_lower {count r : Nat} (hc : 0 < count)
    {theta : ℝ} (ht : 0 < theta)
    (hr : (r : ℤ) = ⌊Real.logb 2 (count : ℝ) - Real.logb 2 theta⌋) :
    theta ≤ binaryDensity count r := by
  have hfloor : (r : ℝ) ≤ Real.logb 2 (count : ℝ) - Real.logb 2 theta := by
    exact_mod_cast (hr ▸ Int.floor_le (Real.logb 2 (count : ℝ) - Real.logb 2 theta))
  rw [← Real.logb_div (by exact_mod_cast hc.ne') ht.ne',
    Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity),
    Real.rpow_natCast] at hfloor
  rw [binaryDensity, le_div_iff₀ (by positivity)]
  have h := (le_div_iff₀ ht).mp hfloor
  nlinarith

theorem literal_floor_violates_target {count r : Nat} (hc : 0 < count)
    {theta : ℝ} (ht : 1 < theta)
    (hr : (r : ℤ) = ⌊Real.logb 2 (count : ℝ) - Real.logb 2 theta⌋) :
    1 / theta < binaryDensity count r := by
  have ht0 : 0 < theta := by linarith
  have hlow := literal_floor_density_lower hc ht0 hr
  have hlt : 1 / theta < theta := by
    rw [div_lt_iff₀ ht0]
    nlinarith
  exact hlt.trans_le hlow

/-- A positive integral SD instance: the printed floor selects k=2 although
three weight-one candidates and two syndromes give density 3/2, greater than 1. -/
theorem source_sd_floor_counterexample :
    sourceSDDimension 3 1 = 2 ∧ sdDensity 3 1 (3 - 2) = 3 / 2 ∧
      1 < sdDensity 3 1 (3 - 2) := by
  have hlo : (1 : ℝ) ≤ Real.logb 2 3 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by norm_num)]
    norm_num
  have hhi : Real.logb 2 3 < (2 : ℝ) := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num)]
    norm_num
  have hf : ⌊Real.logb 2 (3 : ℝ)⌋ = (1 : ℤ) :=
    Int.floor_eq_iff.mpr ⟨by simpa using hlo, by convert hhi using 1; norm_num⟩
  norm_num [sourceSDDimension, hf, sdDensity, binaryDensity]

/-- Here the logarithms are exact integers: the theta sign alone causes the
RSD density claim to fail, independently of nonintegral floor rounding. -/
theorem source_rsd_theta_counterexample :
    sourceRSDMaxDimension 8 2 2 = 5 ∧ rsdDensity 2 4 (8 - 5) = 2 ∧
      1 / (2 : ℝ) < rsdDensity 2 4 (8 - 5) := by
  have hl : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : Nat) by norm_num, Real.logb_pow]
    norm_num
  norm_num [sourceRSDMaxDimension, hl, rsdDensity, binaryDensity]

theorem ceil8_covers (x : Nat) : x ≤ ceil8 x := by
  simpa only [VariantParameters.ceilMultiple_eight] using
    VariantParameters.ceilMultiple_covers 8 x (by decide)

theorem ceil8_minimal {x y : Nat} (hxy : x ≤ y) (hy : 8 ∣ y) : ceil8 x ≤ y := by
  obtain ⟨k, rfl⟩ := hy
  simpa only [VariantParameters.ceilMultiple_eight] using
    VariantParameters.ceilMultiple_minimal 8 x k (by decide) hxy

theorem byte_aligned_dimension {n maxDimension : Nat} (hm : maxDimension ≤ n)
    (hf : ceil8 (n - maxDimension) ≤ n) :
    byteAlignedDimension n maxDimension ≤ maxDimension ∧
    8 ∣ n - byteAlignedDimension n maxDimension ∧
    ∀ k ≤ maxDimension, 8 ∣ n - k → k ≤ byteAlignedDimension n maxDimension := by
  have hc := ceil8_covers (n - maxDimension)
  unfold byteAlignedDimension
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.sub_sub_self hf]
    exact ⟨ceilBytes (n - maxDimension), rfl⟩
  · intro k hk hb
    have hr := ceil8_minimal (x := n - maxDimension) (y := n - k) (by omega) hb
    omega

end SDitH.Proofs.ParameterSelection
