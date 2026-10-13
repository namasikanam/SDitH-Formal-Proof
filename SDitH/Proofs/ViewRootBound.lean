import SDitH.Proofs.RootTouchBound

/-! The root bounds for an abstract view. The honest root bound and the
touching bound at the root were proved for the view pruned at one leaf's
hidden keys; they only use that the view is the same under the root
exchange on the good fiber. Here the view is any distribution chosen from
the root and the family with that invariance as a hypothesis. -/

namespace SDitH.Proofs.ViewRootBound

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys RootExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange RootPosteriorBound RootHonestBound RootTouchBound NodeTouchBound CipherResample ChargeExpect
open ChargeCutExpect TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (w₀ : World lambda s wit rnd)
  {Sig β : Type*} (V : Bits lambda → Family (Bits lambda) (Bits lambda) → PMF (Sig × World lambda s wit rnd))
  (w : Sig × World lambda s wit rnd → ℝ≥0∞)

/-- The weight: the mean of the view function under the view from the
pair's root, restricted to the pairs fresh at the root. -/
def weightVR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (FreshR S w₀ x)) * mean (V x.1 x.2) w

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem weightVR_le_one (hw : ∀ y, w y ≤ 1) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    weightVR S w₀ V w x ≤ 1 := by
  unfold weightVR
  calc _ ≤ 1 * 1 := mul_le_mul' (by by_cases h : FreshR S w₀ x <;> simp [h, indicator])
        (mean_le_const _ _ 1 fun y _ => hw y)
    _ = 1 := mul_one _

variable (hVR : ∀ (root root' : Bits lambda) (x : Bits lambda × Family (Bits lambda) (Bits lambda)), x.1 = root →
    GoodR S.layout (tau * 2 ^ kappa) S.variant salt x →
    ¬ BadR S.layout (tau * 2 ^ kappa) S.variant salt w₀.cipherHistory root' x → FreshR S w₀ x →
    V root' (rootExchanged S.layout x.2 root root') = V root x.2)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hVR in
/-- The weight does not decrease under the root exchange on the good fiber. -/
theorem weightVR_exchanged (root root' : Bits lambda) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) (hx : x.1 = root)
    (hgood : GoodR S.layout (tau * 2 ^ kappa) S.variant salt x)
    (hbad : ¬ BadR S.layout (tau * 2 ^ kappa) S.variant salt w₀.cipherHistory root' x) :
    weightVR S w₀ V w x ≤ weightVR S w₀ V w (root', rootExchanged S.layout x.2 root root') := by
  obtain ⟨r, g⟩ := x
  simp only at hx
  subst hx
  unfold weightVR
  by_cases hfr : FreshR S w₀ (r, g)
  · have hview := hVR r root' (r, g) rfl hgood hbad hfr
    simp only at hview
    have hfr' : FreshR S w₀ (root', rootExchanged S.layout g r root') := by
      simp only [BadR, not_or, not_exists, not_and] at hbad
      exact hbad.1
    show _ ≤ indicator (decide (FreshR S w₀ (root', rootExchanged S.layout g r root'))) *
      mean (V root' (rootExchanged S.layout g r root')) w
    rw [hview]
    simp only [hfr, hfr', decide_true, RandomOracleTrap.indicator_true, one_mul, le_refl]
  · simp only [hfr, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hVR in
/-- The posterior bound for the view at the root, at a fixed salt. -/
theorem honest_root_boundVR (hw : ∀ y, w y ≤ 1)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (root : Bits lambda)
    (hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key root) (c : Nat)
    (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory) (fun x => weightVR S w₀ V w x *
          indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some root))) ≤
      mean (rootDraw w₀.cipherHistory) (weightVR S w₀ V w) :=
  posterior_root_bound S.layout (tau * 2 ^ kappa) S.variant salt w₀.cipherHistory hpos root hfκ _
    (weightVR_le_one S w₀ V w hw)
    (fun root' x hx hgood hbad => weightVR_exchanged S salt w₀ V w hVR root root' x hx hgood hbad) c hfiberR

section Touch

variable (cont : Sig × World lambda s wit rnd → PMF β) (new : β → List (Entry (Bits lambda) (Bits lambda)))

/-- The probability that the continuation of the view records the root's
key. -/
def HitVR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (V x.1 x.2) (hitWeightR S cont new x.1)

/-- The expected number of entries the continuation records. -/
def expectedNewVR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (V x.1 x.2) fun y => mean (cont y) fun z => ((new z).length : ℝ≥0∞)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The good hit at a pair is one term of the sum over the seeds. -/
theorem goodHitVR_le_sum (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    indicator (decide (GoodAllR S salt w₀ x)) * HitVR S V cont new x ≤
      ∑ r : Bits lambda, weightVR S w₀ V (hitWeightR S cont new r) x *
        indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r)) := by
  by_cases hgood : GoodAllR S salt w₀ x
  · simp only [hgood, decide_true, RandomOracleTrap.indicator_true, one_mul]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ x.1))
    have hlabel : labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some x.1 :=
      (labelR_eq_iff _ _ _ _ x x.1).mpr ⟨hgood.1, rfl⟩
    rw [hlabel]
    simp only [decide_true, RandomOracleTrap.indicator_true, mul_one]
    unfold weightVR HitVR
    simp only [hgood.2, decide_true, RandomOracleTrap.indicator_true, one_mul, le_refl]
  · simp only [hgood, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

variable (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
  (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ c)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hVR hpos hfiberR in
/-- The bound for one seed: the posterior bound when the seed's key is
fresh, zero otherwise. -/
theorem seedVR_bound (r : Bits lambda) :
    ((Fintype.card (Bits lambda) - c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory) (fun x => weightVR S w₀ V (hitWeightR S cont new r) x *
          indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r))) ≤
      mean (rootDraw w₀.cipherHistory) (weightVR S w₀ V (hitWeightR S cont new r)) := by
  by_cases hfresh : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key r
  · exact honest_root_boundVR S salt w₀ V (hitWeightR S cont new r) hVR (hitWeightR_le_one S cont new r) hpos r hfresh c hfiberR
  · refine le_trans (le_of_eq ?_) (zero_le _)
    refine mul_eq_zero_of_right _ ((mean_le_const _ _ 0 fun x _ => ?_).antisymm (zero_le _))
    by_cases hlabel : labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r
    · obtain ⟨-, hr⟩ := (labelR_eq_iff _ _ _ _ x r).mp hlabel
      have hnotfresh : ¬ FreshR S w₀ x := by
        intro hfr
        apply hfresh
        intro e he h
        exact hfr (by rw [hr]; exact mem_keysOf.mpr ⟨e, he, h⟩)
      simp only [weightVR, hnotfresh, decide_false, RandomOracleTrap.indicator_false, zero_mul, le_refl]
    · simp only [hlabel, decide_false, RandomOracleTrap.indicator_false, mul_zero, le_refl]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hVR hpos hfiberR in
/-- The touching bound at the root for the view. -/
theorem root_touch_boundVR :
    ((Fintype.card (Bits lambda) - c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodAllR S salt w₀ x)) * HitVR S V cont new x) ≤
      (c : ℝ≥0∞) * mean (rootDraw w₀.cipherHistory) (expectedNewVR V cont new) := by
  set N : ℝ≥0∞ := ((Fintype.card (Bits lambda) - c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞)
    with hN
  calc N * mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodAllR S salt w₀ x)) * HitVR S V cont new x)
      ≤ N * mean (rootDraw w₀.cipherHistory) (fun x => ∑ r : Bits lambda,
          weightVR S w₀ V (hitWeightR S cont new r) x *
            indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r))) :=
        mul_le_mul' le_rfl (mean_le_mean _ _ _ fun x _ => goodHitVR_le_sum S salt w₀ V cont new x)
    _ = ∑ r : Bits lambda, N * mean (rootDraw w₀.cipherHistory) (fun x =>
          weightVR S w₀ V (hitWeightR S cont new r) x *
            indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r))) := by
        rw [← sum_mean (rootDraw w₀.cipherHistory) (fun r x => _) Finset.univ, Finset.mul_sum]
    _ ≤ ∑ r : Bits lambda, mean (rootDraw w₀.cipherHistory) (weightVR S w₀ V (hitWeightR S cont new r)) :=
        Finset.sum_le_sum fun r _ => seedVR_bound S salt w₀ V hVR cont new hpos c hfiberR r
    _ = mean (rootDraw w₀.cipherHistory) (fun x => ∑ r : Bits lambda, weightVR S w₀ V (hitWeightR S cont new r) x) :=
        sum_mean (rootDraw w₀.cipherHistory) (fun r x => weightVR S w₀ V (hitWeightR S cont new r) x) Finset.univ
    _ ≤ mean (rootDraw w₀.cipherHistory) (fun x => (c : ℝ≥0∞) * expectedNewVR V cont new x) := by
        refine mean_le_mean _ _ _ fun x _ => ?_
        unfold weightVR
        rw [← Finset.mul_sum, sum_mean _ (fun r y => hitWeightR S cont new r y) Finset.univ]
        have hsum : mean (V x.1 x.2) (fun y => ∑ r : Bits lambda, hitWeightR S cont new r y) ≤
            (c : ℝ≥0∞) * expectedNewVR V cont new x := by
          unfold expectedNewVR
          rw [← mean_mul_left]
          refine mean_le_mean _ _ _ fun y _ => ?_
          exact sum_root_hit_le S c hfiberR (cont y) new
        calc indicator (decide (FreshR S w₀ x)) * mean (V x.1 x.2) (fun y => ∑ r : Bits lambda, hitWeightR S cont new r y)
            ≤ 1 * ((c : ℝ≥0∞) * expectedNewVR V cont new x) :=
              mul_le_mul' (by by_cases h : FreshR S w₀ x <;> simp [h, indicator]) hsum
          _ = (c : ℝ≥0∞) * expectedNewVR V cont new x := one_mul _
    _ = (c : ℝ≥0∞) * mean (rootDraw w₀.cipherHistory) (expectedNewVR V cont new) := mean_mul_left _ _ _

end Touch

end
end SDitH.Proofs.ViewRootBound
