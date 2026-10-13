import SDitH.Proofs.RootHonestBound
import SDitH.Proofs.NodeTouchBound

/-! The touching bound at the root. A continuation of the view records
entries; the root is touched when its key is among them. Summing the
posterior bound on the root over the seeds, the probability that a good
and fresh pair's root is touched is at most the fiber bound times the
expected number of recorded entries over the number of seeds less the bad
targets. -/

namespace SDitH.Proofs.RootTouchBound

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys RootExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange RootPosteriorBound RootHonestBound NodeTouchBound CipherResample ChargeExpect ChargeCutExpect
open TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w₀ : World lambda s wit rnd) {Sig β : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
  (cont : Sig × World lambda s wit rnd → PMF β) (new : β → List (Entry (Bits lambda) (Bits lambda))) (a : Nat)

/-- The hit weight of a seed: the probability that the continuation records
its key. -/
def hitWeightR (r : Bits lambda) (x : Sig × World lambda s wit rnd) : ℝ≥0∞ :=
  mean (cont x) fun y => indicator (decide (S.layout.key r ∈ keysOf (new y)))

/-- A pair good at the root and fresh. -/
def GoodAllR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : Prop :=
  GoodR S.layout (tau * 2 ^ kappa) S.variant salt x ∧ FreshR S w₀ x

/-- The probability that the continuation of the own-keys view records the
root's key. -/
def HitR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (ownView S salt witness x.1 post (hiddenKeys S.layout x.2 S.variant salt x.1 a) { w₀ with family := x.2 })
    (hitWeightR S cont new x.1)

/-- The expected number of entries the continuation records. -/
def expectedNewR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (ownView S salt witness x.1 post (hiddenKeys S.layout x.2 S.variant salt x.1 a) { w₀ with family := x.2 }) fun y =>
    mean (cont y) fun z => ((new z).length : ℝ≥0∞)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem hitWeightR_le_one (r : Bits lambda) (x : Sig × World lambda s wit rnd) : hitWeightR S cont new r x ≤ 1 :=
  mean_le_const _ _ 1 fun y _ => by
    by_cases h : S.layout.key r ∈ keysOf (new y) <;> simp [h, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The sum over seeds of the hit weights is at most the fiber bound times
the expected number of recorded entries. -/
theorem sum_root_hit_le {α : Type*} (c : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ c)
    (p : PMF α) (N : α → List (Entry (Bits lambda) (Bits lambda))) :
    ∑ r : Bits lambda, mean p (fun x => indicator (decide (S.layout.key r ∈ keysOf (N x)))) ≤
      (c : ℝ≥0∞) * mean p (fun x => ((N x).length : ℝ≥0∞)) := by
  rw [sum_mean p (fun r x => indicator (decide (S.layout.key r ∈ keysOf (N x)))) Finset.univ, ← mean_mul_left]
  refine mean_le_mean _ _ _ fun x _ => ?_
  have hcount : ∑ r : Bits lambda, indicator (decide (S.layout.key r ∈ keysOf (N x))) =
      ((Finset.univ.filter fun r : Bits lambda => S.layout.key r ∈ keysOf (N x)).card : ℝ≥0∞) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : S.layout.key r ∈ keysOf (N x) <;> simp [h, indicator]
  rw [hcount]
  calc ((Finset.univ.filter fun r : Bits lambda => S.layout.key r ∈ keysOf (N x)).card : ℝ≥0∞)
      ≤ ((c * (N x).length : ℕ) : ℝ≥0∞) := by
        refine Nat.cast_le.mpr ((count_root_hits S.layout c hfiberR (keysOf (N x))).trans ?_)
        exact Nat.mul_le_mul_left c (keysOf_card_le (N x))
    _ = (c : ℝ≥0∞) * ((N x).length : ℝ≥0∞) := by push_cast; rfl

/-- The good hit at a pair is one term of the sum over the seeds. -/
theorem goodHitR_le_sum (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    indicator (decide (GoodAllR S salt w₀ x)) * HitR S salt witness w₀ post cont new a x ≤
      ∑ r : Bits lambda, weightR S salt witness w₀ post (hitWeightR S cont new r) a x *
        indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r)) := by
  by_cases hgood : GoodAllR S salt w₀ x
  · simp only [hgood, decide_true, RandomOracleTrap.indicator_true, one_mul]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ x.1))
    have hlabel : labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some x.1 :=
      (labelR_eq_iff _ _ _ _ x x.1).mpr ⟨hgood.1, rfl⟩
    rw [hlabel]
    simp only [decide_true, RandomOracleTrap.indicator_true, mul_one]
    unfold weightR HitR
    simp only [hgood.2, decide_true, RandomOracleTrap.indicator_true, one_mul, le_refl]
  · simp only [hgood, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

variable (hL2 : 2 ≤ tau * 2 ^ kappa) (ha : a < 2 * (tau * 2 ^ kappa))
  (hpost : ∀ c, ∀ x, post (.done (setTree 1 x c)) = post (.done c))
  (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
  (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ c)

include hL2 ha hpost hpos hfiberR in
/-- The bound for one seed: the posterior bound when the seed's key is
fresh, zero otherwise. -/
theorem seed_bound (r : Bits lambda) :
    ((Fintype.card (Bits lambda) - c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory) (fun x => weightR S salt witness w₀ post (hitWeightR S cont new r) a x *
          indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r))) ≤
      mean (rootDraw w₀.cipherHistory) (weightR S salt witness w₀ post (hitWeightR S cont new r) a) := by
  by_cases hfresh : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key r
  · exact honest_root_bound S salt witness w₀ post (hitWeightR S cont new r) a hL2 ha hpost
      (hitWeightR_le_one S cont new r) hpos r hfresh c hfiberR
  · refine le_trans (le_of_eq ?_) (zero_le _)
    refine mul_eq_zero_of_right _ ((mean_le_const _ _ 0 fun x _ => ?_).antisymm (zero_le _))
    by_cases hlabel : labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r
    · obtain ⟨-, hr⟩ := (labelR_eq_iff _ _ _ _ x r).mp hlabel
      have hnotfresh : ¬ FreshR S w₀ x := by
        intro hfr
        apply hfresh
        intro e he h
        exact hfr (by rw [hr]; exact mem_keysOf.mpr ⟨e, he, h⟩)
      simp only [weightR, hnotfresh, decide_false, RandomOracleTrap.indicator_false, zero_mul, le_refl]
    · simp only [hlabel, decide_false, RandomOracleTrap.indicator_false, mul_zero, le_refl]

include hL2 ha hpost hpos hfiberR in
/-- The touching bound at the root. -/
theorem root_touch_bound :
    ((Fintype.card (Bits lambda) - c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodAllR S salt w₀ x)) *
          HitR S salt witness w₀ post cont new a x) ≤
      (c : ℝ≥0∞) * mean (rootDraw w₀.cipherHistory) (expectedNewR S salt witness w₀ post cont new a) := by
  set N : ℝ≥0∞ := ((Fintype.card (Bits lambda) - c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞)
    with hN
  calc N * mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodAllR S salt w₀ x)) *
          HitR S salt witness w₀ post cont new a x)
      ≤ N * mean (rootDraw w₀.cipherHistory) (fun x => ∑ r : Bits lambda,
          weightR S salt witness w₀ post (hitWeightR S cont new r) a x *
            indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r))) :=
        mul_le_mul' le_rfl (mean_le_mean _ _ _ fun x _ => goodHitR_le_sum S salt witness w₀ post cont new a x)
    _ = ∑ r : Bits lambda, N * mean (rootDraw w₀.cipherHistory) (fun x =>
          weightR S salt witness w₀ post (hitWeightR S cont new r) a x *
            indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some r))) := by
        rw [← sum_mean (rootDraw w₀.cipherHistory) (fun r x => _) Finset.univ, Finset.mul_sum]
    _ ≤ ∑ r : Bits lambda, mean (rootDraw w₀.cipherHistory) (weightR S salt witness w₀ post (hitWeightR S cont new r) a) :=
        Finset.sum_le_sum fun r _ => seed_bound S salt witness w₀ post cont new a hL2 ha hpost hpos c hfiberR r
    _ = mean (rootDraw w₀.cipherHistory) (fun x => ∑ r : Bits lambda,
          weightR S salt witness w₀ post (hitWeightR S cont new r) a x) :=
        sum_mean (rootDraw w₀.cipherHistory) (fun r x => weightR S salt witness w₀ post (hitWeightR S cont new r) a x) Finset.univ
    _ ≤ mean (rootDraw w₀.cipherHistory) (fun x => (c : ℝ≥0∞) * expectedNewR S salt witness w₀ post cont new a x) := by
        refine mean_le_mean _ _ _ fun x _ => ?_
        unfold weightR
        rw [← Finset.mul_sum, sum_mean _ (fun r y => hitWeightR S cont new r y) Finset.univ]
        have hsum : mean (ownView S salt witness x.1 post (hiddenKeys S.layout x.2 S.variant salt x.1 a) { w₀ with family := x.2 })
            (fun y => ∑ r : Bits lambda, hitWeightR S cont new r y) ≤
            (c : ℝ≥0∞) * expectedNewR S salt witness w₀ post cont new a x := by
          unfold expectedNewR
          rw [← mean_mul_left]
          refine mean_le_mean _ _ _ fun y _ => ?_
          exact sum_root_hit_le S c hfiberR (cont y) new
        calc indicator (decide (FreshR S w₀ x)) *
              mean (ownView S salt witness x.1 post (hiddenKeys S.layout x.2 S.variant salt x.1 a) { w₀ with family := x.2 })
                (fun y => ∑ r : Bits lambda, hitWeightR S cont new r y)
            ≤ 1 * ((c : ℝ≥0∞) * expectedNewR S salt witness w₀ post cont new a x) :=
              mul_le_mul' (by by_cases h : FreshR S w₀ x <;> simp [h, indicator]) hsum
          _ = (c : ℝ≥0∞) * expectedNewR S salt witness w₀ post cont new a x := one_mul _
    _ = (c : ℝ≥0∞) * mean (rootDraw w₀.cipherHistory) (expectedNewR S salt witness w₀ post cont new a) :=
        mean_mul_left _ _ _

end
end SDitH.Proofs.RootTouchBound
