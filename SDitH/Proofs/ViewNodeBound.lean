import SDitH.Proofs.NodeTouchBound

/-! The node bounds for an abstract view. The honest node bound and the
touching bound at a node were proved for the view pruned at one leaf's
hidden keys; they only use that the view is the same under the exchange of
the node on the good fiber. Here the view is any distribution chosen from
the family with that invariance as a hypothesis. -/

namespace SDitH.Proofs.ViewNodeBound

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys NodeExchange TreeExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange PosteriorNodeBound HonestNodeBound NodeTouchBound KeyWeightSum CipherResample ChargeExpect
open ChargeCutExpect TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (w₀ : World lambda s wit rnd) (root : Bits lambda)
  {Sig β : Type*} (V : Family (Bits lambda) (Bits lambda) → PMF (Sig × World lambda s wit rnd))
  (w : Sig × World lambda s wit rnd → ℝ≥0∞) (b : Nat) (q : Bits lambda)

/-- The weight: the mean of the view function under the view, restricted
to the families with the given parent that are fresh at the node. -/
def weightV (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g)) *
    mean (V g) w

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem weightV_le_one (hw : ∀ x, w x ≤ 1) (g : Family (Bits lambda) (Bits lambda)) :
    weightV S salt w₀ root V w b q g ≤ 1 := by
  unfold weightV
  calc _ ≤ 1 * 1 := mul_le_mul'
        (by by_cases h : (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g) <;>
          simp [h, indicator])
        (mean_le_const _ _ 1 fun x _ => hw x)
    _ = 1 := mul_one _

variable (hb : 1 < b) (hbL : b < 2 * (tau * 2 ^ kappa)) (hin : Function.Injective S.layout.input)
  (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (hV : ∀ (q v v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)), OnFiber S.layout S.variant salt root b q v g →
    Good S.layout (tau * 2 ^ kappa) S.variant salt root b q v g →
    ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root b q w₀.cipherHistory v' g → Fresh S salt w₀ root b g →
    V (exchanged S.layout g S.variant salt root b v') = V g)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hb hbL hin hl hL hV in
/-- The weight does not decrease under the exchange on the good fiber. -/
theorem weightV_exchanged (v v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hg : OnFiber S.layout S.variant salt root b q v g)
    (hgood : Good S.layout (tau * 2 ^ kappa) S.variant salt root b q v g)
    (hbad : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root b q w₀.cipherHistory v' g) :
    weightV S salt w₀ root V w b q g ≤ weightV S salt w₀ root V w b q (exchanged S.layout g S.variant salt root b v') := by
  have hparent : parentKey S.layout g S.variant salt root b = S.layout.key q := by
    unfold parentKey
    rw [hg.1]
  have hb' : node (treeExpand S.layout g S.variant salt) root b =
      S.layout.output (nodeBlock S.layout g S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout g S.variant salt root b hb
  unfold weightV
  by_cases hcond : node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g
  · have hfr := hcond.2
    have hview := hV q v v' g hg hgood hbad hfr
    have hpκ : S.layout.key q ≠ S.layout.key (S.layout.output v) := by
      rw [← hparent, ← hg.2, ← hb']
      exact hfr.2.2
    simp only [Bad, not_or, not_exists, not_and] at hbad
    obtain ⟨hbH, hbp, hb3, hb4⟩ := hbad
    have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL g S.variant salt root b hb hbL v'
      (by rw [hparent, hg.2]; exact hpκ) (by rw [hparent]; exact fun h => hbp h.symm)
      (fun c h1 hc hcb => by rw [hparent]; exact hgood.1 c h1 hc hcb)
      (fun c h1 hc hcb => by rw [hg.2]; exact hgood.2 c h1 hc hcb)
      (fun c _ hc => hb3 c hc)
      (fun c hc hsib hcb => by rw [hparent]; exact hb4 c hc hsib hcb)
    have hhalf : node (treeExpand S.layout (exchanged S.layout g S.variant salt root b v') S.variant salt) root (b / 2) = q := by
      rw [hnode (b / 2) (by omega), if_neg (by omega), hg.1]
    have hcond' : node (treeExpand S.layout (exchanged S.layout g S.variant salt root b v') S.variant salt) root (b / 2) = q ∧
        Fresh S salt w₀ root b (exchanged S.layout g S.variant salt root b v') := by
      refine ⟨hhalf, ?_, ?_, ?_⟩
      · show S.layout.key (node (treeExpand S.layout (exchanged S.layout g S.variant salt root b v') S.variant salt) root (b / 2)) ∉ _
        rw [hhalf, ← hparent]
        exact hfr.1
      · rw [hnode b (by omega), if_pos rfl]
        exact hbH
      · show S.layout.key (node (treeExpand S.layout (exchanged S.layout g S.variant salt root b v') S.variant salt) root (b / 2)) ≠ _
        rw [hhalf, hnode b (by omega), if_pos rfl]
        exact fun h => hbp h.symm
    rw [hview]
    simp only [hcond, hcond', le_refl]
  · simp only [hcond, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hb hbL hin hl hL hV in
/-- The posterior bound for the view at a fixed salt and root. -/
theorem honest_node_boundV (hw : ∀ x, w x ≤ 1) (v : Bits lambda)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory)
    (hfp : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key q) (hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v))
    (hpκ : S.layout.key q ≠ S.layout.key (S.layout.output v)) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (fun g => weightV S salt w₀ root V w b q g *
          indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) ≤
      mean (posterior w₀.cipherHistory) (weightV S salt w₀ root V w b q) :=
  posterior_node_bound S.layout hin hl (tau * 2 ^ kappa) hL S.variant salt root b hb hbL q v
    w₀.cipherHistory hpos hfp hfκ hpκ (weightV S salt w₀ root V w b q)
    (weightV_le_one S salt w₀ root V w b q hw)
    (fun v' g hg hgood hbad => weightV_exchanged S salt w₀ root V w b q hb hbL hin hl hL hV v v' g hg hgood hbad) c hfiber

section Touch

variable (cont : Sig × World lambda s wit rnd → PMF β) (new : β → List (Entry (Bits lambda) (Bits lambda)))

/-- The probability that the continuation of the view records the node's
key. -/
def HitV (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (V g) (hitWeight S cont new (nodeBlock S.layout g S.variant salt root b))

/-- The expected number of entries the continuation records. -/
def expectedNewV (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (V g) fun x => mean (cont x) fun y => ((new y).length : ℝ≥0∞)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The good hit at a family is one term of the double sum over the parent
seed and the block. -/
theorem goodHitV_le_sum (g : Family (Bits lambda) (Bits lambda)) :
    indicator (decide (GoodAll S salt w₀ root b g)) * HitV S salt root V b cont new g ≤
      ∑ q : Bits lambda, ∑ v : Bits lambda,
        weightV S salt w₀ root V (hitWeight S cont new v) b q g *
          indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v))) := by
  by_cases hgood : GoodAll S salt w₀ root b g
  · simp only [hgood, decide_true, RandomOracleTrap.indicator_true, one_mul]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ
      (node (treeExpand S.layout g S.variant salt) root (b / 2))))
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ
      (nodeBlock S.layout g S.variant salt root b)))
    have hlabel : label S.layout (tau * 2 ^ kappa) S.variant salt root b
        (node (treeExpand S.layout g S.variant salt) root (b / 2)) (nodeBlock S.layout g S.variant salt root b) g =
        some (node (treeExpand S.layout g S.variant salt) root (b / 2), nodeBlock S.layout g S.variant salt root b) :=
      (label_eq_iff _ _ _ _ _ _ _ _ g).mpr ⟨hgood.1, rfl, rfl⟩
    rw [hlabel]
    simp only [decide_true, RandomOracleTrap.indicator_true, mul_one]
    unfold weightV HitV
    simp only [true_and, hgood.2, decide_true, RandomOracleTrap.indicator_true, one_mul, le_refl]
  · simp only [hgood, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

variable (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
  (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hb hbL hin hl hL hV hpos hfiber in
/-- The bound for one parent seed and block: the posterior bound when the
parent key and the block's key are fresh and distinct, zero otherwise. -/
theorem pairV_bound (q v : Bits lambda) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (fun g => weightV S salt w₀ root V (hitWeight S cont new v) b q g *
          indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) ≤
      mean (posterior w₀.cipherHistory) (weightV S salt w₀ root V (hitWeight S cont new v) b q) := by
  by_cases hfresh : (∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key q) ∧
      (∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v)) ∧
      S.layout.key q ≠ S.layout.key (S.layout.output v)
  · exact honest_node_boundV S salt w₀ root V (hitWeight S cont new v) b q hb hbL hin hl hL hV
      (hitWeight_le_one S cont new v) v hpos hfresh.1 hfresh.2.1 hfresh.2.2 c hfiber
  · refine le_trans (le_of_eq ?_) (zero_le _)
    refine mul_eq_zero_of_right _ ((mean_le_const _ _ 0 fun g _ => ?_).antisymm (zero_le _))
    by_cases hlabel : label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)
    · obtain ⟨-, hq, hv⟩ := (label_eq_iff _ _ _ _ _ _ _ _ g).mp hlabel
      have hparent : parentKey S.layout g S.variant salt root b = S.layout.key q := by
        unfold parentKey
        rw [hq]
      have hb' : S.layout.key (node (treeExpand S.layout g S.variant salt) root b) = S.layout.key (S.layout.output v) := by
        rw [node_eq_output_nodeBlock S.layout g S.variant salt root b hb, hv]
      have hnotfresh : ¬ Fresh S salt w₀ root b g := by
        intro hfr
        apply hfresh
        refine ⟨fun e he h => hfr.1 (by rw [hparent]; exact mem_keysOf.mpr ⟨e, he, h⟩),
          fun e he h => hfr.2.1 (by rw [hb']; exact mem_keysOf.mpr ⟨e, he, h⟩), ?_⟩
        rw [← hparent, ← hb']
        exact hfr.2.2
      have hnot : ¬ (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g) :=
        fun h => hnotfresh h.2
      simp only [weightV, hnot, decide_false, RandomOracleTrap.indicator_false, zero_mul, le_refl]
    · simp only [hlabel, decide_false, RandomOracleTrap.indicator_false, mul_zero, le_refl]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hb hbL hin hl hL hV hpos hfiber in
/-- The touching bound at the node for the view. -/
theorem node_touch_boundV :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (fun g => indicator (decide (GoodAll S salt w₀ root b g)) *
          HitV S salt root V b cont new g) ≤
      (c : ℝ≥0∞) * mean (posterior w₀.cipherHistory) (expectedNewV V cont new) := by
  set N : ℝ≥0∞ := ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞)
    with hN
  calc N * mean (posterior w₀.cipherHistory) (fun g => indicator (decide (GoodAll S salt w₀ root b g)) *
          HitV S salt root V b cont new g)
      ≤ N * mean (posterior w₀.cipherHistory) (fun g => ∑ q : Bits lambda, ∑ v : Bits lambda,
          weightV S salt w₀ root V (hitWeight S cont new v) b q g *
            indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) :=
        mul_le_mul' le_rfl (mean_le_mean _ _ _ fun g _ => goodHitV_le_sum S salt w₀ root V b cont new g)
    _ = ∑ q : Bits lambda, ∑ v : Bits lambda, N * mean (posterior w₀.cipherHistory) (fun g =>
          weightV S salt w₀ root V (hitWeight S cont new v) b q g *
            indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) := by
        rw [← sum_mean (posterior w₀.cipherHistory) (fun q g => ∑ v : Bits lambda, _) Finset.univ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← sum_mean (posterior w₀.cipherHistory) (fun v g => _) Finset.univ, Finset.mul_sum]
    _ ≤ ∑ q : Bits lambda, ∑ v : Bits lambda,
          mean (posterior w₀.cipherHistory) (weightV S salt w₀ root V (hitWeight S cont new v) b q) :=
        Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun v _ =>
          pairV_bound S salt w₀ root V b hb hbL hin hl hL hV cont new hpos c hfiber q v
    _ = mean (posterior w₀.cipherHistory) (fun g => ∑ q : Bits lambda, ∑ v : Bits lambda,
          weightV S salt w₀ root V (hitWeight S cont new v) b q g) := by
        rw [Finset.sum_congr rfl fun q _ => sum_mean (posterior w₀.cipherHistory)
          (fun v g => weightV S salt w₀ root V (hitWeight S cont new v) b q g) Finset.univ,
          sum_mean (posterior w₀.cipherHistory)
            (fun q g => ∑ v : Bits lambda, weightV S salt w₀ root V (hitWeight S cont new v) b q g) Finset.univ]
    _ ≤ mean (posterior w₀.cipherHistory) (fun g => (c : ℝ≥0∞) * expectedNewV V cont new g) := by
        refine mean_le_mean _ _ _ fun g _ => ?_
        have hinner : ∀ q : Bits lambda, ∑ v : Bits lambda, weightV S salt w₀ root V (hitWeight S cont new v) b q g =
            indicator (decide (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g)) *
              mean (V g) (fun x => ∑ v : Bits lambda, hitWeight S cont new v x) := by
          intro q
          unfold weightV
          rw [← Finset.mul_sum, sum_mean _ (fun v x => hitWeight S cont new v x) Finset.univ]
        simp only [hinner]
        rw [← Finset.sum_mul]
        have hone : ∑ q : Bits lambda, indicator (decide (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧
            Fresh S salt w₀ root b g)) ≤ 1 := by
          have h : ∀ q : Bits lambda, indicator (decide (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧
              Fresh S salt w₀ root b g)) =
              if node (treeExpand S.layout g S.variant salt) root (b / 2) = q then
                indicator (decide (Fresh S salt w₀ root b g)) else 0 := by
            intro q
            by_cases hq : node (treeExpand S.layout g S.variant salt) root (b / 2) = q <;> simp [hq, indicator]
          simp only [h, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          by_cases hf : Fresh S salt w₀ root b g <;> simp [hf, indicator]
        have hsum : mean (V g) (fun x => ∑ v : Bits lambda, hitWeight S cont new v x) ≤
            (c : ℝ≥0∞) * expectedNewV V cont new g := by
          unfold expectedNewV
          rw [← mean_mul_left]
          refine mean_le_mean _ _ _ fun x _ => ?_
          exact sum_hit_weight_le S.layout c hfiber (cont x) new
        calc (∑ q : Bits lambda, indicator (decide (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧
                Fresh S salt w₀ root b g))) * mean (V g) (fun x => ∑ v : Bits lambda, hitWeight S cont new v x)
            ≤ 1 * ((c : ℝ≥0∞) * expectedNewV V cont new g) := mul_le_mul' hone hsum
          _ = (c : ℝ≥0∞) * expectedNewV V cont new g := one_mul _
    _ = (c : ℝ≥0∞) * mean (posterior w₀.cipherHistory) (expectedNewV V cont new) :=
        mean_mul_left _ _ _

end Touch

end
end SDitH.Proofs.ViewNodeBound
