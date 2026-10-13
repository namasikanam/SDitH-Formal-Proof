import SDitH.Proofs.HonestNodeBound
import SDitH.Proofs.KeyWeightSum

/-! The touching bound at a hidden node. A continuation of the view records
entries; the node is touched when its key is among them. Summing the
posterior bound over the parent seed and the node's block, the probability
that a good and fresh family's node is touched is at most the fiber bound
times the expected number of recorded entries over the number of blocks
less the bad targets. -/

namespace SDitH.Proofs.NodeTouchBound

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys NodeExchange TreeExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange PosteriorNodeBound HonestNodeBound KeyWeightSum CipherResample ChargeExpect ChargeCutExpect
open TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w₀ : World lambda s wit rnd) (root : Bits lambda) {Sig β : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
  (cont : Sig × World lambda s wit rnd → PMF β) (new : β → List (Entry (Bits lambda) (Bits lambda))) (a b : Nat)

/-- The hit weight of a block: the probability that the continuation
records its key. -/
def hitWeight (v : Bits lambda) (x : Sig × World lambda s wit rnd) : ℝ≥0∞ :=
  mean (cont x) fun y => indicator (decide (S.layout.key (S.layout.output v) ∈ keysOf (new y)))

/-- A family good at the node with its own parent and block, and fresh. -/
def GoodAll (g : Family (Bits lambda) (Bits lambda)) : Prop :=
  Good S.layout (tau * 2 ^ kappa) S.variant salt root b (node (treeExpand S.layout g S.variant salt) root (b / 2))
    (nodeBlock S.layout g S.variant salt root b) g ∧ Fresh S salt w₀ root b g

/-- The probability that the continuation of the own-keys view records the
node's key. -/
def Hit (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (ownView S salt witness root post (hiddenKeys S.layout g S.variant salt root a) { w₀ with family := g })
    (hitWeight S cont new (nodeBlock S.layout g S.variant salt root b))

/-- The expected number of entries the continuation records. -/
def expectedNew (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (ownView S salt witness root post (hiddenKeys S.layout g S.variant salt root a) { w₀ with family := g }) fun x =>
    mean (cont x) fun y => ((new y).length : ℝ≥0∞)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem hitWeight_le_one (v : Bits lambda) (x : Sig × World lambda s wit rnd) : hitWeight S cont new v x ≤ 1 :=
  mean_le_const _ _ 1 fun y _ => by
    by_cases h : S.layout.key (S.layout.output v) ∈ keysOf (new y) <;> simp [h, indicator]

section Sums

variable {α γ : Type*}

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- A finite sum of means is the mean of the finite sum. -/
theorem sum_mean (p : PMF α) (G : γ → α → ℝ≥0∞) (T : Finset γ) :
    ∑ t ∈ T, mean p (G t) = mean p fun g => ∑ t ∈ T, G t g := by
  have := sum_mean_mul p (fun _ => (1 : ℝ≥0∞)) G T
  simpa only [one_mul] using this

end Sums

variable (hb : 1 < b) (hbk : b ≤ tau * 2 ^ kappa - 1) (hin : Function.Injective S.layout.input)
  (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (ha : a < 2 * (tau * 2 ^ kappa)) (hpath : b ∈ pathAddresses a)
  (hpost : ∀ c, ∀ x, post (.done (setTree b x c)) = post (.done c))
  (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
  (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)

/-- The good hit at a family is one term of the double sum over the parent
seed and the block. -/
theorem goodHit_le_sum (g : Family (Bits lambda) (Bits lambda)) :
    indicator (decide (GoodAll S salt w₀ root b g)) * Hit S salt witness w₀ root post cont new a b g ≤
      ∑ q : Bits lambda, ∑ v : Bits lambda,
        weight S salt witness w₀ root post (hitWeight S cont new v) a b q g *
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
    unfold weight Hit
    simp only [true_and, hgood.2, decide_true, RandomOracleTrap.indicator_true, one_mul, le_refl]
  · simp only [hgood, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

include hb hbk hin hl hL ha hpath hpost hpos hfiber in
/-- The bound for one parent seed and block: the posterior bound when the
parent key and the block's key are fresh and distinct, zero otherwise. -/
theorem pair_bound (q v : Bits lambda) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (fun g => weight S salt witness w₀ root post (hitWeight S cont new v) a b q g *
          indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) ≤
      mean (posterior w₀.cipherHistory) (weight S salt witness w₀ root post (hitWeight S cont new v) a b q) := by
  by_cases hfresh : (∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key q) ∧
      (∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v)) ∧
      S.layout.key q ≠ S.layout.key (S.layout.output v)
  · exact honest_node_bound S salt witness w₀ root post (hitWeight S cont new v) a b q v hb hbk hin hl hL ha hpath hpost
      (hitWeight_le_one S cont new v) hpos hfresh.1 hfresh.2.1 hfresh.2.2 c hfiber
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
      simp only [weight, hnot, decide_false, RandomOracleTrap.indicator_false, zero_mul, le_refl]
    · simp only [hlabel, decide_false, RandomOracleTrap.indicator_false, mul_zero, le_refl]

include hb hbk hin hl hL ha hpath hpost hpos hfiber in
/-- The touching bound at the node. -/
theorem node_touch_bound :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (fun g => indicator (decide (GoodAll S salt w₀ root b g)) *
          Hit S salt witness w₀ root post cont new a b g) ≤
      (c : ℝ≥0∞) * mean (posterior w₀.cipherHistory) (expectedNew S salt witness w₀ root post cont new a) := by
  set N : ℝ≥0∞ := ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞)
    with hN
  calc N * mean (posterior w₀.cipherHistory) (fun g => indicator (decide (GoodAll S salt w₀ root b g)) *
          Hit S salt witness w₀ root post cont new a b g)
      ≤ N * mean (posterior w₀.cipherHistory) (fun g => ∑ q : Bits lambda, ∑ v : Bits lambda,
          weight S salt witness w₀ root post (hitWeight S cont new v) a b q g *
            indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) :=
        mul_le_mul' le_rfl (mean_le_mean _ _ _ fun g _ => goodHit_le_sum S salt witness w₀ root post cont new a b g)
    _ = ∑ q : Bits lambda, ∑ v : Bits lambda, N * mean (posterior w₀.cipherHistory) (fun g =>
          weight S salt witness w₀ root post (hitWeight S cont new v) a b q g *
            indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) := by
        rw [← sum_mean (posterior w₀.cipherHistory) (fun q g => ∑ v : Bits lambda, _) Finset.univ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← sum_mean (posterior w₀.cipherHistory) (fun v g => _) Finset.univ, Finset.mul_sum]
    _ ≤ ∑ q : Bits lambda, ∑ v : Bits lambda,
          mean (posterior w₀.cipherHistory) (weight S salt witness w₀ root post (hitWeight S cont new v) a b q) :=
        Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun v _ =>
          pair_bound S salt witness w₀ root post cont new a b hb hbk hin hl hL ha hpath hpost hpos c hfiber q v
    _ = mean (posterior w₀.cipherHistory) (fun g => ∑ q : Bits lambda, ∑ v : Bits lambda,
          weight S salt witness w₀ root post (hitWeight S cont new v) a b q g) := by
        rw [Finset.sum_congr rfl fun q _ => sum_mean (posterior w₀.cipherHistory)
          (fun v g => weight S salt witness w₀ root post (hitWeight S cont new v) a b q g) Finset.univ,
          sum_mean (posterior w₀.cipherHistory)
            (fun q g => ∑ v : Bits lambda, weight S salt witness w₀ root post (hitWeight S cont new v) a b q g) Finset.univ]
    _ ≤ mean (posterior w₀.cipherHistory) (fun g => (c : ℝ≥0∞) * expectedNew S salt witness w₀ root post cont new a g) := by
        refine mean_le_mean _ _ _ fun g _ => ?_
        -- the sum over the block of the weights, at one parent
        have hinner : ∀ q : Bits lambda, ∑ v : Bits lambda, weight S salt witness w₀ root post (hitWeight S cont new v) a b q g =
            indicator (decide (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g)) *
              mean (ownView S salt witness root post (hiddenKeys S.layout g S.variant salt root a) { w₀ with family := g })
                (fun x => ∑ v : Bits lambda, hitWeight S cont new v x) := by
          intro q
          unfold weight
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
        have hsum : mean (ownView S salt witness root post (hiddenKeys S.layout g S.variant salt root a) { w₀ with family := g })
            (fun x => ∑ v : Bits lambda, hitWeight S cont new v x) ≤
            (c : ℝ≥0∞) * expectedNew S salt witness w₀ root post cont new a g := by
          unfold expectedNew
          rw [← mean_mul_left]
          refine mean_le_mean _ _ _ fun x _ => ?_
          exact sum_hit_weight_le S.layout c hfiber (cont x) new
        calc (∑ q : Bits lambda, indicator (decide (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧
                Fresh S salt w₀ root b g))) *
              mean (ownView S salt witness root post (hiddenKeys S.layout g S.variant salt root a) { w₀ with family := g })
                (fun x => ∑ v : Bits lambda, hitWeight S cont new v x)
            ≤ 1 * ((c : ℝ≥0∞) * expectedNew S salt witness w₀ root post cont new a g) := mul_le_mul' hone hsum
          _ = (c : ℝ≥0∞) * expectedNew S salt witness w₀ root post cont new a g := one_mul _
    _ = (c : ℝ≥0∞) * mean (posterior w₀.cipherHistory) (expectedNew S salt witness w₀ root post cont new a) :=
        mean_mul_left _ _ _

end
end SDitH.Proofs.NodeTouchBound
