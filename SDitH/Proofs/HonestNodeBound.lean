import SDitH.Proofs.PosteriorNodeBound
import SDitH.Proofs.OwnViewExchange

/-! The posterior bound for the commitment view. The weight is the mean,
under the commitment run followed by a post-processing that does not read
an internal node, of a bounded function of the view pruned at the family's
own hidden keys, restricted to the families whose parent of the node is a
given seed and whose parent key and node key are fresh and distinct. The
weight is at most one and does not decrease under the exchange of the
node's block on the good fiber, so the posterior bound applies. -/

namespace SDitH.Proofs.HonestNodeBound

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys NodeExchange TreeExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange PosteriorNodeBound CipherResample ChargeExpect TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w₀ : World lambda s wit rnd) (root : Bits lambda) {Sig : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
  (w : Sig × World lambda s wit rnd → ℝ≥0∞) (a b : Nat) (q : Bits lambda)

/-- The freshness of a family at a node: its parent key and its key are not
among the starting history's keys and differ. -/
def Fresh (g : Family (Bits lambda) (Bits lambda)) : Prop :=
  parentKey S.layout g S.variant salt root b ∉ keysOf w₀.cipherHistory ∧
  S.layout.key (node (treeExpand S.layout g S.variant salt) root b) ∉ keysOf w₀.cipherHistory ∧
  parentKey S.layout g S.variant salt root b ≠ S.layout.key (node (treeExpand S.layout g S.variant salt) root b)

/-- The weight: the mean of the view function under the own-keys view,
restricted to the families with the given parent that are fresh at the
node. -/
def weight (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g)) *
    mean (ownView S salt witness root post (hiddenKeys S.layout g S.variant salt root a) { w₀ with family := g }) w

theorem weight_le_one (hw : ∀ x, w x ≤ 1) (g : Family (Bits lambda) (Bits lambda)) :
    weight S salt witness w₀ root post w a b q g ≤ 1 := by
  unfold weight
  calc _ ≤ 1 * 1 := mul_le_mul'
        (by by_cases h : (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g) <;>
          simp [h, indicator])
        (mean_le_const _ _ 1 fun x _ => hw x)
    _ = 1 := mul_one _

variable (v : Bits lambda) (hb : 1 < b) (hbk : b ≤ tau * 2 ^ kappa - 1) (hin : Function.Injective S.layout.input)
  (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (ha : a < 2 * (tau * 2 ^ kappa)) (hpath : b ∈ pathAddresses a)
  (hpost : ∀ c, ∀ x, post (.done (setTree b x c)) = post (.done c))

include hb hbk hin hl hL ha hpath hpost in
/-- The weight does not decrease under the exchange on the good fiber. -/
theorem weight_exchanged (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hg : OnFiber S.layout S.variant salt root b q v g)
    (hgood : Good S.layout (tau * 2 ^ kappa) S.variant salt root b q v g)
    (hbad : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root b q w₀.cipherHistory v' g) :
    weight S salt witness w₀ root post w a b q g ≤
      weight S salt witness w₀ root post w a b q (exchanged S.layout g S.variant salt root b v') := by
  have hparent : parentKey S.layout g S.variant salt root b = S.layout.key q := by
    unfold parentKey
    rw [hg.1]
  have hb' : node (treeExpand S.layout g S.variant salt) root b =
      S.layout.output (nodeBlock S.layout g S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout g S.variant salt root b hb
  unfold weight
  by_cases hcond : node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g
  · have hfr := hcond.2
    have hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v) := fun e he h =>
      hfr.2.1 (by rw [hb', hg.2]; exact mem_keysOf.mpr ⟨e, he, h⟩)
    have hpκ : S.layout.key q ≠ S.layout.key (S.layout.output v) := by
      rw [← hparent, ← hg.2, ← hb']
      exact hfr.2.2
    simp only [Bad, not_or, not_exists, not_and] at hbad
    obtain ⟨hbH, hbp, hb3, hb4⟩ := hbad
    have hfκ' : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v') := fun e he h =>
      hbH (by rw [← h]; exact mem_keysOf.mpr ⟨e, he, rfl⟩)
    have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL g S.variant salt root b hb (by omega) v'
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
    have hview := ownView_exchanged S salt witness { w₀ with family := g } root b hb hbk v' hin hl hL
      (by rw [hparent, hg.2]; exact hpκ) (by rw [hparent]; exact fun h => hbp h.symm)
      (fun c h1 hc hcb => by rw [hparent]; exact hgood.1 c h1 hc hcb)
      (fun c h1 hc hcb => by rw [hg.2]; exact hgood.2 c h1 hc hcb)
      (fun c _ hc => hb3 c hc)
      (fun c hc hsib hcb => by rw [hparent]; exact hb4 c hc hsib hcb)
      (fun e he => by rw [hg.2]; exact hfκ e he) hfκ' a ha hpath post (fun c => hpost c _)
    simp only at hview
    rw [hview]
    simp only [hcond, hcond', le_refl]
  · simp only [hcond, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

include hb hbk hin hl hL ha hpath hpost in
/-- The posterior bound for the commitment view at a fixed salt and root. -/
theorem honest_node_bound (hw : ∀ x, w x ≤ 1)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory)
    (hfp : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key q) (hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v))
    (hpκ : S.layout.key q ≠ S.layout.key (S.layout.output v)) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (fun g => weight S salt witness w₀ root post w a b q g *
          indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) ≤
      mean (posterior w₀.cipherHistory) (weight S salt witness w₀ root post w a b q) := by
  have hpos' : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  exact posterior_node_bound S.layout hin hl (tau * 2 ^ kappa) hL S.variant salt root b hb (by omega) q v
    w₀.cipherHistory hpos hfp hfκ hpκ (weight S salt witness w₀ root post w a b q)
    (weight_le_one S salt witness w₀ root post w a b q hw)
    (fun v' g hg hgood hbad => weight_exchanged S salt witness w₀ root post w a b q v hb hbk hin hl hL ha hpath hpost
      v' g hg hgood hbad) c hfiber

end
end SDitH.Proofs.HonestNodeBound
