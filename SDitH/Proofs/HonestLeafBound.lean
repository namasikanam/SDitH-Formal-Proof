import SDitH.Proofs.PosteriorNodeBound
import SDitH.Proofs.PhaseViewLeaf
import SDitH.Proofs.HonestNodeBound

/-! The posterior bound for the phase view at a leaf. The weight is the mean
of a bounded function of the phase view pruned at the family's own hidden
keys, restricted to the families whose parent of the leaf is a given seed
and whose parent key and leaf key are fresh and distinct. The weight is at
most one and does not decrease under the exchange of the leaf's block on
the good fiber, since the phase view is unchanged by the exchange, so the
posterior bound applies: the weighted mass of the leaf's block at any
value is at most the total weight over the number of blocks less the bad
targets. -/

namespace SDitH.Proofs.HonestLeafBound

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys NodeExchange TreeExchange CommitPhaseExchange CommitRunExchange
open PhaseViewLeaf PosteriorNodeBound CipherResample ChargeExpect TreeStepFresh HonestNodeBound
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
  (w₀ : World lambda s wit rnd) (root : Bits lambda)
  (w : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
    (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda)) → ℝ≥0∞)
  (a b : Nat) (q : Bits lambda)

/-- The weight: the mean of the view function under the own-keys phase
view, restricted to the families with the given parent that are fresh at
the leaf. -/
def weightL (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g)) *
    mean (phaseView S salt g root (hiddenKeys S.layout g S.variant salt root a) w₀) w

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem weightL_le_one (hw : ∀ x, w x ≤ 1) (g : Family (Bits lambda) (Bits lambda)) :
    weightL S salt w₀ root w a b q g ≤ 1 := by
  unfold weightL
  calc _ ≤ 1 * 1 := mul_le_mul'
        (by by_cases h : (node (treeExpand S.layout g S.variant salt) root (b / 2) = q ∧ Fresh S salt w₀ root b g) <;>
          simp [h, indicator])
        (mean_le_const _ _ 1 fun x _ => hw x)
    _ = 1 := mul_one _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The phase view does not read the world's family. -/
theorem phaseView_setFamily (f g : Family (Bits lambda) (Bits lambda)) (K : List (Bits lambda)) :
    phaseView S salt g root K { w₀ with family := f } = phaseView S salt g root K w₀ := rfl

variable (v : Bits lambda) (hb : 1 < b) (hbL : b < 2 * (tau * 2 ^ kappa)) (hin : Function.Injective S.layout.input)
  (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (ha : a < 2 * (tau * 2 ^ kappa)) (hpath : b ∈ pathAddresses a)

omit [Field F] [Algebra (ZMod 2) F] in
include hb hbL hin hl hL ha hpath in
/-- The weight does not decrease under the exchange on the good fiber. -/
theorem weightL_exchanged (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hg : OnFiber S.layout S.variant salt root b q v g)
    (hgood : Good S.layout (tau * 2 ^ kappa) S.variant salt root b q v g)
    (hbad : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root b q w₀.cipherHistory v' g) :
    weightL S salt w₀ root w a b q g ≤
      weightL S salt w₀ root w a b q (exchanged S.layout g S.variant salt root b v') := by
  have hparent : parentKey S.layout g S.variant salt root b = S.layout.key q := by
    unfold parentKey
    rw [hg.1]
  have hb' : node (treeExpand S.layout g S.variant salt) root b =
      S.layout.output (nodeBlock S.layout g S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout g S.variant salt root b hb
  unfold weightL
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
    have hview := phaseView_exchanged S salt { w₀ with family := g } root b hb hbL v' hin hl hL
      (by rw [hparent, hg.2]; exact hpκ) (by rw [hparent]; exact fun h => hbp h.symm)
      (fun c h1 hc hcb => by rw [hparent]; exact hgood.1 c h1 hc hcb)
      (fun c h1 hc hcb => by rw [hg.2]; exact hgood.2 c h1 hc hcb)
      (fun c _ hc => hb3 c hc)
      (fun c hc hsib hcb => by rw [hparent]; exact hb4 c hc hsib hcb)
      (fun e he => by rw [hg.2]; exact hfκ e he) hfκ' a ha hpath
    simp only at hview
    rw [phaseView_setFamily, phaseView_setFamily] at hview
    rw [hview]
    simp only [hcond, hcond']
    exact le_rfl
  · simp only [hcond, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

omit [Field F] [Algebra (ZMod 2) F] in
include hb hbL hin hl hL ha hpath in
/-- The posterior bound for the phase view at a fixed salt and root, at a
leaf. -/
theorem honest_leaf_bound (hw : ∀ x, w x ≤ 1)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory)
    (hfp : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key q) (hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v))
    (hpκ : S.layout.key q ≠ S.layout.key (S.layout.output v)) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (fun g => weightL S salt w₀ root w a b q g *
          indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root b q v g = some (q, v)))) ≤
      mean (posterior w₀.cipherHistory) (weightL S salt w₀ root w a b q) :=
  posterior_node_bound S.layout hin hl (tau * 2 ^ kappa) hL S.variant salt root b hb hbL q v
    w₀.cipherHistory hpos hfp hfκ hpκ (weightL S salt w₀ root w a b q)
    (weightL_le_one S salt w₀ root w a b q hw)
    (fun v' g hg hgood hbad => weightL_exchanged S salt w₀ root w a b q v hb hbL hin hl hL ha hpath v' g hg hgood hbad) c hfiber

end
end SDitH.Proofs.HonestLeafBound
