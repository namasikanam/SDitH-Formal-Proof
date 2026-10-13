import SDitH.Proofs.PhaseViewLeafAll
import SDitH.Proofs.LeafExchangeDistinct

/-! The joint one-sided uniformity of the hidden leaves' blocks. For a
bounded function of the families invariant under the exchange at any
hidden leaf on the distinct trees, the weighted mass of the families on
which a set of executions' hidden leaves have given parent seeds and
blocks, on the distinct trees, is at most the total weight over the number
of blocks less the bad targets, raised to the number of executions. The
induction over the executions fixes one more leaf at a time; the weight
with the other leaves fixed is invariant since the exchange keeps the
tree distinct and the other leaves' fibers. -/

namespace SDitH.Proofs.LeafJointBound

open Spec.BAVC Spec.DomainSeparation Spec.SeedTree Spec.SeedPrimitives Spec.SharedScheme Spec.SharedSigner
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries TreeExchange NodeExchange PosteriorNodeBound HonestNodeBound NodeTouchBound TreeDistinct
open TreeStepFresh LeafExchangeDistinct CipherResample ChargeExpect
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (w₀ : World lambda s wit rnd)
  (root : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (Φ : Family (Bits lambda) (Bits lambda) → ℝ≥0∞)

/-- The hidden leaf of an execution. -/
def leaf (e : Fin tau) : Nat := leafAddress e (hidden e)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem leaf_bounds (e : Fin tau) : tau * 2 ^ kappa ≤ leaf hidden e ∧ leaf hidden e < 2 * (tau * 2 ^ kappa) :=
  ⟨Nat.le_add_right _ _, (SDitH.Proofs.SeedTree.leafAddress_bounds e (hidden e)).2⟩

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem leaf_ne (e e' : Fin tau) (h : e ≠ e') : leaf hidden e ≠ leaf hidden e' := fun heq =>
  h (SDitH.Proofs.SeedTree.leafOffset_injective e e' (hidden e) (hidden e') (by unfold leaf leafAddress at heq; omega)).1

/-- The fiber indicator of an execution's hidden leaf. -/
def fiberInd (q v : Fin tau → Bits lambda) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (OnFiber S.layout S.variant salt root (leaf hidden e) (q e) (v e) g))

/-- The joint weight: the function on the distinct trees with a set of
executions' hidden leaves on their fibers. -/
def jointWeight (q v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory)) * Φ g *
    ∏ e ∈ T, fiberInd S salt root hidden q v e g

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem fiberInd_le_one (q v : Fin tau → Bits lambda) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda)) :
    fiberInd S salt root hidden q v e g ≤ 1 := by
  unfold fiberInd
  by_cases h : OnFiber S.layout S.variant salt root (leaf hidden e) (q e) (v e) g <;> simp [h, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem jointWeight_le_one (hΦ : ∀ g, Φ g ≤ 1) (q v : Fin tau → Bits lambda) (T : Finset (Fin tau))
    (g : Family (Bits lambda) (Bits lambda)) : jointWeight S salt w₀ root hidden Φ q v T g ≤ 1 := by
  unfold jointWeight
  calc _ ≤ 1 * 1 * 1 := mul_le_mul' (mul_le_mul'
        (by by_cases h : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory <;> simp [h, indicator])
        (hΦ g)) (Finset.prod_le_one (fun e _ => zero_le _) fun e _ => fiberInd_le_one S salt root hidden q v e g)
    _ = 1 := by ring

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- Inserting an execution multiplies the joint weight by its fiber
indicator. -/
theorem jointWeight_insert (q v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (e : Fin tau) (he : e ∉ T)
    (g : Family (Bits lambda) (Bits lambda)) :
    jointWeight S salt w₀ root hidden Φ q v (insert e T) g =
      jointWeight S salt w₀ root hidden Φ q v T g * fiberInd S salt root hidden q v e g := by
  unfold jointWeight
  rw [Finset.prod_insert he]
  ring

variable (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (hΦ : ∀ g, Φ g ≤ 1)
  (hinv : ∀ (e : Fin tau) (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)),
    Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory →
    ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e)
      (node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2)) w₀.cipherHistory v' g →
    Φ (exchanged S.layout g S.variant salt root (leaf hidden e) v') = Φ g)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 hin hl hL hinv in
/-- The joint weight does not decrease under the exchange at a leaf outside
the fixed set, on the good fiber. -/
theorem jointWeight_exchanged (q v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (e : Fin tau) (he : e ∉ T)
    (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hg : OnFiber S.layout S.variant salt root (leaf hidden e) (q e) (v e) g)
    (hbad : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) (q e) w₀.cipherHistory v' g) :
    jointWeight S salt w₀ root hidden Φ q v T g ≤
      jointWeight S salt w₀ root hidden Φ q v T (exchanged S.layout g S.variant salt root (leaf hidden e) v') := by
  have hleaf := leaf_bounds hidden e
  have hb : 1 < leaf hidden e := by omega
  have hbL : leaf hidden e < 2 * (tau * 2 ^ kappa) := hleaf.2
  unfold jointWeight
  by_cases hd : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory
  · have hbad' : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e)
        (node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2)) w₀.cipherHistory v' g := by
      rw [hg.1]; exact hbad
    have hd' := distinct_exchanged S.layout hin hl (tau * 2 ^ kappa) hL g S.variant salt root w₀.cipherHistory hd
      (leaf hidden e) hb hbL v' hbad'
    rw [hinv e v' g hd hbad']
    simp only [hd, hd', decide_true, RandomOracleTrap.indicator_true, one_mul]
    refine mul_le_mul' le_rfl (le_of_eq (Finset.prod_congr rfl fun e' he' => ?_))
    have hne : e' ≠ e := fun h => he (h ▸ he')
    have hother := other_leaf_exchanged S.layout hin hl (tau * 2 ^ kappa) hL g S.variant salt root w₀.cipherHistory hd
      (leaf hidden e) hb hbL v' hbad' hleaf.1 (leaf hidden e') (by have := leaf_bounds hidden e'; omega)
      (leaf_bounds hidden e').2 (leaf_ne hidden e' e hne)
    unfold fiberInd OnFiber
    rw [hother.1, hother.2]
  · simp only [hd, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 in
/-- On the distinct trees, the label test at a leaf is the fiber test. -/
theorem jointWeight_label (q v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (e : Fin tau)
    (g : Family (Bits lambda) (Bits lambda)) :
    jointWeight S salt w₀ root hidden Φ q v T g *
        indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) (q e) (v e) g =
          some (q e, v e))) =
      jointWeight S salt w₀ root hidden Φ q v T g * fiberInd S salt root hidden q v e g := by
  have hleaf := leaf_bounds hidden e
  unfold jointWeight fiberInd
  by_cases hd : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory
  · congr 1
    simp only [label_eq_iff]
    by_cases hf : OnFiber S.layout S.variant salt root (leaf hidden e) (q e) (v e) g
    · have hgood : Good S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) (q e) (v e) g := by
        have h := (goodAll_of_distinct S salt w₀ root g hd (leaf hidden e) (by omega) hleaf.2).1
        rwa [hf.1, hf.2] at h
      simp [hf, hgood]
    · simp [hf]
  · simp [hd, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 in
/-- On the distinct trees, a fiber whose parent key or leaf key is not
fresh, or whose keys coincide, is empty. -/
theorem fiberInd_eq_zero_of_not_fresh (q v : Fin tau → Bits lambda) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda))
    (hd : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory)
    (hnot : ¬ ((∀ x ∈ w₀.cipherHistory, x.key ≠ S.layout.key (q e)) ∧
      (∀ x ∈ w₀.cipherHistory, x.key ≠ S.layout.key (S.layout.output (v e))) ∧
      S.layout.key (q e) ≠ S.layout.key (S.layout.output (v e)))) :
    fiberInd S salt root hidden q v e g = 0 := by
  have hleaf := leaf_bounds hidden e
  unfold fiberInd
  by_cases hf : OnFiber S.layout S.variant salt root (leaf hidden e) (q e) (v e) g
  · exfalso
    apply hnot
    have hb' : node (treeExpand S.layout g S.variant salt) root (leaf hidden e) = S.layout.output (v e) := by
      rw [node_eq_output_nodeBlock S.layout g S.variant salt root _ (by omega), hf.2]
    refine ⟨fun x hx h => ?_, fun x hx h => ?_, ?_⟩
    · exact hd.1 (leaf hidden e / 2) (by omega) (by omega) (by rw [hf.1]; exact mem_keysOf.mpr ⟨x, hx, h⟩)
    · exact hd.1 (leaf hidden e) (by omega) hleaf.2 (by rw [hb']; exact mem_keysOf.mpr ⟨x, hx, h⟩)
    · rw [← hf.1, ← hb']
      exact hd.2 (leaf hidden e / 2) (leaf hidden e) (by omega) (by omega) (by omega) hleaf.2 (by omega)
  · simp [hf, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 hin hl hL hΦ hinv in
/-- One more execution fixed: the mass is divided by the number of blocks
less the bad targets. -/
theorem jointWeight_step (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
    (q v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (e : Fin tau) (he : e ∉ T) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (jointWeight S salt w₀ root hidden Φ q v (insert e T)) ≤
      mean (posterior w₀.cipherHistory) (jointWeight S salt w₀ root hidden Φ q v T) := by
  have hleaf := leaf_bounds hidden e
  have hb : 1 < leaf hidden e := by omega
  by_cases hfresh : (∀ x ∈ w₀.cipherHistory, x.key ≠ S.layout.key (q e)) ∧
      (∀ x ∈ w₀.cipherHistory, x.key ≠ S.layout.key (S.layout.output (v e))) ∧
      S.layout.key (q e) ≠ S.layout.key (S.layout.output (v e))
  · have h := posterior_node_bound S.layout hin hl (tau * 2 ^ kappa) hL S.variant salt root (leaf hidden e) hb hleaf.2
      (q e) (v e) w₀.cipherHistory hpos hfresh.1 hfresh.2.1 hfresh.2.2 (jointWeight S salt w₀ root hidden Φ q v T)
      (jointWeight_le_one S salt w₀ root hidden Φ hΦ q v T)
      (fun v' g hg _ hbad => jointWeight_exchanged S salt w₀ root hidden Φ hL2 hin hl hL hinv q v T e he v' g hg hbad) c hfiber
    refine le_trans (le_of_eq ?_) h
    congr 1
    refine congrArg _ (funext fun g => ?_)
    rw [jointWeight_insert S salt w₀ root hidden Φ q v T e he, jointWeight_label S salt w₀ root hidden Φ hL2]
  · refine le_trans (le_of_eq ?_) (zero_le _)
    refine mul_eq_zero_of_right _ ((mean_le_const _ _ 0 fun g _ => ?_).antisymm (zero_le _))
    rw [jointWeight_insert S salt w₀ root hidden Φ q v T e he]
    unfold jointWeight
    by_cases hd : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory
    · rw [fiberInd_eq_zero_of_not_fresh S salt w₀ root hidden hL2 q v e g hd hfresh, mul_zero]
    · simp [hd, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 hin hl hL hΦ hinv in
/-- The joint bound: the mass with a set of executions' hidden leaves on
their fibers is at most the total over the number of blocks less the bad
targets, raised to the set's size. -/
theorem jointWeight_bound (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
    (q v : Fin tau → Bits lambda) (T : Finset (Fin tau)) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ T.card *
        mean (posterior w₀.cipherHistory) (jointWeight S salt w₀ root hidden Φ q v T) ≤
      mean (posterior w₀.cipherHistory) (jointWeight S salt w₀ root hidden Φ q v ∅) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert e T he ih =>
    rw [Finset.card_insert_of_notMem he, pow_succ, mul_assoc]
    exact le_trans (mul_le_mul' le_rfl
      (jointWeight_step S salt w₀ root hidden Φ hL2 hin hl hL hΦ hinv hpos c hfiber q v T e he)) ih

end
end SDitH.Proofs.LeafJointBound
