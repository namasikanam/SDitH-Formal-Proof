import SDitH.Proofs.LeafJointBound

/-! The joint one-sided uniformity of the hidden leaves' blocks, with the
parent seeds summed out. The mass of the families on which a set of
executions' hidden leaves have given blocks, on the distinct trees, is at
most the total mass over the number of blocks less the bad targets, raised
to the set's size: each step fixes one more block by summing the posterior
bound over the leaf's parent seed, the weight with the parent seed fixed
being invariant since the exchange keeps the parent. -/

namespace SDitH.Proofs.LeafBlockBound

open Spec.BAVC Spec.DomainSeparation Spec.SeedTree Spec.SeedPrimitives Spec.SharedScheme Spec.SharedSigner
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries TreeExchange NodeExchange PosteriorNodeBound HonestNodeBound NodeTouchBound TreeDistinct
open TreeStepFresh LeafExchangeDistinct LeafJointBound CipherResample ChargeExpect
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (w₀ : World lambda s wit rnd)
  (root : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa)) (Φ : Family (Bits lambda) (Bits lambda) → ℝ≥0∞)

/-- The block indicator of an execution's hidden leaf. -/
def blockInd (v : Fin tau → Bits lambda) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (nodeBlock S.layout g S.variant salt root (leaf hidden e) = v e))

/-- The parent indicator of an execution's hidden leaf. -/
def parentInd (e : Fin tau) (q : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2) = q))

/-- The block weight: the function on the distinct trees with a set of
executions' hidden leaves at their blocks. -/
def blockWeight (v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory)) * Φ g *
    ∏ e ∈ T, blockInd S salt root hidden v e g

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem blockInd_le_one (v : Fin tau → Bits lambda) (e : Fin tau) (g : Family (Bits lambda) (Bits lambda)) :
    blockInd S salt root hidden v e g ≤ 1 := by
  unfold blockInd
  by_cases h : nodeBlock S.layout g S.variant salt root (leaf hidden e) = v e <;> simp [h, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem parentInd_le_one (e : Fin tau) (q : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) :
    parentInd S salt root hidden e q g ≤ 1 := by
  unfold parentInd
  by_cases h : node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2) = q <;> simp [h, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem blockWeight_le_one (hΦ : ∀ g, Φ g ≤ 1) (v : Fin tau → Bits lambda) (T : Finset (Fin tau))
    (g : Family (Bits lambda) (Bits lambda)) : blockWeight S salt w₀ root hidden Φ v T g ≤ 1 := by
  unfold blockWeight
  calc _ ≤ 1 * 1 * 1 := mul_le_mul' (mul_le_mul'
        (by by_cases h : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory <;> simp [h, indicator])
        (hΦ g)) (Finset.prod_le_one (fun e _ => zero_le _) fun e _ => blockInd_le_one S salt root hidden v e g)
    _ = 1 := by ring

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem blockWeight_insert (v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (e : Fin tau) (he : e ∉ T)
    (g : Family (Bits lambda) (Bits lambda)) :
    blockWeight S salt w₀ root hidden Φ v (insert e T) g =
      blockWeight S salt w₀ root hidden Φ v T g * blockInd S salt root hidden v e g := by
  unfold blockWeight
  rw [Finset.prod_insert he]
  ring

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The parent indicators sum to one. -/
theorem sum_parentInd (e : Fin tau) (g : Family (Bits lambda) (Bits lambda)) :
    ∑ q : Bits lambda, parentInd S salt root hidden e q g = 1 := by
  unfold parentInd indicator
  simp only [decide_eq_true_eq]
  rw [Finset.sum_ite_eq]
  simp

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The parent and block indicators at a fiber are the fiber indicator. -/
theorem parentInd_mul_blockInd (v : Fin tau → Bits lambda) (e : Fin tau) (q : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) :
    parentInd S salt root hidden e q g * blockInd S salt root hidden v e g =
      indicator (decide (OnFiber S.layout S.variant salt root (leaf hidden e) q (v e) g)) := by
  unfold parentInd blockInd OnFiber
  by_cases h1 : node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2) = q <;>
    by_cases h2 : nodeBlock S.layout g S.variant salt root (leaf hidden e) = v e <;> simp [h1, h2, indicator]

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
/-- The block weight with the leaf's parent fixed does not decrease under
the exchange at that leaf, on the good fiber. -/
theorem blockWeight_parent_exchanged (v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (e : Fin tau) (he : e ∉ T)
    (q : Bits lambda) (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hg : OnFiber S.layout S.variant salt root (leaf hidden e) q (v e) g)
    (hbad : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) q w₀.cipherHistory v' g) :
    blockWeight S salt w₀ root hidden Φ v T g * parentInd S salt root hidden e q g ≤
      blockWeight S salt w₀ root hidden Φ v T (exchanged S.layout g S.variant salt root (leaf hidden e) v') *
        parentInd S salt root hidden e q (exchanged S.layout g S.variant salt root (leaf hidden e) v') := by
  have hleaf := leaf_bounds hidden e
  have hb : 1 < leaf hidden e := by omega
  have hbL : leaf hidden e < 2 * (tau * 2 ^ kappa) := hleaf.2
  unfold blockWeight
  by_cases hd : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory
  · have hbad' : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e)
        (node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2)) w₀.cipherHistory v' g := by
      rw [hg.1]; exact hbad
    have hd' := distinct_exchanged S.layout hin hl (tau * 2 ^ kappa) hL g S.variant salt root w₀.cipherHistory hd
      (leaf hidden e) hb hbL v' hbad'
    obtain ⟨hp, hp', G1, G2, G3, G4⟩ :=
      conditions_of_distinct S.layout (tau * 2 ^ kappa) g S.variant salt root w₀.cipherHistory hd (leaf hidden e) hb hbL v' hbad'
    have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL g S.variant salt root (leaf hidden e) hb hbL v' hp hp'
      G1 G2 G3 G4
    have hhalf : node (treeExpand S.layout (exchanged S.layout g S.variant salt root (leaf hidden e) v') S.variant salt) root
        (leaf hidden e / 2) = node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2) := by
      rw [hnode (leaf hidden e / 2) (by omega), if_neg (by omega)]
    rw [hinv e v' g hd hbad']
    simp only [hd, hd', decide_true, RandomOracleTrap.indicator_true, one_mul]
    unfold parentInd
    rw [hhalf]
    refine mul_le_mul' (mul_le_mul' le_rfl (le_of_eq (Finset.prod_congr rfl fun e' he' => ?_))) le_rfl
    have hne : e' ≠ e := fun h => he (h ▸ he')
    have hother := other_leaf_exchanged S.layout hin hl (tau * 2 ^ kappa) hL g S.variant salt root w₀.cipherHistory hd
      (leaf hidden e) hb hbL v' hbad' hleaf.1 (leaf hidden e') (by have := leaf_bounds hidden e'; omega)
      (leaf_bounds hidden e').2 (leaf_ne hidden e' e hne)
    unfold blockInd
    rw [hother.2]
  · simp only [hd, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 in
/-- On the distinct trees, the label test at a leaf with the parent fixed
is the fiber test. -/
theorem blockWeight_label (v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (e : Fin tau) (q : Bits lambda)
    (g : Family (Bits lambda) (Bits lambda)) :
    blockWeight S salt w₀ root hidden Φ v T g * parentInd S salt root hidden e q g *
        indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) q (v e) g = some (q, v e))) =
      blockWeight S salt w₀ root hidden Φ v T g * (parentInd S salt root hidden e q g * blockInd S salt root hidden v e g) := by
  have hleaf := leaf_bounds hidden e
  rw [parentInd_mul_blockInd, mul_assoc]
  by_cases hd : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory
  · by_cases hf : OnFiber S.layout S.variant salt root (leaf hidden e) q (v e) g
    · have hgood : Good S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) q (v e) g := by
        have h := (goodAll_of_distinct S salt w₀ root g hd (leaf hidden e) (by omega) hleaf.2).1
        rwa [hf.1, hf.2] at h
      have hlab : decide (label S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) q (v e) g = some (q, v e)) =
          true :=
        decide_eq_true ((label_eq_iff S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) q (v e) g).mpr ⟨hgood, hf⟩)
      have hpar : parentInd S salt root hidden e q g = 1 := by
        unfold parentInd
        simp [hf.1, indicator]
      rw [hlab, hpar]
      simp [hf, indicator]
    · have hlab : decide (label S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) q (v e) g = some (q, v e)) =
          false :=
        decide_eq_false fun h =>
          hf ((label_eq_iff S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) q (v e) g).mp h).2
      rw [hlab]
      simp [hf, indicator]
  · unfold blockWeight
    simp [hd, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 hin hl hL hΦ hinv in
/-- One more block fixed: the mass is divided by the number of blocks less
the bad targets. -/
theorem blockWeight_step (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
    (v : Fin tau → Bits lambda) (T : Finset (Fin tau)) (e : Fin tau) (he : e ∉ T) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden Φ v (insert e T)) ≤
      mean (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden Φ v T) := by
  have hleaf := leaf_bounds hidden e
  have hb : 1 < leaf hidden e := by omega
  set N : ℝ≥0∞ := ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞)
    with hN
  -- the mass with the block fixed is the sum over the parent seeds of the fiber masses
  have hsplit : mean (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden Φ v (insert e T)) =
      ∑ q : Bits lambda, mean (posterior w₀.cipherHistory) (fun g =>
        blockWeight S salt w₀ root hidden Φ v T g * parentInd S salt root hidden e q g *
          indicator (decide (label S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e) q (v e) g = some (q, v e)))) := by
    simp only [blockWeight_label S salt w₀ root hidden Φ hL2]
    rw [sum_mean_mul (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden Φ v T)
      (fun q g => parentInd S salt root hidden e q g * blockInd S salt root hidden v e g) Finset.univ]
    refine congrArg _ (funext fun g => ?_)
    rw [blockWeight_insert S salt w₀ root hidden Φ v T e he, ← Finset.sum_mul, sum_parentInd, one_mul]
  have hjoin : ∑ q : Bits lambda, mean (posterior w₀.cipherHistory) (fun g =>
      blockWeight S salt w₀ root hidden Φ v T g * parentInd S salt root hidden e q g) =
      mean (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden Φ v T) := by
    rw [sum_mean_mul (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden Φ v T)
      (fun q g => parentInd S salt root hidden e q g) Finset.univ]
    refine congrArg _ (funext fun g => ?_)
    rw [sum_parentInd, mul_one]
  rw [hsplit, Finset.mul_sum, ← hjoin]
  refine Finset.sum_le_sum fun q _ => ?_
  by_cases hfresh : (∀ x ∈ w₀.cipherHistory, x.key ≠ S.layout.key q) ∧
      (∀ x ∈ w₀.cipherHistory, x.key ≠ S.layout.key (S.layout.output (v e))) ∧
      S.layout.key q ≠ S.layout.key (S.layout.output (v e))
  · exact posterior_node_bound S.layout hin hl (tau * 2 ^ kappa) hL S.variant salt root (leaf hidden e) hb hleaf.2
      q (v e) w₀.cipherHistory hpos hfresh.1 hfresh.2.1 hfresh.2.2
      (fun g => blockWeight S salt w₀ root hidden Φ v T g * parentInd S salt root hidden e q g)
      (fun g => (mul_le_mul' (blockWeight_le_one S salt w₀ root hidden Φ hΦ v T g) (parentInd_le_one S salt root hidden e q g)).trans
        (by simp))
      (fun v' g hg _ hbad => blockWeight_parent_exchanged S salt w₀ root hidden Φ hL2 hin hl hL hinv v T e he q v' g hg hbad)
      c hfiber
  · refine le_trans (le_of_eq ?_) (zero_le _)
    refine mul_eq_zero_of_right _ ((mean_le_const _ _ 0 fun g _ => ?_).antisymm (zero_le _))
    rw [blockWeight_label S salt w₀ root hidden Φ hL2, parentInd_mul_blockInd]
    unfold blockWeight
    by_cases hd : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory
    · have h0 := fiberInd_eq_zero_of_not_fresh S salt w₀ root hidden hL2 (fun _ => q) v e g hd hfresh
      unfold fiberInd at h0
      rw [h0, mul_zero]
    · simp [hd, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 hin hl hL hΦ hinv in
/-- The joint block bound: the mass with a set of executions' hidden leaves
at given blocks is at most the total over the number of blocks less the bad
targets, raised to the set's size. -/
theorem blockWeight_bound (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
    (v : Fin tau → Bits lambda) (T : Finset (Fin tau)) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ T.card *
        mean (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden Φ v T) ≤
      mean (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden Φ v ∅) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert e T he ih =>
    rw [Finset.card_insert_of_notMem he, pow_succ, mul_assoc]
    exact le_trans (mul_le_mul' le_rfl
      (blockWeight_step S salt w₀ root hidden Φ hL2 hin hl hL hΦ hinv hpos c hfiber v T e he)) ih

end
end SDitH.Proofs.LeafBlockBound
