import SDitH.Proofs.LeafBlockBound

/-! The uniform-mixture comparison. For a family of bounded functions of
the families indexed by the hidden blocks' tuple, each invariant under
the exchanges, the mass of the function at the family's own hidden blocks
is at most the sum over the tuples of the function at that tuple, divided
by the number of blocks less the bad targets to the number of executions;
and conversely that sum is at most the mass at the own blocks times the
same power plus the mass of the distinct trees times the difference of
the powers. Together they compare the two signings' masses through their
uniform mixtures over the hidden blocks. -/

namespace SDitH.Proofs.LeafMixture

open Spec.BAVC Spec.DomainSeparation Spec.SeedTree Spec.SeedPrimitives Spec.SharedScheme Spec.SharedSigner
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries TreeExchange NodeExchange PosteriorNodeBound HonestNodeBound NodeTouchBound TreeDistinct
open TreeStepFresh LeafExchangeDistinct LeafJointBound LeafBlockBound CipherResample ChargeExpect
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (w₀ : World lambda s wit rnd)
  (root : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa))

/-- The hidden blocks of a family. -/
def blocks (g : Family (Bits lambda) (Bits lambda)) : Fin tau → Bits lambda :=
  fun e => nodeBlock S.layout g S.variant salt root (leaf hidden e)

/-- The distinct-tree indicator. -/
def distInd (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem distInd_le_one (g : Family (Bits lambda) (Bits lambda)) : distInd S salt w₀ root g ≤ 1 := by
  unfold distInd
  by_cases h : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory <;> simp [h, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The block indicators of all executions select the family's own blocks. -/
theorem prod_blockInd (v : Fin tau → Bits lambda) (g : Family (Bits lambda) (Bits lambda)) :
    ∏ e : Fin tau, blockInd S salt root hidden v e g = if v = blocks S salt root hidden g then 1 else 0 := by
  by_cases h : v = blocks S salt root hidden g
  · rw [if_pos h]
    refine Finset.prod_eq_one fun e _ => ?_
    unfold blockInd
    rw [h]
    simp [blocks, indicator]
  · rw [if_neg h]
    have : ∃ e, nodeBlock S.layout g S.variant salt root (leaf hidden e) ≠ v e := by
      by_contra hall
      push_neg at hall
      exact h (funext fun e => (hall e).symm)
    obtain ⟨e, he⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ e) ?_
    unfold blockInd
    simp [he, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The block weights over all executions sum to the function at the
family's own blocks. -/
theorem sum_blockWeight (Fct : (Fin tau → Bits lambda) → Family (Bits lambda) (Bits lambda) → ℝ≥0∞)
    (g : Family (Bits lambda) (Bits lambda)) :
    ∑ v : Fin tau → Bits lambda, blockWeight S salt w₀ root hidden (Fct v) v Finset.univ g =
      distInd S salt w₀ root g * Fct (blocks S salt root hidden g) g := by
  unfold blockWeight distInd
  simp only [prod_blockInd, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

variable (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
  (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
  (Fct : (Fin tau → Bits lambda) → Family (Bits lambda) (Bits lambda) → ℝ≥0∞)
  (hF : ∀ v g, Fct v g ≤ 1)
  (hinv : ∀ (v : Fin tau → Bits lambda) (e : Fin tau) (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)),
    Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory →
    ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e)
      (node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2)) w₀.cipherHistory v' g →
    Fct v (exchanged S.layout g S.variant salt root (leaf hidden e) v') = Fct v g)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 hin hl hL hpos hfiber hF hinv in
/-- The upper mixture bound: the mass at the own blocks, times the number
of blocks less the bad targets to the number of executions, is at most the
sum of the masses over the tuples. -/
theorem mixture_upper :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct (blocks S salt root hidden g) g) ≤
      ∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g) := by
  have hcard : (Finset.univ : Finset (Fin tau)).card = tau := Finset.card_fin tau
  calc _ = ∑ v : Fin tau → Bits lambda,
        ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^
          (Finset.univ : Finset (Fin tau)).card *
          mean (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden (Fct v) v Finset.univ) := by
        rw [← Finset.mul_sum, sum_mean (posterior w₀.cipherHistory) (fun v g => blockWeight S salt w₀ root hidden (Fct v) v Finset.univ g)
          Finset.univ, hcard]
        refine congrArg _ (congrArg _ (funext fun g => ?_))
        exact (sum_blockWeight S salt w₀ root hidden Fct g).symm
    _ ≤ ∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (blockWeight S salt w₀ root hidden (Fct v) v ∅) :=
        Finset.sum_le_sum fun v _ => blockWeight_bound S salt w₀ root hidden (Fct v) hL2 hin hl hL (hF v)
          (fun e v' g hd hbad => hinv v e v' g hd hbad) hpos c hfiber v Finset.univ
    _ = _ := by
        refine Finset.sum_congr rfl fun v _ => congrArg _ (funext fun g => ?_)
        simp [blockWeight, distInd]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- A weight times the complement of a bounded function plus the weight
times the function is the weight. -/
theorem mean_compl_add (p : PMF (Family (Bits lambda) (Bits lambda))) (w f : Family (Bits lambda) (Bits lambda) → ℝ≥0∞)
    (hf : ∀ g, f g ≤ 1) :
    mean p (fun g => w g * (1 - f g)) + mean p (fun g => w g * f g) = mean p w := by
  rw [← mean_add]
  refine congrArg _ (funext fun g => ?_)
  rw [← mul_add, tsub_add_cancel_of_le (hf g), mul_one]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 hin hl hL hpos hfiber hF hinv in
/-- The lower mixture bound: the sum of the masses over the tuples plus the
distinct mass times the power is at most the distinct mass times the
number of tuples plus the mass at the own blocks times the power. -/
theorem mixture_lower :
    (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g)) +
        ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
          mean (posterior w₀.cipherHistory) (distInd S salt w₀ root) ≤
      (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * mean (posterior w₀.cipherHistory) (distInd S salt w₀ root) +
        ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
          mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct (blocks S salt root hidden g) g) := by
  set N' : ℝ≥0∞ :=
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) with hN'
  -- the complement family
  have hupper := mixture_upper S salt w₀ root hidden hL2 hin hl hL hpos c hfiber (fun v g => 1 - Fct v g)
    (fun v g => tsub_le_self) (fun v e v' g hd hbad => by simp only [hinv v e v' g hd hbad])
  simp only at hupper
  have hown := mean_compl_add (posterior w₀.cipherHistory) (distInd S salt w₀ root) (fun g => Fct (blocks S salt root hidden g) g)
    (fun g => hF _ g)
  have hsum : (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * (1 - Fct v g))) +
      ∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g) =
      (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * mean (posterior w₀.cipherHistory) (distInd S salt w₀ root) := by
    rw [← Finset.sum_add_distrib]
    simp only [mean_compl_add (posterior w₀.cipherHistory) (distInd S salt w₀ root) (fun g => Fct _ g) (fun g => hF _ g)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- assemble: Σ a + N'^τ b = Σ a + N'^τ u + N'^τ a' ≤ Σ a + Σ u + N'^τ a' = card b + N'^τ a'
  calc (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g)) +
        N' ^ tau * mean (posterior w₀.cipherHistory) (distInd S salt w₀ root)
      = (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g)) +
        (N' ^ tau * mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * (1 - Fct (blocks S salt root hidden g) g)) +
          N' ^ tau * mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct (blocks S salt root hidden g) g)) := by
        rw [← mul_add, hown]
    _ ≤ (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g)) +
        ((∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * (1 - Fct v g))) +
          N' ^ tau * mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct (blocks S salt root hidden g) g)) :=
        add_le_add le_rfl (add_le_add hupper le_rfl)
    _ = _ := by
        rw [← add_assoc, add_comm (∑ v : Fin tau → Bits lambda, _) (∑ v : Fin tau → Bits lambda, _), hsum]

end
end SDitH.Proofs.LeafMixture
