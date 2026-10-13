import SDitH.Proofs.LeafMixture

/-! The uniform-mixture lower bound relative to a bound function. For a
family of functions bounded by a second family, both invariant under the
exchanges, the sum of the masses over the tuples plus the bound's mass at
the own blocks times the power is at most the sum of the bound's masses
over the tuples plus the function's mass at the own blocks times the
power. With the bound the tuple's probability, whose values sum to at
most one over the tuples, the slack of the comparison stays independent
of the number of tuples. -/

namespace SDitH.Proofs.LeafMixtureGen

open Spec.BAVC Spec.DomainSeparation Spec.SeedTree Spec.SeedPrimitives Spec.SharedScheme Spec.SharedSigner
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries TreeExchange NodeExchange PosteriorNodeBound HonestNodeBound NodeTouchBound TreeDistinct
open TreeStepFresh LeafExchangeDistinct LeafJointBound LeafBlockBound LeafMixture CipherResample ChargeExpect
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (w₀ : World lambda s wit rnd)
  (root : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- A weight times the difference to a bound plus the weight times the
function is the weight times the bound. -/
theorem mean_sub_add (p : PMF (Family (Bits lambda) (Bits lambda))) (w f b : Family (Bits lambda) (Bits lambda) → ℝ≥0∞)
    (hf : ∀ g, f g ≤ b g) :
    mean p (fun g => w g * (b g - f g)) + mean p (fun g => w g * f g) = mean p (fun g => w g * b g) := by
  rw [← mean_add]
  refine congrArg _ (funext fun g => ?_)
  rw [← mul_add, tsub_add_cancel_of_le (hf g)]

variable (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
  (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
  (Fct Bnd : (Fin tau → Bits lambda) → Family (Bits lambda) (Bits lambda) → ℝ≥0∞)
  (hFB : ∀ v g, Fct v g ≤ Bnd v g) (hB : ∀ v g, Bnd v g ≤ 1)
  (hinvF : ∀ (v : Fin tau → Bits lambda) (e : Fin tau) (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)),
    Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory →
    ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e)
      (node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2)) w₀.cipherHistory v' g →
    Fct v (exchanged S.layout g S.variant salt root (leaf hidden e) v') = Fct v g)
  (hinvB : ∀ (v : Fin tau → Bits lambda) (e : Fin tau) (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)),
    Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory →
    ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root (leaf hidden e)
      (node (treeExpand S.layout g S.variant salt) root (leaf hidden e / 2)) w₀.cipherHistory v' g →
    Bnd v (exchanged S.layout g S.variant salt root (leaf hidden e) v') = Bnd v g)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 hin hl hL hpos hfiber hFB hB hinvF hinvB in
/-- The lower mixture bound relative to the bound function. -/
theorem mixture_lower_gen :
    (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g)) +
        ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
          mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Bnd (blocks S salt root hidden g) g) ≤
      (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Bnd v g)) +
        ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
          mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct (blocks S salt root hidden g) g) := by
  set N' : ℝ≥0∞ :=
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) with hN'
  have hupper := mixture_upper S salt w₀ root hidden hL2 hin hl hL hpos c hfiber (fun v g => Bnd v g - Fct v g)
    (fun v g => tsub_le_self.trans (hB v g)) (fun v e v' g hd hbad => by simp only [hinvF v e v' g hd hbad, hinvB v e v' g hd hbad])
  simp only at hupper
  have hown := mean_sub_add (posterior w₀.cipherHistory) (distInd S salt w₀ root) (fun g => Fct (blocks S salt root hidden g) g)
    (fun g => Bnd (blocks S salt root hidden g) g) (fun g => hFB _ g)
  have hsum : (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * (Bnd v g - Fct v g))) +
      ∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g) =
      ∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Bnd v g) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ =>
      mean_sub_add (posterior w₀.cipherHistory) (distInd S salt w₀ root) (fun g => Fct v g) (fun g => Bnd v g) (fun g => hFB v g)
  calc (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g)) +
        N' ^ tau * mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Bnd (blocks S salt root hidden g) g)
      = (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g)) +
        (N' ^ tau * mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g *
            (Bnd (blocks S salt root hidden g) g - Fct (blocks S salt root hidden g) g)) +
          N' ^ tau * mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct (blocks S salt root hidden g) g)) := by
        rw [← mul_add, hown]
    _ ≤ (∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct v g)) +
        ((∑ v : Fin tau → Bits lambda, mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * (Bnd v g - Fct v g))) +
          N' ^ tau * mean (posterior w₀.cipherHistory) (fun g => distInd S salt w₀ root g * Fct (blocks S salt root hidden g) g)) :=
        add_le_add le_rfl (add_le_add hupper le_rfl)
    _ = _ := by
        rw [← add_assoc, add_comm (∑ v : Fin tau → Bits lambda, _) (∑ v : Fin tau → Bits lambda, _), hsum]

end
end SDitH.Proofs.LeafMixtureGen
