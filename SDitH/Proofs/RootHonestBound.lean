import SDitH.Proofs.RootPosteriorBound
import SDitH.Proofs.RootOwnView

/-! The posterior bound for the commitment view at the root. The weight is
the mean, under the commitment run from the pair's root followed by a
post-processing that does not read the root, of a bounded function of the
view pruned at the family's own hidden keys, restricted to the pairs whose
root key is fresh. The weight is at most one and does not decrease under
the root exchange on the good fiber, so the posterior bound on the root
applies. -/

namespace SDitH.Proofs.RootHonestBound

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys KeySwap RootExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange RootOwnView RootPosteriorBound CipherResample ChargeExpect TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w₀ : World lambda s wit rnd) {Sig : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
  (w : Sig × World lambda s wit rnd → ℝ≥0∞) (a : Nat)

/-- The freshness of a pair at the root: the root's key is not among the
starting history's keys. -/
def FreshR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : Prop :=
  S.layout.key x.1 ∉ keysOf w₀.cipherHistory

/-- The weight: the mean of the view function under the own-keys view from
the pair's root, restricted to the pairs fresh at the root. -/
def weightR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (decide (FreshR S w₀ x)) *
    mean (ownView S salt witness x.1 post (hiddenKeys S.layout x.2 S.variant salt x.1 a) { w₀ with family := x.2 }) w

theorem weightR_le_one (hw : ∀ y, w y ≤ 1) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    weightR S salt witness w₀ post w a x ≤ 1 := by
  unfold weightR
  calc _ ≤ 1 * 1 := mul_le_mul' (by by_cases h : FreshR S w₀ x <;> simp [h, indicator])
        (mean_le_const _ _ 1 fun y _ => hw y)
    _ = 1 := mul_one _

variable (hL2 : 2 ≤ tau * 2 ^ kappa) (ha : a < 2 * (tau * 2 ^ kappa))
  (hpost : ∀ c, ∀ x, post (.done (setTree 1 x c)) = post (.done c))

include hL2 ha hpost in
/-- The weight does not decrease under the root exchange on the good fiber. -/
theorem weightR_exchanged (root root' : Bits lambda) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) (hx : x.1 = root)
    (hgood : GoodR S.layout (tau * 2 ^ kappa) S.variant salt x)
    (hbad : ¬ BadR S.layout (tau * 2 ^ kappa) S.variant salt w₀.cipherHistory root' x) :
    weightR S salt witness w₀ post w a x ≤
      weightR S salt witness w₀ post w a (root', rootExchanged S.layout x.2 root root') := by
  obtain ⟨r, g⟩ := x
  simp only at hx
  subst hx
  simp only [BadR, not_or, not_exists, not_and] at hbad
  obtain ⟨hbH, hb2⟩ := hbad
  unfold weightR
  by_cases hfr : FreshR S w₀ (r, g)
  · have hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key r := fun e he h => hfr (mem_keysOf.mpr ⟨e, he, h⟩)
    have hfκ' : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key root' := fun e he h =>
      hbH (by rw [← h]; exact mem_keysOf.mpr ⟨e, he, rfl⟩)
    have hfr' : FreshR S w₀ (root', rootExchanged S.layout g r root') := hbH
    have hview := ownView_root_exchanged S salt witness { w₀ with family := g } r root' hL2
      (fun c h2 hc => hgood c h2 hc) (fun c _ hc => hb2 c hc) hfκ hfκ' a ha post (fun c => hpost c _)
    simp only at hview
    show _ ≤ indicator (decide (FreshR S w₀ (root', rootExchanged S.layout g r root'))) *
      mean (ownView S salt witness root' post (hiddenKeys S.layout (rootExchanged S.layout g r root') S.variant salt root' a)
        { w₀ with family := rootExchanged S.layout g r root' }) w
    rw [hview]
    simp only [hfr, hfr', decide_true, RandomOracleTrap.indicator_true, one_mul, le_refl]
  · simp only [hfr, decide_false, RandomOracleTrap.indicator_false, zero_mul]
    exact zero_le _

include hL2 ha hpost in
/-- The posterior bound for the commitment view at the root, at a fixed salt. -/
theorem honest_root_bound (hw : ∀ y, w y ≤ 1)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (root : Bits lambda)
    (hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key root) (c : Nat)
    (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory) (fun x => weightR S salt witness w₀ post w a x *
          indicator (decide (labelR S.layout (tau * 2 ^ kappa) S.variant salt x = some root))) ≤
      mean (rootDraw w₀.cipherHistory) (weightR S salt witness w₀ post w a) :=
  posterior_root_bound S.layout (tau * 2 ^ kappa) S.variant salt w₀.cipherHistory hpos root hfκ _
    (weightR_le_one S salt witness w₀ post w a hw)
    (fun root' x hx hgood hbad => weightR_exchanged S salt witness w₀ post w a hL2 ha hpost root root' x hx hgood hbad)
    c hfiberR

end
end SDitH.Proofs.RootHonestBound
