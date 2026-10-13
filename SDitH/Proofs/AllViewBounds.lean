import SDitH.Proofs.ViewNodeBound
import SDitH.Proofs.ViewRootBound
import SDitH.Proofs.OwnViewExchangeAll

/-! The touching bounds for the view pruned at the hidden keys of all
executions. The view is the commitment run followed by the
post-processing, pruned at the hidden keys of all executions for a fixed
hidden tuple; it is the same under the exchange of a node on some
execution's hidden path and under the root exchange, so the abstract node
and root bounds apply. -/

namespace SDitH.Proofs.AllViewBounds

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys NodeExchange TreeExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange OwnViewExchangeAll PosteriorNodeBound HonestNodeBound NodeTouchBound ViewNodeBound
open RootExchange RootPosteriorBound RootHonestBound RootTouchBound ViewRootBound HiddenTuple
open CipherResample ChargeExpect ChargeCutExpect TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w₀ : World lambda s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa)) {Sig β : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)

/-- The view pruned at the hidden keys of all executions, from a root and
a family. -/
def viewAll (root : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) : PMF (Sig × World lambda s wit rnd) :=
  ownView S salt witness root post (hiddenKeysAll S.layout g S.variant salt root hidden) { w₀ with family := g }

/-- The view is the same under the exchange of a node on some execution's
hidden path, on the good fiber. -/
theorem viewAll_exchanged (root : Bits lambda) (b : Nat) (hb : 1 < b) (hbk : b ≤ tau * 2 ^ kappa - 1)
    (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (e : Fin tau) (hpath : b ∈ pathAddresses (leafAddress e (hidden e)))
    (hpost : ∀ c, ∀ x, post (.done (setTree b x c)) = post (.done c))
    (q v v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) (hg : OnFiber S.layout S.variant salt root b q v g)
    (hgood : Good S.layout (tau * 2 ^ kappa) S.variant salt root b q v g)
    (hbad : ¬ Bad S.layout (tau * 2 ^ kappa) S.variant salt root b q w₀.cipherHistory v' g) (hfr : Fresh S salt w₀ root b g) :
    viewAll S salt witness w₀ hidden post root (exchanged S.layout g S.variant salt root b v') =
      viewAll S salt witness w₀ hidden post root g := by
  have hparent : parentKey S.layout g S.variant salt root b = S.layout.key q := by
    unfold parentKey
    rw [hg.1]
  have hb' : node (treeExpand S.layout g S.variant salt) root b =
      S.layout.output (nodeBlock S.layout g S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout g S.variant salt root b hb
  have hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v) := fun e he h =>
    hfr.2.1 (by rw [hb', hg.2]; exact mem_keysOf.mpr ⟨e, he, h⟩)
  have hpκ : S.layout.key q ≠ S.layout.key (S.layout.output v) := by
    rw [← hparent, ← hg.2, ← hb']
    exact hfr.2.2
  simp only [Bad, not_or, not_exists, not_and] at hbad
  obtain ⟨hbH, hbp, hb3, hb4⟩ := hbad
  have hfκ' : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key (S.layout.output v') := fun e he h =>
    hbH (by rw [← h]; exact mem_keysOf.mpr ⟨e, he, rfl⟩)
  have hview := ownView_exchanged_all S salt witness { w₀ with family := g } root hidden b hb hbk v' hin hl hL
    (by rw [hparent, hg.2]; exact hpκ) (by rw [hparent]; exact fun h => hbp h.symm)
    (fun c h1 hc hcb => by rw [hparent]; exact hgood.1 c h1 hc hcb)
    (fun c h1 hc hcb => by rw [hg.2]; exact hgood.2 c h1 hc hcb)
    (fun c _ hc => hb3 c hc)
    (fun c hc hsib hcb => by rw [hparent]; exact hb4 c hc hsib hcb)
    (fun e he => by rw [hg.2]; exact hfκ e he) hfκ' e hpath post (fun c => hpost c _)
  simp only at hview
  unfold viewAll
  exact hview

/-- The view is the same under the root exchange, on the good fiber. -/
theorem viewAll_root_exchanged (hL2 : 2 ≤ tau * 2 ^ kappa) (e : Fin tau)
    (hpost : ∀ c, ∀ x, post (.done (setTree 1 x c)) = post (.done c))
    (root root' : Bits lambda) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) (hx : x.1 = root)
    (hgood : GoodR S.layout (tau * 2 ^ kappa) S.variant salt x)
    (hbad : ¬ BadR S.layout (tau * 2 ^ kappa) S.variant salt w₀.cipherHistory root' x) (hfr : FreshR S w₀ x) :
    viewAll S salt witness w₀ hidden post root' (rootExchanged S.layout x.2 root root') =
      viewAll S salt witness w₀ hidden post root x.2 := by
  obtain ⟨r, g⟩ := x
  simp only at hx
  subst hx
  simp only [BadR, not_or, not_exists, not_and] at hbad
  obtain ⟨hbH, hb2⟩ := hbad
  have hfκ : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key r := fun e he h => hfr (mem_keysOf.mpr ⟨e, he, h⟩)
  have hfκ' : ∀ e ∈ w₀.cipherHistory, e.key ≠ S.layout.key root' := fun e he h =>
    hbH (by rw [← h]; exact mem_keysOf.mpr ⟨e, he, rfl⟩)
  have hview := ownView_root_exchanged_all S salt witness { w₀ with family := g } r hidden root' hL2
    (fun c h2 hc => hgood c h2 hc) (fun c _ hc => hb2 c hc) hfκ hfκ' e post (fun c => hpost c _)
  simp only at hview
  unfold viewAll
  exact hview

variable (cont : Sig × World lambda s wit rnd → PMF β) (new : β → List (Entry (Bits lambda) (Bits lambda)))

/-- The touching bound at a node on some execution's hidden path, for the
view pruned at the hidden keys of all executions. -/
theorem node_touch_bound_all (root : Bits lambda) (b : Nat) (hb : 1 < b) (hbk : b ≤ tau * 2 ^ kappa - 1)
    (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (e : Fin tau) (hpath : b ∈ pathAddresses (leafAddress e (hidden e)))
    (hpost : ∀ c, ∀ x, post (.done (setTree b x c)) = post (.done c))
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior w₀.cipherHistory) (fun g => indicator (decide (GoodAll S salt w₀ root b g)) *
          HitV S salt root (viewAll S salt witness w₀ hidden post root) b cont new g) ≤
      (c : ℝ≥0∞) * mean (posterior w₀.cipherHistory) (expectedNewV (viewAll S salt witness w₀ hidden post root) cont new) := by
  have hpos' : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  exact node_touch_boundV S salt w₀ root (viewAll S salt witness w₀ hidden post root) b hb (by omega) hin hl hL
    (fun q v v' g hg hgood hbad hfr =>
      viewAll_exchanged S salt witness w₀ hidden post root b hb hbk hin hl hL e hpath hpost q v v' g hg hgood hbad hfr)
    cont new hpos c hfiber

/-- The touching bound at the root, for the view pruned at the hidden keys
of all executions. -/
theorem root_touch_bound_all (hL2 : 2 ≤ tau * 2 ^ kappa) (e : Fin tau)
    (hpost : ∀ c, ∀ x, post (.done (setTree 1 x c)) = post (.done c))
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (c : Nat)
    (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodAllR S salt w₀ x)) *
          HitVR S (viewAll S salt witness w₀ hidden post) cont new x) ≤
      (c : ℝ≥0∞) * mean (rootDraw w₀.cipherHistory) (expectedNewVR (viewAll S salt witness w₀ hidden post) cont new) :=
  root_touch_boundVR S salt w₀ (viewAll S salt witness w₀ hidden post)
    (fun root root' x hx hgood hbad hfr => viewAll_root_exchanged S salt witness w₀ hidden post hL2 e hpost root root' x hx hgood hbad hfr)
    cont new hpos c hfiberR

end
end SDitH.Proofs.AllViewBounds
