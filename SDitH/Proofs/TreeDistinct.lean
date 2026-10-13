import SDitH.Proofs.NodeTouchBound

/-! Distinct and fresh tree keys. When every node of the tree has a key
outside the starting history's keys and distinct nodes have distinct keys,
every internal node is good and fresh in the sense of the touching
bound. -/

namespace SDitH.Proofs.TreeDistinct

open Spec.BAVC Spec.DomainSeparation Spec.SeedTree Spec.SharedSigner
open Spec.IdealCipher (Family Entry)
open HiddenLeafNode TreeExchange PosteriorNodeBound HonestNodeBound NodeTouchBound TreeStepFresh
open scoped Classical

noncomputable section

variable {lambda : Nat} (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
  (g : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root : Bits lambda) (L : Nat)
  (H : List (Entry (Bits lambda) (Bits lambda)))

/-- The tree's keys are fresh and distinct on the allocated addresses. -/
def Distinct : Prop :=
  (∀ c, 1 ≤ c → c < 2 * L → layout.key (node (treeExpand layout g variant salt) root c) ∉ keysOf H) ∧
  (∀ c c', 1 ≤ c → c < 2 * L → 1 ≤ c' → c' < 2 * L → c ≠ c' →
    layout.key (node (treeExpand layout g variant salt) root c) ≠ layout.key (node (treeExpand layout g variant salt) root c'))

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (w₀ : Spec.SharedScheme.World lambda s wit rnd)
  (root : Bits lambda)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- Distinct and fresh tree keys make every internal node good and fresh. -/
theorem goodAll_of_distinct (g : Family (Bits lambda) (Bits lambda))
    (hd : Distinct S.layout g S.variant salt root (tau * 2 ^ kappa) w₀.cipherHistory) (b : Nat) (hb : 1 < b)
    (hbL : b < 2 * (tau * 2 ^ kappa)) : GoodAll S salt w₀ root b g := by
  have hb' : node (treeExpand S.layout g S.variant salt) root b =
      S.layout.output (nodeBlock S.layout g S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout g S.variant salt root b hb
  refine ⟨⟨fun c h1 hc hcb => ?_, fun c h1 hc hcb => ?_⟩, ?_, ?_, ?_⟩
  · exact hd.2 c (b / 2) h1 hc (by omega) (by omega) hcb
  · rw [← hb']
    exact hd.2 c b h1 hc (by omega) hbL hcb
  · exact hd.1 (b / 2) (by omega) (by omega)
  · exact hd.1 b (by omega) hbL
  · exact hd.2 (b / 2) b (by omega) (by omega) (by omega) hbL (by omega)

end
end SDitH.Proofs.TreeDistinct
