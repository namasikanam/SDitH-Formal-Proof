import SDitH.Proofs.TreeDistinct

/-! Distinctness and the other leaves' fibers under the exchange of a leaf's
value. When the tree's keys are fresh and distinct and the target block is
not bad, the exchanged tree's keys are fresh and distinct too (the new
leaf's key is fresh and differs from every node's), and every other leaf
keeps its parent seed and its block: its parent is an internal node, so
unchanged, and its block is read at a key the exchange fixes, or, for the
sibling, is moved by neither block of the transposition. -/

namespace SDitH.Proofs.LeafExchangeDistinct

open Spec.BAVC Spec.DomainSeparation Spec.SeedTree Spec.SeedPrimitives
open Spec.IdealCipher (Family Entry)
open HiddenLeafNode TreeExchange NodeExchange PosteriorNodeBound TreeDistinct TreeStepFresh
open scoped Classical

noncomputable section

variable {lambda : Nat} (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
  (hin : Function.Injective layout.input) (hl : 26 ≤ lambda) (L : Nat) (hL : 4 * L ≤ 2 ^ 24)
  (g : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root : Bits lambda)
  (H₀ : List (Entry (Bits lambda) (Bits lambda))) (hd : Distinct layout g variant salt root L H₀)
  (b : Nat) (hb : 1 < b) (hbL : b < 2 * L) (v' : Bits lambda)
  (hbad : ¬ Bad layout L variant salt root b (node (treeExpand layout g variant salt) root (b / 2)) H₀ v' g)

include hd hb hbL hbad in
/-- The exchange's side conditions from distinctness and a target that is
not bad. -/
theorem conditions_of_distinct :
    parentKey layout g variant salt root b ≠ layout.key (layout.output (nodeBlock layout g variant salt root b)) ∧
    parentKey layout g variant salt root b ≠ layout.key (layout.output v') ∧
    (∀ c, 1 ≤ c → c < 2 * L → c ≠ b / 2 →
      layout.key (node (treeExpand layout g variant salt) root c) ≠ parentKey layout g variant salt root b) ∧
    (∀ c, 1 ≤ c → c < 2 * L → c ≠ b →
      layout.key (node (treeExpand layout g variant salt) root c) ≠
        layout.key (layout.output (nodeBlock layout g variant salt root b))) ∧
    (∀ c, 1 ≤ c → c < 2 * L → layout.key (node (treeExpand layout g variant salt) root c) ≠ layout.key (layout.output v')) ∧
    (∀ c, c < 2 * L → c / 2 = b / 2 → c ≠ b →
      g (parentKey layout g variant salt root b) (layout.input (nodeTweak variant salt c)) ≠ v') := by
  have hb' : node (treeExpand layout g variant salt) root b = layout.output (nodeBlock layout g variant salt root b) :=
    node_eq_output_nodeBlock layout g variant salt root b hb
  simp only [Bad, not_or, not_exists, not_and] at hbad
  obtain ⟨-, hbp, hb3, hb4⟩ := hbad
  refine ⟨?_, fun h => hbp h.symm, fun c h1 hc hcb => ?_, fun c h1 hc hcb => ?_, fun c _ hc => hb3 c hc,
    fun c hc hsib hcb => hb4 c hc hsib hcb⟩
  · show layout.key (node (treeExpand layout g variant salt) root (b / 2)) ≠ _
    rw [← hb']
    exact hd.2 (b / 2) b (by omega) (by omega) (by omega) hbL (by omega)
  · exact hd.2 c (b / 2) h1 hc (by omega) (by omega) hcb
  · rw [← hb']
    exact hd.2 c b h1 hc (by omega) hbL hcb

include hin hl hL hd hb hbL hbad in
/-- The exchanged tree's keys are fresh and distinct. -/
theorem distinct_exchanged : Distinct layout (exchanged layout g variant salt root b v') variant salt root L H₀ := by
  obtain ⟨hp, hp', G1, G2, G3, G4⟩ := conditions_of_distinct layout L g variant salt root H₀ hd b hb hbL v' hbad
  have hnode := node_exchanged layout hin hl L hL g variant salt root b hb hbL v' hp hp' G1 G2 G3 G4
  have hbH : layout.key (layout.output v') ∉ keysOf H₀ := by
    simp only [Bad, not_or] at hbad
    exact hbad.1
  refine ⟨fun c h1 hc => ?_, fun c c' h1 hc h1' hc' hne => ?_⟩
  · rw [hnode c hc]
    by_cases hcb : c = b
    · rw [if_pos hcb]; exact hbH
    · rw [if_neg hcb]; exact hd.1 c h1 hc
  · rw [hnode c hc, hnode c' hc']
    by_cases hcb : c = b
    · rw [if_pos hcb, if_neg (by omega)]
      exact fun h => G3 c' h1' hc' h.symm
    · rw [if_neg hcb]
      by_cases hcb' : c' = b
      · rw [if_pos hcb']
        exact G3 c h1 hc
      · rw [if_neg hcb']
        exact hd.2 c c' h1 hc h1' hc' hne

include hin hl hL hd hb hbL hbad in
/-- Another leaf keeps its parent seed and its block under the exchange. -/
theorem other_leaf_exchanged (hleaf : L ≤ b) (b' : Nat) (hb'1 : 1 < b') (hb'L : b' < 2 * L) (hne : b' ≠ b) :
    node (treeExpand layout (exchanged layout g variant salt root b v') variant salt) root (b' / 2) =
        node (treeExpand layout g variant salt) root (b' / 2) ∧
      nodeBlock layout (exchanged layout g variant salt root b v') variant salt root b' =
        nodeBlock layout g variant salt root b' := by
  obtain ⟨hp, hp', G1, G2, G3, G4⟩ := conditions_of_distinct layout L g variant salt root H₀ hd b hb hbL v' hbad
  have hnode := node_exchanged layout hin hl L hL g variant salt root b hb hbL v' hp hp' G1 G2 G3 G4
  have hhalf : node (treeExpand layout (exchanged layout g variant salt root b v') variant salt) root (b' / 2) =
      node (treeExpand layout g variant salt) root (b' / 2) := by
    rw [hnode (b' / 2) (by omega), if_neg (by omega)]
  refine ⟨hhalf, ?_⟩
  unfold nodeBlock parentKey
  rw [hhalf]
  unfold exchanged
  by_cases hpar : b' / 2 = b / 2
  · -- the sibling: read at the parent's key, moved by neither block
    have hpk : layout.key (node (treeExpand layout g variant salt) root (b / 2)) = parentKey layout g variant salt root b := rfl
    rw [hpar, hpk, swapNode_apply_parent, Equiv.trans_apply]
    have h1 : (g (parentKey layout g variant salt root b)) (layout.input (nodeTweak variant salt b')) ≠
        nodeBlock layout g variant salt root b := by
      intro h
      have hinj := (g (parentKey layout g variant salt root b)).injective h
      exact nodeTweak_ne_of_sibling hl L hL variant salt b b' hbL hb'L hpar hne (hin hinj)
    have h2 := G4 b' hb'L hpar hne
    exact @Equiv.swap_apply_of_ne_of_ne _ (fun a b => Classical.propDecidable (a = b)) _ _ _ h1 h2
  · -- another parent: a key the exchange fixes
    rw [swapNode_apply_of_ne _ _ _ _ _ _ _ (G1 (b' / 2) (by omega) (by omega) hpar)
      (G2 (b' / 2) (by omega) (by omega) (by omega)) (G3 (b' / 2) (by omega) (by omega))]

end
end SDitH.Proofs.LeafExchangeDistinct
