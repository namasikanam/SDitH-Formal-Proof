import SDitH.Proofs.NodeExchange
import SDitH.Proofs.HiddenKeys
import SDitH.Proofs.SeedPrimitives

/-! The seed tree under the exchange of a node's value. The exchanged family
computes the same tree except at the exchanged node, which takes the new
value: the ancestors are untouched, the node's sibling keeps its value since
the transposition moves neither it nor the new value, the node's children
are the old children because the permutation at the old key now sits at the
new key, and every other node uses a key the exchange fixes. The keys of
the tree's nodes are assumed distinct from the three exchanged keys (the
goodness of the tree), which the fresh-key counting supplies. -/

namespace SDitH.Proofs.TreeExchange

open Spec.SeedTree Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation Spec.SeedPrimitives
open HiddenLeafNode HiddenEntries NodeExchange
open scoped Classical

noncomputable section

variable {lambda : Nat} {Key Block : Type*}

/-- The key of a node's parent. -/
def parentKey (layout : Layout lambda Key Block) (f : Family Key Block) (variant : Grinding) (salt root : Bits lambda)
    (b : Nat) : Key :=
  layout.key (node (treeExpand layout f variant salt) root (b / 2))

/-- The cipher block of a node's expansion from its parent. -/
def nodeBlock (layout : Layout lambda Key Block) (f : Family Key Block) (variant : Grinding) (salt root : Bits lambda)
    (b : Nat) : Block :=
  f (parentKey layout f variant salt root b) (layout.input (nodeTweak variant salt b))

theorem node_eq_output_nodeBlock (layout : Layout lambda Key Block) (f : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (b : Nat) (hb : 1 < b) :
    node (treeExpand layout f variant salt) root b = layout.output (nodeBlock layout f variant salt root b) :=
  node_eq_child layout f variant salt root b hb

/-- The family with a node's value exchanged for a block. -/
def exchanged (layout : Layout lambda Key Block) (f : Family Key Block) (variant : Grinding) (salt root : Bits lambda)
    (b : Nat) (v' : Block) : Family Key Block :=
  swapNode (parentKey layout f variant salt root b) (nodeBlock layout f variant salt root b) v'
    (layout.key (layout.output (nodeBlock layout f variant salt root b))) (layout.key (layout.output v')) f

/-- The tweaks of two distinct siblings differ. -/
theorem nodeTweak_ne_of_sibling (hl : 26 ≤ lambda) (L : Nat) (hL : 4 * L ≤ 2 ^ 24) (variant : Grinding)
    (salt : Bits lambda) (b c : Nat) (hb : b < 2 * L) (_hc : c < 2 * L) (hcb : c / 2 = b / 2) (hne : c ≠ b) :
    nodeTweak variant salt c ≠ nodeTweak variant salt b := by
  intro h
  simp only [nodeTweak] at h
  obtain ⟨-, hpar⟩ := SeedPrimitives.cipherInput_injective hl hL (by omega : c / 2 < 2 * L) (by omega : b / 2 < 2 * L) variant salt _ _ h
  have : (c % 2 = 1 ↔ b % 2 = 1) := by simpa using hpar
  omega

/-- The tree under the exchange: the same tree except at the exchanged node. -/
theorem node_exchanged (layout : Layout lambda Key Block) (hin : Function.Injective layout.input) (hl : 26 ≤ lambda)
    (L : Nat) (hL : 4 * L ≤ 2 ^ 24) (f : Family Key Block) (variant : Grinding) (salt root : Bits lambda)
    (b : Nat) (hb : 1 < b) (hbL : b < 2 * L) (v' : Block)
    (hp : parentKey layout f variant salt root b ≠ layout.key (layout.output (nodeBlock layout f variant salt root b)))
    (hp' : parentKey layout f variant salt root b ≠ layout.key (layout.output v'))
    (G1 : ∀ c, 1 ≤ c → c < 2 * L → c ≠ b / 2 →
      layout.key (node (treeExpand layout f variant salt) root c) ≠ parentKey layout f variant salt root b)
    (G2 : ∀ c, 1 ≤ c → c < 2 * L → c ≠ b →
      layout.key (node (treeExpand layout f variant salt) root c) ≠
        layout.key (layout.output (nodeBlock layout f variant salt root b)))
    (G3 : ∀ c, 1 ≤ c → c < 2 * L → layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key (layout.output v'))
    (G4 : ∀ c, c < 2 * L → c / 2 = b / 2 → c ≠ b →
      f (parentKey layout f variant salt root b) (layout.input (nodeTweak variant salt c)) ≠ v') :
    ∀ c, c < 2 * L →
      node (treeExpand layout (exchanged layout f variant salt root b v') variant salt) root c =
        if c = b then layout.output v' else node (treeExpand layout f variant salt) root c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    by_cases hc1 : c ≤ 1
    · rw [if_neg (by omega)]
      have h1 : ∀ e : Nat → Bits lambda → Bits lambda × Bits lambda, node e root c = root := fun e => by
        rw [node]
        simp [hc1]
      rw [h1, h1]
    · have hc1' : 1 < c := by omega
      have hhalf := ih (c / 2) (by omega) (by omega)
      by_cases hcb : c = b
      · subst hcb
        rw [if_pos rfl, node_eq_child layout _ variant salt root c hc1', hhalf, if_neg (by omega)]
        show layout.output (swapNode _ _ _ _ _ f (parentKey layout f variant salt root c) _) = _
        rw [swapNode_apply_parent]
        simp only [Equiv.trans_apply]
        show layout.output (Equiv.swap (nodeBlock layout f variant salt root c) v' (nodeBlock layout f variant salt root c)) = _
        rw [Equiv.swap_apply_left]
      · rw [if_neg hcb, node_eq_child layout _ variant salt root c hc1', node_eq_child layout f variant salt root c hc1',
          hhalf]
        by_cases hhb : c / 2 = b
        · rw [if_pos hhb]
          show layout.output (swapNode _ _ _ _ _ f (layout.key (layout.output v')) _) = _
          rw [swapNode_apply_right _ _ _ _ _ _ hp'.symm, hhb, node_eq_output_nodeBlock layout f variant salt root b hb]
        · rw [if_neg hhb]
          by_cases hsib : c / 2 = b / 2
          · have hkey : layout.key (node (treeExpand layout f variant salt) root (c / 2)) =
                parentKey layout f variant salt root b := by
              rw [hsib]; rfl
            rw [hkey]
            show layout.output (swapNode _ _ _ _ _ f (parentKey layout f variant salt root b) _) = _
            rw [swapNode_apply_parent]
            simp only [Equiv.trans_apply]
            rw [Equiv.swap_apply_of_ne_of_ne]
            · exact (f (parentKey layout f variant salt root b)).injective.ne
                (hin.ne (nodeTweak_ne_of_sibling hl L hL variant salt b c hbL hc hsib hcb))
            · exact G4 c hc hsib hcb
          · show layout.output (swapNode _ _ _ _ _ f _ _) = _
            rw [swapNode_apply_of_ne _ _ _ _ _ f _ (G1 (c / 2) (by omega) (by omega) hsib)
              (G2 (c / 2) (by omega) (by omega) hhb) (G3 (c / 2) (by omega) (by omega))]

end
end SDitH.Proofs.TreeExchange
