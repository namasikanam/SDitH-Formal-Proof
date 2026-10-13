import SDitH.Proofs.KeySwap
import SDitH.Proofs.HiddenKeys

/-! The seed tree under the exchange of the root. Exchanging the root for
another seed while swapping the permutations at the two roots' keys
computes the same tree below the root: the root's
children are the old root's permutation's outputs at the new root's key,
and every other node uses a key the exchange fixes. -/

namespace SDitH.Proofs.RootExchange

open Spec.SeedTree Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation
open HiddenLeafNode HiddenEntries KeySwap
open scoped Classical

noncomputable section

variable {lambda : Nat} {Key Block : Type*}

/-- The family with the permutations at the two roots' keys swapped. -/
def rootExchanged (layout : Layout lambda Key Block) (f : Family Key Block) (root root' : Bits lambda) :
    Family Key Block :=
  swapKeys (layout.key root) (layout.key root') f

/-- The tree under the root exchange: the new root, then the old tree. -/
theorem node_root_exchanged (layout : Layout lambda Key Block) (f : Family Key Block) (variant : Grinding)
    (salt root root' : Bits lambda) (L : Nat)
    (G2 : ∀ c, 2 ≤ c → c < 2 * L → layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key root)
    (G3 : ∀ c, 2 ≤ c → c < 2 * L → layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key root') :
    ∀ c, c < 2 * L →
      node (treeExpand layout (rootExchanged layout f root root') variant salt) root' c =
        if c ≤ 1 then root' else node (treeExpand layout f variant salt) root c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    by_cases hc1 : c ≤ 1
    · rw [if_pos hc1, node]
      simp [hc1]
    · have hc1' : 1 < c := by omega
      rw [if_neg hc1, node_eq_child layout _ variant salt root' c hc1', node_eq_child layout f variant salt root c hc1',
        ih (c / 2) (by omega) (by omega)]
      by_cases hhalf : c / 2 ≤ 1
      · rw [if_pos hhalf]
        have hroot : node (treeExpand layout f variant salt) root (c / 2) = root := by
          rw [node]
          simp [hhalf]
        rw [hroot]
        show layout.output (swapKeys _ _ f (layout.key root') _) = _
        rw [swapKeys_apply_right]
      · rw [if_neg hhalf]
        show layout.output (swapKeys _ _ f _ _) = _
        rw [swapKeys_apply_of_ne _ _ f _ (G2 (c / 2) (by omega) (by omega)) (G3 (c / 2) (by omega) (by omega))]

end
end SDitH.Proofs.RootExchange
