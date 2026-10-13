import SDitH.Proofs.RootExchange
import SDitH.Proofs.TreeRunClosed
import SDitH.Proofs.TreeHistoryExchange

/-! The expansion's run and recorded entries under the root exchange. The
seed tree's run from the new root through the exchanged family is the new
root followed by the old tree, and the recorded entries pruned at the two
root keys coincide: the root's own calls move from the old root's key to the
new one, and every other node's calls are unchanged. -/

namespace SDitH.Proofs.RootHistoryExchange

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree
open Spec.IdealCipher (Family)
open HiddenLeafNode HiddenEntries KeySwap RootExchange TreeRunClosed TreeHistoryExchange
open scoped Classical

noncomputable section

variable {lambda : Nat} (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
  (f : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root root' : Bits lambda)
  (L : Nat)
  (G2 : ∀ c, 2 ≤ c → c < 2 * L → layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key root)
  (G3 : ∀ c, 2 ≤ c → c < 2 * L → layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key root')

/-- The two root keys. -/
def rootKeys : List (Bits lambda) := [layout.key root, layout.key root']

include G2 G3 in
/-- The seed tree's run under the root exchange on the allocated addresses. -/
theorem run_root_exchanged (k : Nat) (hk : 2 * k + 1 < 2 * L) (c : Nat) (hc0 : 0 < c) (hck : c ≤ 2 * k + 1) :
    run (treeExpand layout (rootExchanged layout f root root') variant salt) root' (fun _ => root') k c =
      if c ≤ 1 then root' else run (treeExpand layout f variant salt) root (fun _ => root) k c := by
  rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ hc0 hck,
    node_root_exchanged layout f variant salt root root' L G2 G3 c (by omega)]
  by_cases hc1 : c ≤ 1
  · simp [hc1]
  · rw [if_neg hc1, if_neg hc1, SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ hc0 hck]

include G2 G3 in
/-- The recorded entries pruned at any key list containing the root keys
coincide. -/
theorem treeHistory_root_exchanged (K : List (Bits lambda)) (hK : ∀ κ ∈ rootKeys layout root root', κ ∈ K)
    (k : Nat) (hk : 2 * k + 1 < 2 * L) :
    pruneAt K (treeHistory layout (rootExchanged layout f root root') variant salt root' (fun _ => root') k) =
      pruneAt K (treeHistory layout f variant salt root (fun _ => root) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih := ih (by omega)
    have hrun := run_root_exchanged layout f variant salt root root' L G2 G3 k (by omega) (k + 1)
      (by omega) (by omega)
    simp only [treeHistory]
    by_cases hk1 : k + 1 ≤ 1
    · rw [hrun, if_pos hk1]
      have hold : run (treeExpand layout f variant salt) root (fun _ => root) k (k + 1) = root := by
        rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega), node]
        simp [hk1]
      rw [hold, pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem']
      · exact ih
      all_goals exact hK _ (by simp [rootKeys, Spec.IdealCipher.entry])
    · rw [hrun, if_neg hk1]
      have hkey : layout.key (run (treeExpand layout f variant salt) root (fun _ => root) k (k + 1)) =
          layout.key (node (treeExpand layout f variant salt) root (k + 1)) := by
        rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)]
      have hfix : rootExchanged layout f root root'
          (layout.key (run (treeExpand layout f variant salt) root (fun _ => root) k (k + 1))) =
          f (layout.key (run (treeExpand layout f variant salt) root (fun _ => root) k (k + 1))) := by
        rw [hkey]
        exact swapKeys_apply_of_ne _ _ f _ (G2 (k + 1) (by omega) (by omega)) (G3 (k + 1) (by omega) (by omega))
      rw [hfix]
      simp only [pruneAt, List.filter_cons]
      rw [← pruneAt, ← pruneAt, ih]

end
end SDitH.Proofs.RootHistoryExchange
