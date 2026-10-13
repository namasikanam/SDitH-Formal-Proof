import SDitH.Proofs.TreeRunClosed
import SDitH.Proofs.TreeExchange

/-! The tree expansion's run and recorded entries under the exchange. The
seed tree's run through the exchanged family is the run through the family
with the exchanged node's value replaced, and the recorded entries pruned at
the three exchanged keys coincide: the node's own expansion calls move
from the old key to the new one, its parent's calls are at the parent key,
and every other node's calls are unchanged. -/

namespace SDitH.Proofs.TreeHistoryExchange

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree
open Spec.IdealCipher (Family)
open HiddenLeafNode HiddenEntries NodeExchange TreeExchange TreeRunClosed
open scoped Classical

noncomputable section

variable {lambda : Nat} (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
  (hin : Function.Injective layout.input) (hl : 26 ≤ lambda) (L : Nat) (hL : 4 * L ≤ 2 ^ 24)
  (f : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root : Bits lambda) (initial : Nat → Seed lambda)
  (b : Nat) (hb : 1 < b) (hbL : b < 2 * L) (v' : Bits lambda)
  (hp : parentKey layout f variant salt root b ≠ layout.key (layout.output (nodeBlock layout f variant salt root b)))
  (hp' : parentKey layout f variant salt root b ≠ layout.key (layout.output v'))
  (G1 : ∀ c, 1 ≤ c → c < 2 * L → c ≠ b / 2 →
    layout.key (node (treeExpand layout f variant salt) root c) ≠ parentKey layout f variant salt root b)
  (G2 : ∀ c, 1 ≤ c → c < 2 * L → c ≠ b →
    layout.key (node (treeExpand layout f variant salt) root c) ≠
      layout.key (layout.output (nodeBlock layout f variant salt root b)))
  (G3 : ∀ c, 1 ≤ c → c < 2 * L → layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key (layout.output v'))
  (G4 : ∀ c, c < 2 * L → c / 2 = b / 2 → c ≠ b →
    f (parentKey layout f variant salt root b) (layout.input (nodeTweak variant salt c)) ≠ v')

omit hin hl hL hb hbL hp hp' G1 G2 G3 G4 in
theorem pruneAt_cons_of_mem' (K : List (Bits lambda)) (e : Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))
    (l : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (h : e.key ∈ K) : pruneAt K (e :: l) = pruneAt K l := by
  simp [pruneAt, h]

/-- The three exchanged keys. -/
def exchangedKeys : List (Bits lambda) :=
  [parentKey layout f variant salt root b, layout.key (layout.output (nodeBlock layout f variant salt root b)),
    layout.key (layout.output v')]

include hin hl hL hb hbL hp hp' G1 G2 G3 G4 in
/-- The seed tree's run under the exchange: the run with the node's value
replaced, on the allocated addresses. -/
theorem run_exchanged (k : Nat) (hk : 2 * k + 1 < 2 * L) (c : Nat) (hc0 : 0 < c) (hck : c ≤ 2 * k + 1) :
    run (treeExpand layout (exchanged layout f variant salt root b v') variant salt) root initial k c =
      if c = b then layout.output v' else run (treeExpand layout f variant salt) root initial k c := by
  rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ hc0 hck, node_exchanged layout hin hl L hL f variant salt root b hb hbL v' hp hp'
    G1 G2 G3 G4 c (by omega)]
  by_cases hcb : c = b
  · simp [hcb]
  · rw [if_neg hcb, if_neg hcb, SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ hc0 hck]

include hin hl hL hb hbL hp hp' G1 G2 G3 G4 in
/-- The recorded entries pruned at the three exchanged keys coincide. -/
theorem treeHistory_exchanged (k : Nat) (hk : 2 * k + 1 < 2 * L) :
    pruneAt (exchangedKeys layout f variant salt root b v')
        (treeHistory layout (exchanged layout f variant salt root b v') variant salt root initial k) =
      pruneAt (exchangedKeys layout f variant salt root b v') (treeHistory layout f variant salt root initial k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih := ih (by omega)
    have hrun := run_exchanged layout hin hl L hL f variant salt root initial b hb hbL v' hp hp' G1 G2 G3 G4 k
      (by omega) (k + 1) (by omega) (by omega)
    simp only [treeHistory]
    by_cases hkb : k + 1 = b
    · -- the node's own calls: at the new key under the exchange, at the old key otherwise
      rw [hrun, if_pos hkb]
      have hold : run (treeExpand layout f variant salt) root initial k (k + 1) =
          layout.output (nodeBlock layout f variant salt root b) := by
        rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega), hkb,
          node_eq_output_nodeBlock layout f variant salt root b hb]
      rw [hold, pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem']
      · exact ih
      all_goals simp [exchangedKeys, Spec.IdealCipher.entry]
    · rw [hrun, if_neg hkb]
      by_cases hkp : k + 1 = b / 2
      · -- the parent's calls: at the parent key
        have hkey : layout.key (run (treeExpand layout f variant salt) root initial k (k + 1)) =
            parentKey layout f variant salt root b := by
          rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega), hkp]
          rfl
        rw [hkey, pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem']
        · exact ih
        all_goals simp [exchangedKeys, Spec.IdealCipher.entry]
      · -- any other node: the same key, fixed by the exchange
        have hkey : layout.key (run (treeExpand layout f variant salt) root initial k (k + 1)) =
            layout.key (node (treeExpand layout f variant salt) root (k + 1)) := by
          rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)]
        have hfix : exchanged layout f variant salt root b v' (layout.key (run (treeExpand layout f variant salt) root initial k (k + 1))) =
            f (layout.key (run (treeExpand layout f variant salt) root initial k (k + 1))) := by
          rw [hkey]
          exact swapNode_apply_of_ne _ _ _ _ _ f _ (G1 (k + 1) (by omega) (by omega) hkp)
            (G2 (k + 1) (by omega) (by omega) hkb) (G3 (k + 1) (by omega) (by omega))
        rw [hfix]
        simp only [pruneAt, List.filter_cons]
        rw [← pruneAt, ← pruneAt, ih]

end
end SDitH.Proofs.TreeHistoryExchange
