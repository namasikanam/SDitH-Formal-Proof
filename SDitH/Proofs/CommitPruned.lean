import SDitH.Proofs.CommitRunExchange
import SDitH.Proofs.CandidateResample

/-! What the exchange leaves unchanged. The expansion's recorded entries
pruned at any key list containing the three exchanged keys coincide; and
the candidate signature's payload and body do not read an internal node of
the committed tree, since the payload is the lines and the hashed
coefficients and the body opens the key at the leaves only. -/

namespace SDitH.Proofs.CommitPruned

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.IdealCipher (Family)
open HiddenLeafNode HiddenEntries NodeExchange TreeExchange TreeRunClosed TreeHistoryExchange CommitPhaseExchange
open CandidateResample
open scoped Classical

noncomputable section

section History

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
  (K : List (Bits lambda)) (hK : ∀ κ ∈ exchangedKeys layout f variant salt root b v', κ ∈ K)

include hin hl hL hb hbL hp hp' G1 G2 G3 G4 hK in
/-- The recorded entries pruned at any key list containing the exchanged
keys coincide. -/
theorem treeHistory_exchanged_subset (k : Nat) (hk : 2 * k + 1 < 2 * L) :
    pruneAt K (treeHistory layout (exchanged layout f variant salt root b v') variant salt root initial k) =
      pruneAt K (treeHistory layout f variant salt root initial k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih := ih (by omega)
    have hrun := run_exchanged layout hin hl L hL f variant salt root initial b hb hbL v' hp hp' G1 G2 G3 G4 k
      (by omega) (k + 1) (by omega) (by omega)
    simp only [treeHistory]
    by_cases hkb : k + 1 = b
    · rw [hrun, if_pos hkb]
      have hold : run (treeExpand layout f variant salt) root initial k (k + 1) =
          layout.output (nodeBlock layout f variant salt root b) := by
        rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega), hkb,
          node_eq_output_nodeBlock layout f variant salt root b hb]
      rw [hold, pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem']
      · exact ih
      all_goals exact hK _ (by simp [exchangedKeys, Spec.IdealCipher.entry])
    · rw [hrun, if_neg hkb]
      by_cases hkp : k + 1 = b / 2
      · have hkey : layout.key (run (treeExpand layout f variant salt) root initial k (k + 1)) =
            parentKey layout f variant salt root b := by
          rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega), hkp]
          rfl
        rw [hkey, pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem', pruneAt_cons_of_mem']
        · exact ih
        all_goals exact hK _ (by simp [exchangedKeys, Spec.IdealCipher.entry])
      · have hkey : layout.key (run (treeExpand layout f variant salt) root initial k (k + 1)) =
            layout.key (node (treeExpand layout f variant salt) root (k + 1)) := by
          rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)]
        have hfix : exchanged layout f variant salt root b v'
            (layout.key (run (treeExpand layout f variant salt) root initial k (k + 1))) =
            f (layout.key (run (treeExpand layout f variant salt) root initial k (k + 1))) := by
          rw [hkey]
          exact swapNode_apply_of_ne _ _ _ _ _ f _ (G1 (k + 1) (by omega) (by omega) hkp)
            (G2 (k + 1) (by omega) (by omega) hkb) (G3 (k + 1) (by omega) (by omega))
        rw [hfix]
        simp only [pruneAt, List.filter_cons]
        rw [← pruneAt, ← pruneAt, ih]

end History

section Body

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths) (salt : Bits lambda)
  (b : Nat) (x : Seed lambda) (hb : ∀ (e : Fin tau) (i : Fin (2 ^ kappa)), (leafNode e i).val ≠ b)

include hb in
/-- Opening a key with an internal node set opens the key. -/
theorem openKey_setTree (key : Key lambda tau (2 ^ kappa)) (hidden : Fin tau → Fin (2 ^ kappa)) :
    Spec.CandidateBAVC.openKey { key with tree := fun a => if a.val = b then x else key.tree a } hidden =
      Spec.CandidateBAVC.openKey key hidden := by
  simp only [Spec.CandidateBAVC.openKey]
  congr 1
  funext e i
  rw [if_neg (hb e i)]

omit [Algebra (ZMod 2) F] in
include hb in
/-- The retry attempts of a key with an internal node set are the key's. -/
theorem attempt_setTree (key : Key lambda tau (2 ^ kappa))
    (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow) (encode : (Fin tau → Fin (2 ^ kappa)) → F) :
    Spec.CandidateScheme.attempt { key with tree := fun a => if a.val = b then x else key.tree a } expand encode =
      Spec.CandidateScheme.attempt key expand encode := by
  funext ctr
  simp only [Spec.CandidateScheme.attempt, openKey_setTree b x hb]

omit [DecidableEq F] hb in
/-- The payload does not read the tree. -/
theorem payloadOf_setTree (c : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    payloadOf S salt (.done (setTree b x c)) = payloadOf S salt (.done c) := rfl

include hb in
/-- The body does not read an internal node of the tree. -/
theorem bodyOf_setTree (c : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (digest : Digest lambda) :
    bodyOf S (signedOf S salt (.done (setTree b x c))) digest = bodyOf S (signedOf S salt (.done c)) digest := by
  simp only [bodyOf, signedOf, stateOf, setTree]
  rw [attempt_setTree b x hb]

end Body

end
end SDitH.Proofs.CommitPruned
