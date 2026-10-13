import SDitH.Proofs.RootHistoryExchange
import SDitH.Proofs.CommitRunExchange

/-! The commitment run under the root exchange. From the new root through
the exchanged family, the expansion's tree is the old tree with the root
replaced, so the rest is the rest with a finish setting the root in the
committed tree, it queries only the leaves' keys where the exchanged family
agrees with the family, and the starting history only shifts the result's;
so the commitment run under the root exchange is the base run with the
root set and the exchanged expansion's history appended. -/

namespace SDitH.Proofs.RootCommitRun

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open RunCongr RunHistoryShift CommitPhaseExchange TreeRunClosed RootExchange RootHistoryExchange HiddenLeafNode
open CommitRunExchange KeySwap
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {lambda tau kappa s wit rnd : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (f : Family (Bits lambda) (Bits lambda)) (root root' : Bits lambda) (hL2 : 2 ≤ tau * 2 ^ kappa)
  (G2 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root c) ≠ S.layout.key root)
  (G3 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root c) ≠ S.layout.key root')

include hL2 G2 G3 in
/-- The root-exchanged expansion's tree is the tree with the root replaced. -/
theorem root_exchanged_tree_eq :
    commitRest S salt witness
        (Spec.SeedTree.run (treeExpand S.layout (rootExchanged S.layout f root root') S.variant salt) root'
          (fun _ => root') (tau * 2 ^ kappa - 1)) =
      commitRest S salt witness (Function.update (baseTree S salt f root) 1 root') := by
  refine commitRest_congr S salt witness _ _ fun a ha0 haL => ?_
  rw [run_root_exchanged S.layout f S.variant salt root root' (tau * 2 ^ kappa) G2 G3 (tau * 2 ^ kappa - 1)
    (by omega) a ha0 (by omega), Function.update_apply]
  by_cases ha1 : a = 1
  · subst ha1
    simp
  · rw [if_neg (by omega), if_neg ha1]
    rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
include hL2 G2 G3 in
/-- The root-exchanged family agrees with the family at the leaves' keys. -/
theorem root_exchanged_leafKeys : ∀ κ ∈ leafKeys S (baseTree S salt f root),
    rootExchanged S.layout f root root' κ = f κ := by
  rintro κ ⟨e, i, rfl⟩
  have hleaf := SDitH.Proofs.SeedTree.leafAddress_bounds e i
  have hval' : (leafNode e i).val = Spec.SeedTree.leafAddress e i := rfl
  have hge : tau * 2 ^ kappa ≤ Spec.SeedTree.leafAddress e i := Nat.le_add_right _ _
  have hsub : tau * 2 ^ kappa - 1 + 1 = tau * 2 ^ kappa := Nat.sub_add_cancel (by omega)
  have hval : baseTree S salt f root (leafNode e i).val =
      Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root (leafNode e i).val :=
    SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ hleaf.1 (by omega)
  rw [hval]
  exact swapKeys_apply_of_ne _ _ f _ (G2 _ (by omega) hleaf.2) (G3 _ (by omega) hleaf.2)

include hL2 G2 G3 in
/-- The commitment run under the root exchange: the base run with the root
set and the exchanged expansion's history appended. -/
theorem commitRun_root_exchanged (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure (rootExchanged S.layout f root root') (commitBudget tau kappa)
        (commitProgram S salt root' witness) table hashes ciphers log =
      ((runFixed procedure f (restBudget tau kappa) (commitRest S salt witness (baseTree S salt f root)) table hashes [] log).map
        fun out => { out with state := Spec.HashCipherProgram.bind out.state fun c => .done (setTree 1 root' c) }).map
        (appendHistory (treeHistory S.layout (rootExchanged S.layout f root root') S.variant salt root' (fun _ => root')
          (tau * 2 ^ kappa - 1) ++ ciphers)) := by
  rw [commitRun_eq, root_exchanged_tree_eq S salt witness f root root' hL2 G2 G3,
    commitRest_update S salt witness _ 1 _ (fun e i => by
      have hge : tau * 2 ^ kappa ≤ Spec.SeedTree.leafAddress e i := Nat.le_add_right _ _
      show Spec.SeedTree.leafAddress e i ≠ 1
      omega),
    runFixed_bind_done, runFixed_congr_family (leafKeys S (baseTree S salt f root)) f _
      (root_exchanged_leafKeys S salt f root root' hL2 G2 G3) _ _ (queriesIn_commitRest S salt witness _),
    runFixed_history_shift, PMF.map_comp, PMF.map_comp]
  rfl

end
end SDitH.Proofs.RootCommitRun
