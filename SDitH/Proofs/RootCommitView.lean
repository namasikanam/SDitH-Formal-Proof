import SDitH.Proofs.RootCommitRun
import SDitH.Proofs.CommitViewExchange
import SDitH.Proofs.CommitHistoryKeys
import SDitH.Proofs.OwnViewExchange

/-! The commitment run's view under the root exchange. For a post-processing
of the committed value that does not read the root, the commitment run from
the new root through the exchanged family, followed by it and viewed with
the family stripped and the history pruned at a key list containing the
root keys, has the same law as the run from the root through the family;
and the views pruned at each family's own hidden keys coincide. -/

namespace SDitH.Proofs.RootCommitView

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open HiddenLeafNode HiddenEntries HiddenKeys KeySwap RootExchange RootHistoryExchange RootCommitRun
open CommitPhaseExchange CommitRunExchange CommitViewExchange CommitHistoryKeys OwnViewExchange FiberCountingSided
open HiddenKeysExchange RunHistoryShift RunCongr SharedResample SharedPrune PrefixOrMention
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w : World lambda s wit rnd) (root root' : Bits lambda) (hL2 : 2 ≤ tau * 2 ^ kappa)
  (G2 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root)
  (G3 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root')

include hL2 G2 G3 in
/-- The commitment run's view under the root exchange. -/
theorem commit_view_root_exchanged {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (hpost : ∀ c, post (.done (setTree 1 root' c)) = post (.done c)) (K : List (Bits lambda))
    (hK : ∀ κ ∈ rootKeys S.layout root root', κ ∈ K) :
    ((runProgram (commitBudget tau kappa) (commitProgram S salt root' witness)
        { w with family := rootExchanged S.layout w.family root root' }).bind fun r =>
      (post r.1).map fun q => (q, stripFamily (pruneShared K r.2))) =
    ((runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w).bind fun r =>
      (post r.1).map fun q => (q, stripFamily (pruneShared K r.2))) := by
  unfold runProgram
  simp only
  rw [commitRun_root_exchanged S salt witness w.family root root' hL2 G2 G3,
    commitRun_eq S salt witness w.family root]
  conv_rhs => rw [runFixed_history_shift]
  simp only [PMF.bind_map, Function.comp_def]
  unfold baseTree
  refine bind_congr_support _ _ _ fun out hout => ?_
  obtain ⟨c, hc⟩ := runFixed_bounded_done _ _ _ (commitRest_bounded S salt witness _) _ _ _ _ out hout
  simp only [appendHistory, hc, Spec.HashCipherProgram.bind, hpost]
  refine congrArg _ (funext fun q => ?_)
  simp only [stripFamily, pruneShared, pruneAt_append,
    treeHistory_root_exchanged S.layout w.family S.variant salt root root' (tau * 2 ^ kappa) G2 G3 K hK
      (tau * 2 ^ kappa - 1) (by omega)]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The hidden keys under the root exchange: with the old root's key added
they have the members of the hidden keys with the new root's key added. -/
theorem mem_hiddenKeys_root_exchanged (a : Nat) (ha : a < 2 * (tau * 2 ^ kappa)) (x : Bits lambda)
    (G2 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
      S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root)
    (G3 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
      S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root') :
    x ∈ S.layout.key root :: hiddenKeys S.layout (rootExchanged S.layout w.family root root') S.variant salt root' a ↔
      x ∈ S.layout.key root' :: hiddenKeys S.layout w.family S.variant salt root a := by
  have hnode := node_root_exchanged S.layout w.family S.variant salt root root' (tau * 2 ^ kappa) G2 G3
  have hrange : ∀ c, (c = 1 ∨ c ∈ pathAddresses a) → c < 2 * (tau * 2 ^ kappa) := by
    rintro c (rfl | hc)
    · omega
    · have := le_of_mem_pathAddresses hc
      omega
  have hroot : ∀ g : Family (Bits lambda) (Bits lambda), ∀ r : Bits lambda,
      node (treeExpand S.layout g S.variant salt) r 1 = r := fun g r => by
    rw [node]
    simp
  simp only [List.mem_cons, mem_hiddenKeys]
  constructor
  · rintro (rfl | ⟨c, hc, rfl⟩)
    · exact Or.inr ⟨1, Or.inl rfl, by rw [hroot]⟩
    · rw [hnode c (hrange c hc)]
      by_cases hc1 : c ≤ 1
      · rw [if_pos hc1]
        exact Or.inl rfl
      · rw [if_neg hc1]
        exact Or.inr ⟨c, hc, rfl⟩
  · rintro (rfl | ⟨c, hc, rfl⟩)
    · exact Or.inr ⟨1, Or.inl rfl, by rw [hnode 1 (by omega), if_pos le_rfl]⟩
    · by_cases hc1 : c ≤ 1
      · have hc1' : c = 1 := by
          rcases hc with rfl | hc
          · rfl
          · have := (mem_pathAddresses_iff.mp hc).1
            omega
        subst hc1'
        exact Or.inl (by rw [hroot])
      · exact Or.inr ⟨c, hc, by rw [hnode c (hrange c hc), if_neg hc1]⟩

end
end SDitH.Proofs.RootCommitView
