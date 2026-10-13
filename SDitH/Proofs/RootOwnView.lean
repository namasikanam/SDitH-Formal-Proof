import SDitH.Proofs.RootCommitView

/-! The commitment view pruned at its own hidden keys under the root
exchange. As for a path node: neither history has entries at the other
root's key, so each view prunes as well at it, the enlarged key lists have
the same members, and the common view is the commitment run's view under
the root exchange. -/

namespace SDitH.Proofs.RootOwnView

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open HiddenLeafNode HiddenEntries HiddenKeys KeySwap RootExchange RootHistoryExchange RootCommitRun RootCommitView
open CommitPhaseExchange CommitRunExchange CommitViewExchange CommitHistoryKeys OwnViewExchange FiberCountingSided
open HiddenKeysExchange SharedResample SharedPrune
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w : World lambda s wit rnd) (root root' : Bits lambda) (hL2 : 2 ≤ tau * 2 ^ kappa)
  (G2 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root)
  (G3 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root')
  (hfκ : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key root)
  (hfκ' : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key root')
  (a : Nat) (ha : a < 2 * (tau * 2 ^ kappa))

include hL2 G2 G3 hfκ hfκ' ha in
/-- The view pruned at the family's own hidden keys is the same under the
root exchange. -/
theorem ownView_root_exchanged {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (hpost : ∀ c, post (.done (setTree 1 root' c)) = post (.done c)) :
    ownView S salt witness root' post
        (hiddenKeys S.layout (rootExchanged S.layout w.family root root') S.variant salt root' a)
        { w with family := rootExchanged S.layout w.family root root' } =
      ownView S salt witness root post (hiddenKeys S.layout w.family S.variant salt root a) w := by
  have hnode := node_root_exchanged S.layout w.family S.variant salt root root' (tau * 2 ^ kappa) G2 G3
  have hroot : ∀ g : Family (Bits lambda) (Bits lambda), ∀ r : Bits lambda,
      node (treeExpand S.layout g S.variant salt) r 1 = r := fun g r => by
    rw [node]
    simp
  set g' := rootExchanged S.layout w.family root root' with hg'
  set L' := hiddenKeys S.layout g' S.variant salt root' a with hL'
  set L := hiddenKeys S.layout w.family S.variant salt root a with hL
  -- the new root's key is among the exchanged hidden keys, the old among the family's
  have hκ'mem : S.layout.key root' ∈ L' := by
    rw [hL', mem_hiddenKeys]
    exact ⟨1, Or.inl rfl, by rw [hroot]⟩
  have hκmem : S.layout.key root ∈ L := by
    rw [hL, mem_hiddenKeys]
    exact ⟨1, Or.inl rfl, by rw [hroot]⟩
  -- the keys the exchanged run records: the history's, the new root's, or the tree's below the root
  have hkeys' : ∀ r ∈ (runProgram (commitBudget tau kappa) (commitProgram S salt root' witness)
      { w with family := g' }).support, ∀ e ∈ r.2.cipherHistory,
      e ∈ w.cipherHistory ∨ e.key = S.layout.key root' ∨
        ∃ c, 2 ≤ c ∧ c < 2 * (tau * 2 ^ kappa) ∧ e.key = S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) := by
    intro r hr e he
    simp only [runProgram, PMF.mem_support_map_iff] at hr
    obtain ⟨out, hout, rfl⟩ := hr
    rcases commitRun_keys S salt witness _ root' _ _ _ _ out hout e he with hold | ⟨c, hc1, hcL, hc⟩
    · exact Or.inl hold
    · rw [hc, hnode c hcL]
      by_cases hc1' : c ≤ 1
      · rw [if_pos hc1']
        exact Or.inr (Or.inl rfl)
      · rw [if_neg hc1']
        exact Or.inr (Or.inr ⟨c, by omega, hcL, rfl⟩)
  -- the keys the family's run records
  have hkeys : ∀ r ∈ (runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w).support,
      ∀ e ∈ r.2.cipherHistory,
      e ∈ w.cipherHistory ∨ e.key = S.layout.key root ∨
        ∃ c, 2 ≤ c ∧ c < 2 * (tau * 2 ^ kappa) ∧ e.key = S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) := by
    intro r hr e he
    simp only [runProgram, PMF.mem_support_map_iff] at hr
    obtain ⟨out, hout, rfl⟩ := hr
    rcases commitRun_keys S salt witness _ root _ _ _ _ out hout e he with hold | ⟨c, hc1, hcL, hc⟩
    · exact Or.inl hold
    · by_cases hc1' : c ≤ 1
      · have : c = 1 := by omega
        subst this
        rw [hc, hroot]
        exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨c, by omega, hcL, hc⟩)
  -- step A: the exchanged view prunes as well at the old root's key
  have hA : ownView S salt witness root' post L' { w with family := g' } =
      ownView S salt witness root' post (S.layout.key root :: L') { w with family := g' } := by
    by_cases hmem : S.layout.key root ∈ L'
    · refine ownView_congr_mem S salt witness root' post _ _ (fun x => ?_) _
      simp only [List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun hx => hx ▸ hmem) id⟩
    · refine (ownView_cons_of_fresh S salt witness root' post _ _ _ fun r hr e he => ?_).symm
      rcases hkeys' r hr e he with hold | hr' | ⟨c, hc2, hcL, hc⟩
      · exact hfκ e hold
      · rw [hr']
        intro h
        exact hmem (h ▸ hκ'mem)
      · rw [hc]
        exact G2 c hc2 hcL
  -- step B: the enlarged lists have the same members
  have hB : ownView S salt witness root' post (S.layout.key root :: L') { w with family := g' } =
      ownView S salt witness root' post (S.layout.key root' :: L) { w with family := g' } :=
    ownView_congr_mem S salt witness root' post _ _
      (mem_hiddenKeys_root_exchanged S salt w root root' a ha · G2 G3) _
  -- step C: the commitment run's view under the root exchange
  have hC : ownView S salt witness root' post (S.layout.key root' :: L) { w with family := g' } =
      ownView S salt witness root post (S.layout.key root' :: L) w := by
    unfold ownView
    refine commit_view_root_exchanged S salt witness w root root' hL2 G2 G3 post hpost _ fun x hx => ?_
    simp only [rootKeys, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact List.mem_cons_of_mem _ hκmem
    · exact List.mem_cons_self
  -- step D: the family's view prunes as well at the new root's key
  have hD : ownView S salt witness root post (S.layout.key root' :: L) w = ownView S salt witness root post L w := by
    by_cases hmem : S.layout.key root' ∈ L
    · refine ownView_congr_mem S salt witness root post _ _ (fun x => ?_) _
      simp only [List.mem_cons]
      exact ⟨fun h => h.elim (fun hx => hx ▸ hmem) id, Or.inr⟩
    · refine ownView_cons_of_fresh S salt witness root post _ _ _ fun r hr e he => ?_
      rcases hkeys r hr e he with hold | hr' | ⟨c, hc2, hcL, hc⟩
      · exact hfκ' e hold
      · rw [hr']
        intro h
        exact hmem (h ▸ hκmem)
      · rw [hc]
        exact G3 c hc2 hcL
  exact hA.trans (hB.trans (hC.trans hD))

end
end SDitH.Proofs.RootOwnView
