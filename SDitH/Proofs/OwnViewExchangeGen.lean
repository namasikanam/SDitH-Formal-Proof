import SDitH.Proofs.OwnViewExchange
import SDitH.Proofs.RootOwnView

/-! The own-view exchange for an abstract key list. The view pruned at a
key list chosen from the family is the same under the exchange of a node,
or of the root, as soon as the list contains the keys the exchange moves
and the enlarged lists have the same members: the proofs of the hidden
keys' own-view exchanges only use these three facts. -/

namespace SDitH.Proofs.OwnViewExchangeGen

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open HiddenLeafNode HiddenEntries HiddenKeys HiddenKeysExchange NodeExchange TreeExchange CommitPhaseExchange
open CommitRunExchange CommitViewExchange CommitHistoryKeys FiberCountingSided SharedResample SharedPrune
open TreeHistoryExchange OwnViewExchange KeySwap RootExchange RootHistoryExchange RootCommitRun RootCommitView
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w : World lambda s wit rnd) (root : Bits lambda)

section Node

variable (b : Nat) (hb : 1 < b) (hbk : b ≤ tau * 2 ^ kappa - 1)
  (v' : Bits lambda) (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (hp : parentKey S.layout w.family S.variant salt root b ≠
    S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)))
  (hp' : parentKey S.layout w.family S.variant salt root b ≠ S.layout.key (S.layout.output v'))
  (G1 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b / 2 →
    S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ parentKey S.layout w.family S.variant salt root b)
  (G2 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b →
    S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠
      S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)))
  (G3 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key (S.layout.output v'))
  (G4 : ∀ c, c < 2 * (tau * 2 ^ kappa) → c / 2 = b / 2 → c ≠ b →
    w.family (parentKey S.layout w.family S.variant salt root b) (S.layout.input (nodeTweak S.variant salt c)) ≠ v')
  (hfκ : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)))
  (hfκ' : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key (S.layout.output v'))

include hb hbk hin hl hL hp hp' G1 G2 G3 G4 hfκ hfκ' in
/-- The view pruned at a key list chosen from the family is the same under
the exchange of a node when the list contains the moved keys and the
enlarged lists have the same members. -/
theorem ownView_exchanged_of_mem {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (hpost : ∀ c, post (.done (setTree b (S.layout.output v') c)) = post (.done c))
    (K : Family (Bits lambda) (Bits lambda) → List (Bits lambda))
    (hκ'mem : S.layout.key (S.layout.output v') ∈ K (exchanged S.layout w.family S.variant salt root b v'))
    (hκmem : S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ∈ K w.family)
    (hpmem : parentKey S.layout w.family S.variant salt root b ∈ K w.family)
    (hmem : ∀ x, x ∈ S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
        K (exchanged S.layout w.family S.variant salt root b v') ↔
      x ∈ S.layout.key (S.layout.output v') :: K w.family) :
    ownView S salt witness root post (K (exchanged S.layout w.family S.variant salt root b v'))
        { w with family := exchanged S.layout w.family S.variant salt root b v' } =
      ownView S salt witness root post (K w.family) w := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root b hb (by omega) v' hp hp'
    G1 G2 G3 G4
  -- step A: the exchanged view prunes as well at the old key
  have hA : ownView S salt witness root post (K (exchanged S.layout w.family S.variant salt root b v'))
        { w with family := exchanged S.layout w.family S.variant salt root b v' } =
      ownView S salt witness root post
        (S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
          K (exchanged S.layout w.family S.variant salt root b v'))
        { w with family := exchanged S.layout w.family S.variant salt root b v' } := by
    by_cases hmem' : S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ∈
        K (exchanged S.layout w.family S.variant salt root b v')
    · refine ownView_congr_mem S salt witness root post _ _ (fun x => ?_) _
      simp only [List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun hx => hx ▸ hmem') id⟩
    · refine (ownView_cons_of_fresh S salt witness root post _ _ _ fun r hr e he => ?_).symm
      simp only [runProgram, PMF.mem_support_map_iff] at hr
      obtain ⟨out, hout, rfl⟩ := hr
      rcases commitRun_keys S salt witness _ root _ _ _ _ out hout e he with hold | ⟨c, hc1, hcL, hc⟩
      · exact hfκ e hold
      · rw [hc, hnode c hcL]
        by_cases hcb : c = b
        · rw [if_pos hcb]
          intro h
          exact hmem' (h ▸ hκ'mem)
        · rw [if_neg hcb]
          exact G2 c hc1 hcL hcb
  -- step B: the enlarged lists have the same members
  have hB : ownView S salt witness root post
        (S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
          K (exchanged S.layout w.family S.variant salt root b v'))
        { w with family := exchanged S.layout w.family S.variant salt root b v' } =
      ownView S salt witness root post (S.layout.key (S.layout.output v') :: K w.family)
        { w with family := exchanged S.layout w.family S.variant salt root b v' } :=
    ownView_congr_mem S salt witness root post _ _ hmem _
  -- step C: the commitment run's view under the exchange
  have hC : ownView S salt witness root post (S.layout.key (S.layout.output v') :: K w.family)
        { w with family := exchanged S.layout w.family S.variant salt root b v' } =
      ownView S salt witness root post (S.layout.key (S.layout.output v') :: K w.family) w := by
    unfold ownView
    refine commit_view_exchanged S salt witness w root b hb hbk v' hin hl hL hp hp' G1 G2 G3 G4 _ (fun x hx => ?_) post hpost
    simp only [exchangedKeys, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact List.mem_cons_of_mem _ hpmem
    · exact List.mem_cons_of_mem _ hκmem
    · exact List.mem_cons_self
  -- step D: the family's view prunes as well at the new key
  have hD : ownView S salt witness root post (S.layout.key (S.layout.output v') :: K w.family) w =
      ownView S salt witness root post (K w.family) w := by
    by_cases hmem' : S.layout.key (S.layout.output v') ∈ K w.family
    · refine ownView_congr_mem S salt witness root post _ _ (fun x => ?_) _
      simp only [List.mem_cons]
      exact ⟨fun h => h.elim (fun hx => hx ▸ hmem') id, Or.inr⟩
    · refine ownView_cons_of_fresh S salt witness root post _ _ _ fun r hr e he => ?_
      simp only [runProgram, PMF.mem_support_map_iff] at hr
      obtain ⟨out, hout, rfl⟩ := hr
      rcases commitRun_keys S salt witness _ root _ _ _ _ out hout e he with hold | ⟨c, hc1, hcL, hc⟩
      · exact hfκ' e hold
      · rw [hc]
        exact G3 c hc1 hcL
  exact hA.trans (hB.trans (hC.trans hD))

end Node

section Root

variable (root' : Bits lambda) (hL2 : 2 ≤ tau * 2 ^ kappa)
  (G2 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root)
  (G3 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root')
  (hfκ : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key root)
  (hfκ' : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key root')

include hL2 G2 G3 hfκ hfκ' in
/-- The view pruned at a key list chosen from the root and the family is
the same under the root exchange when the lists contain the roots' keys
and the enlarged lists have the same members. -/
theorem ownView_root_exchanged_of_mem {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (hpost : ∀ c, post (.done (setTree 1 root' c)) = post (.done c))
    (K : Bits lambda → Family (Bits lambda) (Bits lambda) → List (Bits lambda))
    (hκ'mem : S.layout.key root' ∈ K root' (rootExchanged S.layout w.family root root'))
    (hκmem : S.layout.key root ∈ K root w.family)
    (hmem : ∀ x, x ∈ S.layout.key root :: K root' (rootExchanged S.layout w.family root root') ↔
      x ∈ S.layout.key root' :: K root w.family) :
    ownView S salt witness root' post (K root' (rootExchanged S.layout w.family root root'))
        { w with family := rootExchanged S.layout w.family root root' } =
      ownView S salt witness root post (K root w.family) w := by
  have hnode := node_root_exchanged S.layout w.family S.variant salt root root' (tau * 2 ^ kappa) G2 G3
  have hroot : ∀ g : Family (Bits lambda) (Bits lambda), ∀ r : Bits lambda,
      node (treeExpand S.layout g S.variant salt) r 1 = r := fun g r => by
    rw [node]
    simp
  -- the keys the exchanged run records: the history's, the new root's, or the tree's below the root
  have hkeys' : ∀ r ∈ (runProgram (commitBudget tau kappa) (commitProgram S salt root' witness)
      { w with family := rootExchanged S.layout w.family root root' }).support, ∀ e ∈ r.2.cipherHistory,
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
  have hA : ownView S salt witness root' post (K root' (rootExchanged S.layout w.family root root'))
        { w with family := rootExchanged S.layout w.family root root' } =
      ownView S salt witness root' post (S.layout.key root :: K root' (rootExchanged S.layout w.family root root'))
        { w with family := rootExchanged S.layout w.family root root' } := by
    by_cases hmem' : S.layout.key root ∈ K root' (rootExchanged S.layout w.family root root')
    · refine ownView_congr_mem S salt witness root' post _ _ (fun x => ?_) _
      simp only [List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun hx => hx ▸ hmem') id⟩
    · refine (ownView_cons_of_fresh S salt witness root' post _ _ _ fun r hr e he => ?_).symm
      rcases hkeys' r hr e he with hold | hr' | ⟨c, hc2, hcL, hc⟩
      · exact hfκ e hold
      · rw [hr']
        intro h
        exact hmem' (h ▸ hκ'mem)
      · rw [hc]
        exact G2 c hc2 hcL
  -- step B: the enlarged lists have the same members
  have hB : ownView S salt witness root' post (S.layout.key root :: K root' (rootExchanged S.layout w.family root root'))
        { w with family := rootExchanged S.layout w.family root root' } =
      ownView S salt witness root' post (S.layout.key root' :: K root w.family)
        { w with family := rootExchanged S.layout w.family root root' } :=
    ownView_congr_mem S salt witness root' post _ _ hmem _
  -- step C: the commitment run's view under the root exchange
  have hC : ownView S salt witness root' post (S.layout.key root' :: K root w.family)
        { w with family := rootExchanged S.layout w.family root root' } =
      ownView S salt witness root post (S.layout.key root' :: K root w.family) w := by
    unfold ownView
    refine commit_view_root_exchanged S salt witness w root root' hL2 G2 G3 post hpost _ fun x hx => ?_
    simp only [rootKeys, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact List.mem_cons_of_mem _ hκmem
    · exact List.mem_cons_self
  -- step D: the family's view prunes as well at the new root's key
  have hD : ownView S salt witness root post (S.layout.key root' :: K root w.family) w =
      ownView S salt witness root post (K root w.family) w := by
    by_cases hmem' : S.layout.key root' ∈ K root w.family
    · refine ownView_congr_mem S salt witness root post _ _ (fun x => ?_) _
      simp only [List.mem_cons]
      exact ⟨fun h => h.elim (fun hx => hx ▸ hmem') id, Or.inr⟩
    · refine ownView_cons_of_fresh S salt witness root post _ _ _ fun r hr e he => ?_
      rcases hkeys r hr e he with hold | hr' | ⟨c, hc2, hcL, hc⟩
      · exact hfκ' e hold
      · rw [hr']
        intro h
        exact hmem' (h ▸ hκmem)
      · rw [hc]
        exact G3 c hc2 hcL
  exact hA.trans (hB.trans (hC.trans hD))

end Root

end
end SDitH.Proofs.OwnViewExchangeGen
