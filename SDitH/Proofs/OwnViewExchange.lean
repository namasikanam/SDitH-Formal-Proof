import SDitH.Proofs.CommitViewExchange
import SDitH.Proofs.CommitHistoryKeys
import SDitH.Proofs.HiddenKeysExchange
import SDitH.Proofs.FiberCountingSided

/-! The commitment view pruned at its own hidden keys under the exchange.
Each family's view prunes the history at that family's hidden keys of the
hidden leaf. When the exchanged node lies on the hidden path, the two
pruned views coincide: neither history has entries at the other family's
key of the node (the tree's keys are good and the starting history is
fresh there), so each view prunes as well at the other key, the two
enlarged key lists have the same members, and the common view is the
commitment run's view under the exchange. -/

namespace SDitH.Proofs.OwnViewExchange

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open HiddenLeafNode HiddenEntries HiddenKeys HiddenKeysExchange NodeExchange TreeExchange CommitPhaseExchange
open CommitRunExchange CommitViewExchange CommitHistoryKeys FiberCountingSided SharedResample SharedPrune
open TreeHistoryExchange
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The commitment run followed by a post-processing, viewed with the
family stripped and the history pruned at a key list. -/
def ownView {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2) (root : Bits lambda)
    {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (K : List (Bits lambda)) (w₀ : World lambda s wit rnd) : PMF (Sig × World lambda s wit rnd) :=
  (runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w₀).bind fun r =>
    (post r.1).map fun q => (q, stripFamily (pruneShared K r.2))

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w : World lambda s wit rnd) (root : Bits lambda) (b : Nat) (hb : 1 < b) (hbk : b ≤ tau * 2 ^ kappa - 1)
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
  (a : Nat) (ha : a < 2 * (tau * 2 ^ kappa)) (hpath : b ∈ pathAddresses a)

/-- The view at a key list equals the view at the list with a key added that
no recorded entry uses. -/
theorem ownView_cons_of_fresh {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (K : List (Bits lambda)) (κ : Bits lambda) (w₀ : World lambda s wit rnd)
    (hfresh : ∀ r ∈ (runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w₀).support,
      ∀ e ∈ r.2.cipherHistory, e.key ≠ κ) :
    ownView S salt witness root post (κ :: K) w₀ = ownView S salt witness root post K w₀ := by
  unfold ownView
  refine bind_congr_support _ _ _ fun r hr => ?_
  refine congrArg _ (funext fun q => ?_)
  simp only [stripFamily, pruneShared, pruneAt_cons_of_no_entry K κ r.2.cipherHistory (hfresh r hr)]

/-- The views at two key lists with the same members coincide. -/
theorem ownView_congr_mem {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (K₁ K₂ : List (Bits lambda)) (h : ∀ x, x ∈ K₁ ↔ x ∈ K₂) (w₀ : World lambda s wit rnd) :
    ownView S salt witness root post K₁ w₀ = ownView S salt witness root post K₂ w₀ := by
  unfold ownView
  refine congrArg _ (funext fun r => congrArg _ (funext fun q => ?_))
  simp only [stripFamily, pruneShared, pruneAt_congr_mem K₁ K₂ h]

include hb hbk hin hl hL hp hp' G1 G2 G3 G4 hfκ hfκ' ha hpath in
/-- The view pruned at the family's own hidden keys is the same under the
exchange of a path node. -/
theorem ownView_exchanged {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (hpost : ∀ c, post (.done (setTree b (S.layout.output v') c)) = post (.done c)) :
    ownView S salt witness root post (hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a)
        { w with family := exchanged S.layout w.family S.variant salt root b v' } =
      ownView S salt witness root post (hiddenKeys S.layout w.family S.variant salt root a) w := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root b hb (by omega) v' hp hp'
    G1 G2 G3 G4
  have hb' : node (treeExpand S.layout w.family S.variant salt) root b =
      S.layout.output (nodeBlock S.layout w.family S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout w.family S.variant salt root b hb
  -- the new key is among the exchanged family's hidden keys
  have hκ'mem : S.layout.key (S.layout.output v') ∈
      hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a := by
    rw [mem_hiddenKeys]
    exact ⟨b, Or.inr hpath, by rw [hnode b (by omega), if_pos rfl]⟩
  -- the old key and the parent key are among the family's hidden keys
  have hκmem : S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ∈
      hiddenKeys S.layout w.family S.variant salt root a := by
    rw [mem_hiddenKeys]
    exact ⟨b, Or.inr hpath, by rw [hb']⟩
  have hpmem : parentKey S.layout w.family S.variant salt root b ∈ hiddenKeys S.layout w.family S.variant salt root a := by
    rw [mem_hiddenKeys]
    exact ⟨b / 2, parent_mem_pathAddresses hpath, rfl⟩
  -- step A: the exchanged view prunes as well at the old key
  have hA : ownView S salt witness root post
      (hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a)
        { w with family := exchanged S.layout w.family S.variant salt root b v' } =
      ownView S salt witness root post
        (S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
          hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a)
        { w with family := exchanged S.layout w.family S.variant salt root b v' } := by
    by_cases hmem : S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ∈
        hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a
    · refine ownView_congr_mem S salt witness root post _ _ (fun x => ?_) _
      simp only [List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hx)
        · exact hmem
        · exact hx
    · refine (ownView_cons_of_fresh S salt witness root post _ _ _ fun r hr e he => ?_).symm
      simp only [runProgram, PMF.mem_support_map_iff] at hr
      obtain ⟨out, hout, rfl⟩ := hr
      rcases commitRun_keys S salt witness _ root _ _ _ _ out hout e he with hold | ⟨c, hc1, hcL, hc⟩
      · exact hfκ e hold
      · rw [hc, hnode c hcL]
        by_cases hcb : c = b
        · rw [if_pos hcb]
          intro h
          exact hmem (h ▸ hκ'mem)
        · rw [if_neg hcb]
          exact G2 c hc1 hcL hcb
  -- step B: the enlarged lists have the same members
  have hB : ownView S salt witness root post
      (S.layout.key (S.layout.output (nodeBlock S.layout w.family S.variant salt root b)) ::
        hiddenKeys S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root a)
        { w with family := exchanged S.layout w.family S.variant salt root b v' } =
      ownView S salt witness root post
        (S.layout.key (S.layout.output v') :: hiddenKeys S.layout w.family S.variant salt root a)
        { w with family := exchanged S.layout w.family S.variant salt root b v' } :=
    ownView_congr_mem S salt witness root post _ _
      (mem_hiddenKeys_exchanged S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root b hb (by omega) v' hp hp'
        G1 G2 G3 G4 a ha hpath) _
  -- step C: the commitment run's view under the exchange
  have hC : ownView S salt witness root post
      (S.layout.key (S.layout.output v') :: hiddenKeys S.layout w.family S.variant salt root a)
        { w with family := exchanged S.layout w.family S.variant salt root b v' } =
      ownView S salt witness root post
        (S.layout.key (S.layout.output v') :: hiddenKeys S.layout w.family S.variant salt root a) w := by
    unfold ownView
    refine commit_view_exchanged S salt witness w root b hb hbk v' hin hl hL hp hp' G1 G2 G3 G4 _ (fun x hx => ?_) post hpost
    simp only [exchangedKeys, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact List.mem_cons_of_mem _ hpmem
    · exact List.mem_cons_of_mem _ hκmem
    · exact List.mem_cons_self
  -- step D: the family's view prunes as well at the new key
  have hD : ownView S salt witness root post
      (S.layout.key (S.layout.output v') :: hiddenKeys S.layout w.family S.variant salt root a) w =
      ownView S salt witness root post (hiddenKeys S.layout w.family S.variant salt root a) w := by
    by_cases hmem : S.layout.key (S.layout.output v') ∈ hiddenKeys S.layout w.family S.variant salt root a
    · refine ownView_congr_mem S salt witness root post _ _ (fun x => ?_) _
      simp only [List.mem_cons]
      constructor
      · rintro (rfl | hx)
        · exact hmem
        · exact hx
      · exact Or.inr
    · refine ownView_cons_of_fresh S salt witness root post _ _ _ fun r hr e he => ?_
      simp only [runProgram, PMF.mem_support_map_iff] at hr
      obtain ⟨out, hout, rfl⟩ := hr
      rcases commitRun_keys S salt witness _ root _ _ _ _ out hout e he with hold | ⟨c, hc1, hcL, hc⟩
      · exact hfκ' e hold
      · rw [hc]
        exact G3 c hc1 hcL
  exact hA.trans (hB.trans (hC.trans hD))

end
end SDitH.Proofs.OwnViewExchange
