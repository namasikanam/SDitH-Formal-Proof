import SDitH.Proofs.OwnViewExchangeGen
import SDitH.Proofs.HiddenKeysAllExchange

/-! The view pruned at the hidden keys of all executions under the
exchanges: the abstract own-view exchanges instantiated with the hidden
keys of all executions, whose membership facts hold when the exchanged
node lies on some execution's hidden path. -/

namespace SDitH.Proofs.OwnViewExchangeAll

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open HiddenLeafNode HiddenEntries HiddenKeys HiddenKeysExchange NodeExchange TreeExchange CommitRunExchange CommitPhaseExchange
open OwnViewExchange OwnViewExchangeGen HiddenTuple HiddenKeysAllExchange KeySwap RootExchange
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w : World lambda s wit rnd) (root : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa))

/-- The view pruned at the hidden keys of all executions is the same under
the exchange of a node on some execution's hidden path. -/
theorem ownView_exchanged_all (b : Nat) (hb : 1 < b) (hbk : b ≤ tau * 2 ^ kappa - 1)
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
    (e : Fin tau) (hpath : b ∈ pathAddresses (leafAddress e (hidden e))) {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (hpost : ∀ c, post (.done (setTree b (S.layout.output v') c)) = post (.done c)) :
    ownView S salt witness root post
        (hiddenKeysAll S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root hidden)
        { w with family := exchanged S.layout w.family S.variant salt root b v' } =
      ownView S salt witness root post (hiddenKeysAll S.layout w.family S.variant salt root hidden) w := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  have hnode := node_exchanged S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root b hb (by omega) v' hp hp'
    G1 G2 G3 G4
  have hb' : node (treeExpand S.layout w.family S.variant salt) root b =
      S.layout.output (nodeBlock S.layout w.family S.variant salt root b) :=
    node_eq_output_nodeBlock S.layout w.family S.variant salt root b hb
  refine ownView_exchanged_of_mem S salt witness w root b hb hbk v' hin hl hL hp hp' G1 G2 G3 G4 hfκ hfκ' post hpost
    (fun g => hiddenKeysAll S.layout g S.variant salt root hidden) ?_ ?_ ?_
    (mem_hiddenKeysAll_exchanged S.layout w.family S.variant salt root hidden hin hl hL b hb (by omega) v' hp hp'
      G1 G2 G3 G4 e hpath)
  · have h := key_mem_hiddenKeysAll S.layout (exchanged S.layout w.family S.variant salt root b v') S.variant salt root
      hidden e b (Or.inr hpath)
    rwa [hnode b (by omega), if_pos rfl] at h
  · have h := key_mem_hiddenKeysAll S.layout w.family S.variant salt root hidden e b (Or.inr hpath)
    rwa [hb'] at h
  · exact key_mem_hiddenKeysAll S.layout w.family S.variant salt root hidden e (b / 2) (parent_mem_pathAddresses hpath)

/-- The view pruned at the hidden keys of all executions is the same under
the root exchange. -/
theorem ownView_root_exchanged_all (root' : Bits lambda) (hL2 : 2 ≤ tau * 2 ^ kappa)
    (G2 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
      S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root)
    (G3 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
      S.layout.key (node (treeExpand S.layout w.family S.variant salt) root c) ≠ S.layout.key root')
    (hfκ : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key root)
    (hfκ' : ∀ e ∈ w.cipherHistory, e.key ≠ S.layout.key root') (e : Fin tau) {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (hpost : ∀ c, post (.done (setTree 1 root' c)) = post (.done c)) :
    ownView S salt witness root' post
        (hiddenKeysAll S.layout (rootExchanged S.layout w.family root root') S.variant salt root' hidden)
        { w with family := rootExchanged S.layout w.family root root' } =
      ownView S salt witness root post (hiddenKeysAll S.layout w.family S.variant salt root hidden) w := by
  have hroot : ∀ g : Family (Bits lambda) (Bits lambda), ∀ r : Bits lambda,
      node (treeExpand S.layout g S.variant salt) r 1 = r := fun g r => by
    rw [node]
    simp
  refine ownView_root_exchanged_of_mem S salt witness w root root' hL2 G2 G3 hfκ hfκ' post hpost
    (fun r g => hiddenKeysAll S.layout g S.variant salt r hidden) ?_ ?_
    (mem_hiddenKeysAll_root_exchanged S.layout w.family S.variant salt root hidden root' G2 G3 e)
  · have h := key_mem_hiddenKeysAll S.layout (rootExchanged S.layout w.family root root') S.variant salt root' hidden e 1
      (Or.inl rfl)
    rwa [hroot] at h
  · have h := key_mem_hiddenKeysAll S.layout w.family S.variant salt root hidden e 1 (Or.inl rfl)
    rwa [hroot] at h

end
end SDitH.Proofs.OwnViewExchangeAll
