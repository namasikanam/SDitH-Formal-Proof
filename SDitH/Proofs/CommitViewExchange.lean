import SDitH.Proofs.CommitPruned
import SDitH.Proofs.PrefixOrMention
import SDitH.Proofs.SharedPrune

/-! The commitment run's view under the exchange. For a post-processing of
the committed value that does not read an internal node of the tree, the
commitment run followed by it, viewed with the world's family stripped and
its cipher history pruned at a key list containing the exchanged keys, has
the same law under the exchanged family and under the family. -/

namespace SDitH.Proofs.CommitViewExchange

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open HiddenLeafNode HiddenEntries NodeExchange TreeExchange TreeRunClosed TreeHistoryExchange CommitPhaseExchange
open CommitRunExchange CommitPruned RunHistoryShift RunCongr SharedResample PrefixOrMention SharedPrune
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat}

/-- A shared world with its family replaced by the identity family. -/
def stripFamily (o : World lambda s wit rnd) : World lambda s wit rnd :=
  { o with family := fun _ => Equiv.refl (Bits lambda) }

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
  (K : List (Bits lambda)) (hK : ∀ κ ∈ exchangedKeys S.layout w.family S.variant salt root b v', κ ∈ K)

include hb hbk hin hl hL hp hp' G1 G2 G3 G4 hK in
/-- The commitment run's view under the exchange. -/
theorem commit_view_exchanged {Sig : Type*}
    (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
    (hpost : ∀ c, post (.done (setTree b (S.layout.output v') c)) = post (.done c)) :
    ((runProgram (commitBudget tau kappa) (commitProgram S salt root witness)
        { w with family := exchanged S.layout w.family S.variant salt root b v' }).bind fun r =>
      (post r.1).map fun q => (q, stripFamily (pruneShared K r.2))) =
    ((runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w).bind fun r =>
      (post r.1).map fun q => (q, stripFamily (pruneShared K r.2))) := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  unfold runProgram
  simp only
  rw [commitRun_exchanged S salt witness hin hl hL w.family root b hb hbk v' hp hp' G1 G2 G3 G4,
    commitRun_eq S salt witness w.family root]
  conv_rhs => rw [runFixed_history_shift]
  simp only [PMF.bind_map, Function.comp_def]
  unfold baseTree
  refine bind_congr_support _ _ _ fun out hout => ?_
  obtain ⟨c, hc⟩ := runFixed_bounded_done _ _ _ (commitRest_bounded S salt witness _) _ _ _ _ out hout
  simp only [appendHistory, hc, Spec.HashCipherProgram.bind, hpost]
  refine congrArg _ (funext fun q => ?_)
  simp only [stripFamily, pruneShared, pruneAt_append,
    treeHistory_exchanged_subset S.layout hin hl (tau * 2 ^ kappa) hL w.family S.variant salt root (fun _ => root) b hb
      (by omega) v' hp hp' G1 G2 G3 G4 K hK (tau * 2 ^ kappa - 1) (by omega)]

end
end SDitH.Proofs.CommitViewExchange
