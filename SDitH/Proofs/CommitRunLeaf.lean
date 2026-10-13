import SDitH.Proofs.CommitPhaseLeaf
import SDitH.Proofs.TreeHistoryExchange

/-! The commitment run under the exchange of a leaf's value. The run is
the expansion's history followed by the rest at the expansion's tree; at
the exchanged leaf the tree is the tree with the leaf set, the phase's run
is the relabelled run of the phase, and the tail runs at the tree with the
leaf set. Pruned at a key list containing the three exchanged keys, the
history before the tail is the same as under the family. -/

namespace SDitH.Proofs.CommitRunLeaf

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open RunCongr RunHistoryShift CommitPhaseExchange TreeRunClosed TreeHistoryExchange TreeExchange HiddenLeafNode RunBind
open NodeExchange CommitRunExchange ProgramRelabel CommitPhaseLeaf HiddenEntries
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {lambda tau kappa s wit rnd : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)

/-- The phase's budget: two cipher steps per leaf. -/
def phaseBudget (tau kappa : Nat) : Nat := 2 * (Spec.SharedSlopeExec.allPairs tau kappa).length

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem restBudget_eq : restBudget tau kappa = phaseBudget tau kappa + (tau + 4) := rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem commitPhase_bounded (nodes : Nat → Seed lambda) : Bounded (phaseBudget tau kappa) (commitPhase S salt nodes) := by
  unfold phaseBudget commitPhase
  exact HashCipherProgram.bounded_mono _ _ _ (by rw [Nat.mul_comm])
    (SDitH.Proofs.SharedSigner.collect_bounded _ 2
      (fun pair => SDitH.Proofs.SharedSigner.commitCall_bounded S.layout _ S.variant salt _ _) _ _)

theorem commitTail_bounded (nodes : Nat → Seed lambda) (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) :
    Bounded (tau + 4) (commitTail S salt witness nodes commits) := by
  unfold commitTail
  refine HashCipherProgram.bounded_mono _ _ _ (by simp [List.length_finRange])
    (HashCipherProgram.bounded_bind _ _ ((List.finRange tau).length * 1) 4
      (SDitH.Proofs.SharedSigner.collect_bounded _ 1 (fun _ => SDitH.Proofs.SharedSigner.hashCall_bounded _) _ _)
      fun rowHashes => ?_)
  intro _ _ _ _
  trivial

/-- The rest's run is the phase's run continued by the tail. -/
theorem commitRest_run (f : Family (Bits lambda) (Bits lambda)) (nodes : Nat → Seed lambda)
    (table : List Bool → Option (Out lambda s wit rnd)) (hashes : List (List Bool × Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure f (restBudget tau kappa) (commitRest S salt witness nodes) table hashes ciphers log =
      (runFixed procedure f (phaseBudget tau kappa) (commitPhase S salt nodes) table hashes ciphers log).bind
        (continueRun f (tau + 4) (commitTail S salt witness nodes)) := by
  rw [restBudget_eq, commitRest_eq]
  exact runFixed_bind f _ _ _ _ (commitPhase_bounded S salt nodes) (fun commits => commitTail_bounded S salt witness nodes commits)
    table hashes ciphers log

section Exchange

variable (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (f : Family (Bits lambda) (Bits lambda)) (root : Bits lambda) (b : Nat) (hb : 1 < b) (hbL : b < 2 * (tau * 2 ^ kappa))
  (v' : Bits lambda)
  (hp : parentKey S.layout f S.variant salt root b ≠ S.layout.key (S.layout.output (nodeBlock S.layout f S.variant salt root b)))
  (hp' : parentKey S.layout f S.variant salt root b ≠ S.layout.key (S.layout.output v'))
  (G1 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b / 2 →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root c) ≠ parentKey S.layout f S.variant salt root b)
  (G2 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root c) ≠
      S.layout.key (S.layout.output (nodeBlock S.layout f S.variant salt root b)))
  (G3 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) →
    S.layout.key (Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root c) ≠ S.layout.key (S.layout.output v'))
  (G4 : ∀ c, c < 2 * (tau * 2 ^ kappa) → c / 2 = b / 2 → c ≠ b →
    f (parentKey S.layout f S.variant salt root b) (S.layout.input (nodeTweak S.variant salt c)) ≠ v')

include hin hl hL hb hbL hp hp' G1 G2 G3 G4 in
/-- The exchanged expansion's tree gives the rest at the tree with the
node set (for any node, leaves included). -/
theorem exchanged_tree_eq' :
    commitRest S salt witness
        (Spec.SeedTree.run (treeExpand S.layout (exchanged S.layout f S.variant salt root b v') S.variant salt) root
          (fun _ => root) (tau * 2 ^ kappa - 1)) =
      commitRest S salt witness (Function.update (baseTree S salt f root) b (S.layout.output v')) := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hsub : tau * 2 ^ kappa - 1 + 1 = tau * 2 ^ kappa := Nat.sub_add_cancel hpos
  refine commitRest_congr S salt witness _ _ fun a ha0 haL => ?_
  rw [run_exchanged S.layout hin hl (tau * 2 ^ kappa) hL f S.variant salt root (fun _ => root) b hb hbL v' hp hp'
    G1 G2 G3 G4 (tau * 2 ^ kappa - 1) (by omega) a ha0 (by omega), Function.update_apply]
  rfl

include hin hl hL hb hbL hp hp' G1 G2 G3 G4 in
/-- The commitment run under the exchange at a leaf: the phase's run under
the family, relabelled, with the exchanged expansion's history appended,
continued by the tail at the tree with the leaf set. -/
theorem commitRun_leaf_exchanged (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure (exchanged S.layout f S.variant salt root b v') (commitBudget tau kappa)
        (commitProgram S salt root witness) table hashes ciphers log =
      ((runFixed procedure f (phaseBudget tau kappa) (commitPhase S salt (baseTree S salt f root)) table hashes [] log).map
        fun out => appendHistory
          (treeHistory S.layout (exchanged S.layout f S.variant salt root b v') S.variant salt root (fun _ => root)
            (tau * 2 ^ kappa - 1) ++ ciphers) (mapResult (leafSwap S salt f root b v') out)).bind
      (continueRun (exchanged S.layout f S.variant salt root b v') (tau + 4)
        (commitTail S salt witness (Function.update (baseTree S salt f root) b (S.layout.output v')))) := by
  rw [commitRun_eq, exchanged_tree_eq' S salt witness hin hl hL f root b hb hbL v' hp hp' G1 G2 G3 G4, commitRest_run,
    runFixed_history_shift]
  have hphase := commitPhase_run_exchanged S salt f root b hb hbL v' hp' G1 G2 G3 (phaseBudget tau kappa) table hashes [] log
  simp only [List.map_nil] at hphase
  rw [hphase, PMF.map_comp]
  rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- Pruning at a list containing another list's members is pruning after
pruning at that list. -/
theorem pruneAt_of_subset (K K' : List (Bits lambda)) (h : ∀ k ∈ K', k ∈ K)
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) : pruneAt K (pruneAt K' H) = pruneAt K H := by
  unfold pruneAt
  rw [List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  by_cases hk : e.key ∈ K
  · simp [hk]
  · have hk' : e.key ∉ K' := fun h' => hk (h _ h')
    simp [hk, hk']

omit [Field F] [Algebra (ZMod 2) F] in
include hin hl hL hb hbL hp hp' G1 G2 G3 G4 in
/-- The history before the tail, pruned at a list containing the three
exchanged keys, is the same under the exchange. -/
theorem leaf_history_pruned (K : List (Bits lambda)) (hK : ∀ k ∈ exchangedKeys S.layout f S.variant salt root b v', k ∈ K)
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Fin tau × Fin (2 ^ kappa) → Digest lambda))) :
    pruneAt K (appendHistory
        (treeHistory S.layout (exchanged S.layout f S.variant salt root b v') S.variant salt root (fun _ => root)
          (tau * 2 ^ kappa - 1) ++ ciphers) (mapResult (leafSwap S salt f root b v') out)).cipherHistory =
      pruneAt K (appendHistory (treeHistory S.layout f S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1) ++ ciphers)
        out).cipherHistory := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hκ : S.layout.key (S.layout.output (nodeBlock S.layout f S.variant salt root b)) ∈ K :=
    hK _ (by simp [exchangedKeys])
  have hκ' : S.layout.key (S.layout.output v') ∈ K := hK _ (by simp [exchangedKeys])
  simp only [appendHistory, mapResult, pruneAt_append]
  rw [pruneAt_map K _ (fun k => ?_) (fun k hk => ?_),
    ← pruneAt_of_subset K _ hK (treeHistory S.layout (exchanged S.layout f S.variant salt root b v') _ _ _ _ _),
    treeHistory_exchanged S.layout hin hl (tau * 2 ^ kappa) hL f S.variant salt root (fun _ => root) b hb hbL v' hp hp' G1 G2 G3 G4
      (tau * 2 ^ kappa - 1) (by omega), pruneAt_of_subset K _ hK]
  · unfold leafSwap
    by_cases h1 : k = S.layout.key (S.layout.output (nodeBlock S.layout f S.variant salt root b))
    · subst h1; rw [Equiv.swap_apply_left]; exact ⟨fun _ => hκ, fun _ => hκ'⟩
    · by_cases h2 : k = S.layout.key (S.layout.output v')
      · subst h2; rw [Equiv.swap_apply_right]; exact ⟨fun _ => hκ', fun _ => hκ⟩
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · unfold leafSwap
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hk (h ▸ hκ)) (fun h => hk (h ▸ hκ'))

end Exchange

end
end SDitH.Proofs.CommitRunLeaf
