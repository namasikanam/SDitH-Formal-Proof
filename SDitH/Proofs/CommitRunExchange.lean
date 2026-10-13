import SDitH.Proofs.CommitPhaseExchange
import SDitH.Proofs.RunHistoryShift
import SDitH.Proofs.TreeRunClosed

/-! The commitment run under the exchange. The commitment run is the rest's
run from the expansion's tree and history; under the exchange of an
internal node the expansion's tree is the tree with the node replaced, so
the rest is the rest with a finish setting the node, it queries only the
leaves' keys where the exchanged family agrees with the family, and the
starting history only shifts the result's. So the commitment run under
the exchanged family is the commitment run's base (the rest from the
empty history) with the node set and the exchanged expansion's history
appended. -/

namespace SDitH.Proofs.CommitRunExchange

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open RunCongr RunHistoryShift CommitPhaseExchange TreeRunClosed TreeHistoryExchange TreeExchange HiddenLeafNode RunBind
open NodeExchange
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {lambda tau kappa s wit rnd : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)

/-- The rest's budget. -/
def restBudget (tau kappa : Nat) : Nat := 2 * (Spec.SharedSlopeExec.allPairs tau kappa).length + (tau + 4)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem commitBudget_eq : commitBudget tau kappa = 2 * (tau * 2 ^ kappa - 1) + restBudget tau kappa := by
  unfold commitBudget restBudget
  omega

theorem commitRest_bounded (nodes : Nat → Seed lambda) :
    Bounded (restBudget tau kappa) (commitRest S salt witness nodes) := by
  unfold restBudget commitRest
  refine HashCipherProgram.bounded_mono _ _ _ (by rw [Nat.mul_comm])
    (HashCipherProgram.bounded_bind _ _ ((Spec.SharedSlopeExec.allPairs tau kappa).length * 2) (tau + 4)
      (SDitH.Proofs.SharedSigner.collect_bounded _ 2
        (fun pair => SDitH.Proofs.SharedSigner.commitCall_bounded S.layout _ S.variant salt _ _) _ _) fun commits => ?_)
  unfold commitTail
  refine HashCipherProgram.bounded_mono _ _ _ (by simp [List.length_finRange])
    (HashCipherProgram.bounded_bind _ _ ((List.finRange tau).length * 1) 4
      (SDitH.Proofs.SharedSigner.collect_bounded _ 1 (fun _ => SDitH.Proofs.SharedSigner.hashCall_bounded _) _ _)
      fun rowHashes => ?_)
  intro _ _ _ _
  trivial

/-- The commitment run is the rest's run from the expansion's tree and
history. -/
theorem commitRun_eq (f : Family (Bits lambda) (Bits lambda)) (root : Bits lambda)
    (table : List Bool → Option (Out lambda s wit rnd)) (hashes : List (List Bool × Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure f (commitBudget tau kappa) (commitProgram S salt root witness) table hashes ciphers log =
      runFixed procedure f (restBudget tau kappa)
        (commitRest S salt witness
          (Spec.SeedTree.run (treeExpand S.layout f S.variant salt) root (fun _ => root) (tau * 2 ^ kappa - 1)))
        table hashes
        (treeHistory S.layout f S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1) ++ ciphers) log := by
  rw [commitBudget_eq, commitProgram_eq,
    runFixed_bind f _ _ _ _ (SDitH.Proofs.SharedSigner.treeThrough_bounded S.layout S.variant salt root (fun _ => root) _)
      (fun v => commitRest_bounded S salt witness v), tree_run_eq, PMF.pure_bind]
  unfold continueRun
  simp only [Bool.false_or]
  exact (congrArg₂ PMF.map (funext fun out' => rfl) rfl).trans (PMF.map_id _)

section Congr

variable (n₁ n₂ : Nat → Seed lambda) (h : ∀ a, 0 < a → a < 2 * (tau * 2 ^ kappa) → n₁ a = n₂ a)

include h in
theorem commitFour_congr (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) (rowHashes : Fin tau → Digest lambda) :
    commitFour S salt witness n₁ commits rowHashes = commitFour S salt witness n₂ commits rowHashes := by
  have hleaf : (fun (e : Fin tau) (i : Fin (2 ^ kappa)) => n₁ (leafNode e i).val) = fun e i => n₂ (leafNode e i).val := by
    funext e i
    exact h _ (SDitH.Proofs.SeedTree.leafAddress_bounds e i).1 (SDitH.Proofs.SeedTree.leafAddress_bounds e i).2
  have htree : (fun a : NodeAddress tau (2 ^ kappa) => n₁ a.val) = fun a => n₂ a.val := by
    funext a
    exact h _ a.property.1 a.property.2
  simp only [commitFour, hleaf, htree]

include h in
theorem commitTail_congr (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) :
    commitTail S salt witness n₁ commits = commitTail S salt witness n₂ commits := by
  unfold commitTail
  congr 1
  funext rowHashes
  exact commitFour_congr S salt witness n₁ n₂ h commits rowHashes

include h in
/-- The rest depends on the tree only within the allocated addresses. -/
theorem commitRest_congr : commitRest S salt witness n₁ = commitRest S salt witness n₂ := by
  unfold commitRest
  have hcalls : (fun pair : Fin tau × Fin (2 ^ kappa) =>
      commitCall (s := s) (wit := wit) (rnd := rnd) S.layout (tau * 2 ^ kappa) S.variant salt
        (n₁ (leafNode pair.1 pair.2).val) (Spec.SeedTree.leafOffset pair.1 pair.2)) =
      fun pair => commitCall S.layout (tau * 2 ^ kappa) S.variant salt (n₂ (leafNode pair.1 pair.2).val)
        (Spec.SeedTree.leafOffset pair.1 pair.2) := by
    funext pair
    rw [h (leafNode pair.1 pair.2).val (SDitH.Proofs.SeedTree.leafAddress_bounds pair.1 pair.2).1
      (SDitH.Proofs.SeedTree.leafAddress_bounds pair.1 pair.2).2]
  rw [hcalls]
  congr 1
  funext commits
  exact commitTail_congr S salt witness n₁ n₂ h commits

end Congr

section Exchange

variable (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (f : Family (Bits lambda) (Bits lambda)) (root : Bits lambda) (b : Nat) (hb : 1 < b) (hbk : b ≤ tau * 2 ^ kappa - 1)
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

/-- The expansion's tree. -/
def baseTree : Nat → Seed lambda :=
  Spec.SeedTree.run (treeExpand S.layout f S.variant salt) root (fun _ => root) (tau * 2 ^ kappa - 1)

omit [Field F] [Algebra (ZMod 2) F] in
theorem leafCount_pos : 0 < tau * 2 ^ kappa :=
  Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne tau)) (Nat.two_pow_pos kappa)

include hin hl hL hb hbk hp hp' G1 G2 G3 G4 in
/-- The exchanged expansion's tree is the tree with the node replaced. -/
theorem exchanged_tree_eq :
    commitRest S salt witness
        (Spec.SeedTree.run (treeExpand S.layout (exchanged S.layout f S.variant salt root b v') S.variant salt) root
          (fun _ => root) (tau * 2 ^ kappa - 1)) =
      commitRest S salt witness (Function.update (baseTree S salt f root) b (S.layout.output v')) := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hsub : tau * 2 ^ kappa - 1 + 1 = tau * 2 ^ kappa := Nat.sub_add_cancel hpos
  refine commitRest_congr S salt witness _ _ fun a ha0 haL => ?_
  rw [run_exchanged S.layout hin hl (tau * 2 ^ kappa) hL f S.variant salt root (fun _ => root) b hb (by omega) v' hp hp'
    G1 G2 G3 G4 (tau * 2 ^ kappa - 1) (by omega) a ha0 (by omega), Function.update_apply]
  rfl

omit [Field F] [Algebra (ZMod 2) F] in
include hbk G1 G2 G3 in
/-- The exchanged family agrees with the family at the leaves' keys. -/
theorem exchanged_leafKeys : ∀ κ ∈ leafKeys S (baseTree S salt f root),
    exchanged S.layout f S.variant salt root b v' κ = f κ := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hsub : tau * 2 ^ kappa - 1 + 1 = tau * 2 ^ kappa := Nat.sub_add_cancel hpos
  rintro κ ⟨e, i, rfl⟩
  have hleaf := SDitH.Proofs.SeedTree.leafAddress_bounds e i
  have hval' : (leafNode e i).val = Spec.SeedTree.leafAddress e i := rfl
  have hge : tau * 2 ^ kappa ≤ Spec.SeedTree.leafAddress e i := Nat.le_add_right _ _
  have hval : baseTree S salt f root (leafNode e i).val =
      Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root (leafNode e i).val :=
    SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ hleaf.1 (by show _ ≤ 2 * (tau * 2 ^ kappa - 1) + 1; omega)
  rw [hval]
  exact swapNode_apply_of_ne _ _ _ _ _ f _ (G1 _ hleaf.1 hleaf.2 (by show ¬ (_ = b / 2); omega))
    (G2 _ hleaf.1 hleaf.2 (by show ¬ (_ = b); omega)) (G3 _ hleaf.1 hleaf.2)

include hin hl hL hb hbk hp hp' G1 G2 G3 G4 in
/-- The commitment run under the exchange: the base run with the node set
and the exchanged expansion's history appended. -/
theorem commitRun_exchanged (table : List Bool → Option (Out lambda s wit rnd)) (hashes : List (List Bool × Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure (exchanged S.layout f S.variant salt root b v') (commitBudget tau kappa)
        (commitProgram S salt root witness) table hashes ciphers log =
      ((runFixed procedure f (restBudget tau kappa) (commitRest S salt witness (baseTree S salt f root)) table hashes [] log).map
        fun out => { out with state := Spec.HashCipherProgram.bind out.state fun c => .done (setTree b (S.layout.output v') c) }).map
        (appendHistory (treeHistory S.layout (exchanged S.layout f S.variant salt root b v') S.variant salt root (fun _ => root)
          (tau * 2 ^ kappa - 1) ++ ciphers)) := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos
  have hsub : tau * 2 ^ kappa - 1 + 1 = tau * 2 ^ kappa := Nat.sub_add_cancel hpos
  rw [commitRun_eq, exchanged_tree_eq S salt witness hin hl hL f root b hb hbk v' hp hp' G1 G2 G3 G4,
    commitRest_update S salt witness _ b _ (fun e i => by
      have hge : tau * 2 ^ kappa ≤ Spec.SeedTree.leafAddress e i := Nat.le_add_right _ _
      show Spec.SeedTree.leafAddress e i ≠ b
      omega),
    runFixed_bind_done, runFixed_congr_family (leafKeys S (baseTree S salt f root)) f _
      (exchanged_leafKeys S salt f root b hbk v' G1 G2 G3) _ _
      (queriesIn_commitRest S salt witness _),
    runFixed_history_shift, PMF.map_comp, PMF.map_comp]
  rfl

end Exchange

end
end SDitH.Proofs.CommitRunExchange
