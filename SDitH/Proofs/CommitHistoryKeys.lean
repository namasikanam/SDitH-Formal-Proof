import SDitH.Proofs.RunKeys
import SDitH.Proofs.CommitRunExchange

/-! The keys the commitment run records. The expansion records the keys of
the expanded nodes, and the rest queries only the leaves' keys, so every
entry the commitment run records over its starting history is at the key of
a node of the tree. -/

namespace SDitH.Proofs.CommitHistoryKeys

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open HiddenLeafNode TreeRunClosed CommitPhaseExchange CommitRunExchange RunKeys
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The expansion records the keys of the expanded nodes. -/
theorem treeHistory_key (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (family : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root : Bits lambda)
    (initial : Nat → Seed lambda) :
    ∀ (k : Nat) (e : Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)),
      e ∈ treeHistory layout family variant salt root initial k →
      ∃ c, 1 ≤ c ∧ c ≤ k ∧ e.key = layout.key (Spec.SeedTree.node (treeExpand layout family variant salt) root c) := by
  intro k
  induction k with
  | zero =>
    intro e he
    simp [treeHistory] at he
  | succ k ih =>
    intro e he
    simp only [treeHistory, List.mem_cons] at he
    rcases he with rfl | rfl | he
    · refine ⟨k + 1, by omega, le_rfl, ?_⟩
      show layout.key (Spec.SeedTree.run (treeExpand layout family variant salt) root initial k (k + 1)) = _
      rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)]
    · refine ⟨k + 1, by omega, le_rfl, ?_⟩
      show layout.key (Spec.SeedTree.run (treeExpand layout family variant salt) root initial k (k + 1)) = _
      rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)]
    · obtain ⟨c, h1, hk, hc⟩ := ih e he
      exact ⟨c, h1, by omega, hc⟩

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)

/-- Every entry the commitment run records over its starting history is at
the key of a node of the tree. -/
theorem commitRun_keys (f : Family (Bits lambda) (Bits lambda)) (root : Bits lambda)
    (table : List Bool → Option (Out lambda s wit rnd)) (hashes : List (List Bool × Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd)))
    (hout : out ∈ (runFixed procedure f (commitBudget tau kappa) (commitProgram S salt root witness) table hashes ciphers
      log).support) :
    ∀ e ∈ out.cipherHistory, e ∈ ciphers ∨
      ∃ c, 1 ≤ c ∧ c < 2 * (tau * 2 ^ kappa) ∧
        e.key = S.layout.key (Spec.SeedTree.node (treeExpand S.layout f S.variant salt) root c) := by
  have hpos : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  have hsub : tau * 2 ^ kappa - 1 + 1 = tau * 2 ^ kappa := Nat.sub_add_cancel hpos
  rw [commitRun_eq] at hout
  intro e he
  rcases runFixed_keys _ f _ _ (queriesIn_commitRest S salt witness _) _ _ _ _ out hout e he with hmem | hS
  · rcases List.mem_append.mp hmem with htree | hcip
    · obtain ⟨c, h1, hk, hc⟩ := treeHistory_key S.layout f S.variant salt root (fun _ => root) _ e htree
      exact Or.inr ⟨c, h1, by omega, hc⟩
    · exact Or.inl hcip
  · obtain ⟨ex, i, hκ⟩ := hS
    have hleaf := SDitH.Proofs.SeedTree.leafAddress_bounds ex i
    have hval : (leafNode ex i).val = Spec.SeedTree.leafAddress ex i := rfl
    refine Or.inr ⟨(leafNode ex i).val, by omega, by omega, ?_⟩
    rw [hκ, SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)]

end
end SDitH.Proofs.CommitHistoryKeys
