import SDitH.Proofs.PrefixLinesFresh

/-! The prefix's head split. The prefix is the head (tree expansion, leaf
commitments, row hashes) bound to its last three queries; the head is
bounded by the prefix budget less three and the last three queries by
three, so the prefix's traced run is the head's run continued by the
three queries' run. Together with the stored-lines-input argument this
locates the lines input's freshness after any prefix run. -/

namespace SDitH.Proofs.PrefixHeadSplit

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives
open Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition CommitSplitRun RunBind PrefixLinesFresh

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The head: tree expansion, leaf commitments and row hashes. -/
def prefixHead {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt root : Bits lambda) : SignerProgram lambda s wit rnd (HeadData lambda tau kappa) :=
  Spec.HashCipherProgram.bind (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes =>
    Spec.HashCipherProgram.bind (collect (fun pair : Fin tau × Fin (2 ^ kappa) =>
        commitCall S.layout (tau * 2 ^ kappa) S.variant salt (nodes (leafNode pair.1 pair.2).val)
          (Spec.SeedTree.leafOffset pair.1 pair.2))
        (Spec.SharedSlopeExec.allPairs tau kappa) fun _ => fun _ => false) fun commits =>
      Spec.HashCipherProgram.bind (collect (fun e => hashCall (Spec.BAVCBinding.rowQuery (fun e i => commits (e, i)) e))
          (List.finRange tau) fun _ => fun _ => false) fun rowHashes =>
        Program.done (nodes, commits, rowHashes)

/-- The prefix is the head bound to its last three queries. -/
theorem commitPrefix_eq_head {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) :
    commitPrefix S salt root = Spec.HashCipherProgram.bind (prefixHead S salt root) (prefixTail S salt) := by
  unfold commitPrefix prefixHead
  rw [bind_assoc]
  congr 1
  funext nodes
  rw [bind_assoc]
  congr 1
  funext commits
  rw [bind_assoc]
  rfl

/-- The head's budget: the prefix budget less the last three queries. -/
def headBudget (tau kappa : Nat) : Nat :=
  2 * (tau * 2 ^ kappa - 1) + 2 * (Spec.SharedSlopeExec.allPairs tau kappa).length + tau

theorem prefixBudget_eq (tau kappa : Nat) : prefixBudget tau kappa = headBudget tau kappa + 3 := by
  unfold prefixBudget headBudget
  omega

theorem prefixHead_bounded {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) :
    Bounded (headBudget tau kappa) (prefixHead S salt root) := by
  unfold prefixHead headBudget
  refine HashCipherProgram.bounded_mono _ _ _ (by omega)
    (HashCipherProgram.bounded_bind _ _ (2 * (tau * 2 ^ kappa - 1))
      (2 * (Spec.SharedSlopeExec.allPairs tau kappa).length + tau)
      (SharedSigner.treeThrough_bounded S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes => ?_)
  refine HashCipherProgram.bounded_mono _ _ _ (by rw [Nat.mul_comm])
    (HashCipherProgram.bounded_bind _ _ ((Spec.SharedSlopeExec.allPairs tau kappa).length * 2) tau
      (SharedSigner.collect_bounded _ 2 (fun pair => SharedSigner.commitCall_bounded S.layout _ S.variant salt _ _) _ _)
      fun commits => ?_)
  refine HashCipherProgram.bounded_mono _ _ _ (by simp [List.length_finRange])
    (HashCipherProgram.bounded_bind _ _ ((List.finRange tau).length * 1) 0
      (SharedSigner.collect_bounded _ 1 (fun e => SharedSigner.hashCall_bounded _) _ _) fun rowHashes => ?_)
  trivial

theorem prefixTail_bounded {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (head : HeadData lambda tau kappa) :
    Bounded 3 (prefixTail S salt head) := by
  intro _ _ _
  trivial

/-- The prefix's traced run is the head's run continued by the last three
queries' run. -/
theorem runFixed_prefix_split {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure family (prefixBudget tau kappa) (commitPrefix S salt root) table hashes ciphers log =
      (runFixed procedure family (headBudget tau kappa) (prefixHead S salt root) table hashes ciphers log).bind
        (continueRun family 3 (prefixTail S salt)) := by
  rw [prefixBudget_eq, commitPrefix_eq_head]
  exact runFixed_bind family (headBudget tau kappa) 3 (prefixHead S salt root) (prefixTail S salt)
    (prefixHead_bounded S salt root) (prefixTail_bounded S salt) table hashes ciphers log

end
end SDitH.Proofs.PrefixHeadSplit
