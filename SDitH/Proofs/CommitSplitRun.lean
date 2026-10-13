import SDitH.Proofs.CommitDecomposition
import SDitH.Proofs.RunBind
import SDitH.Spec.SharedScheme

/-! The split run of the commitment. The witness-free prefix is bounded by
the commitment budget less one and the tail by one, so the traced run of
the commitment program with the commitment budget is the prefix's run
continued by the tail's run; in the shared world, the signer's run of the
commitment with any witness is the common prefix run followed by that
witness's tail. -/

namespace SDitH.Proofs.CommitSplitRun

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives
open Spec.SharedScheme Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The prefix's budget: the commitment budget less the lines query. -/
def prefixBudget (tau kappa : Nat) : Nat :=
  2 * (tau * 2 ^ kappa - 1) + 2 * (Spec.SharedSlopeExec.allPairs tau kappa).length + tau + 3

theorem commitBudget_eq (tau kappa : Nat) : commitBudget tau kappa = prefixBudget tau kappa + 1 := by
  unfold commitBudget prefixBudget
  omega

/-- The witness-free prefix is bounded by the prefix budget. -/
theorem commitPrefix_bounded {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) :
    Bounded (prefixBudget tau kappa) (commitPrefix S salt root) := by
  unfold commitPrefix prefixBudget
  refine HashCipherProgram.bounded_mono _ _ _ (by omega)
    (HashCipherProgram.bounded_bind _ _ (2 * (tau * 2 ^ kappa - 1))
      (2 * (Spec.SharedSlopeExec.allPairs tau kappa).length + (tau + 3))
      (SharedSigner.treeThrough_bounded S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes => ?_)
  refine HashCipherProgram.bounded_mono _ _ _ (by rw [Nat.mul_comm])
    (HashCipherProgram.bounded_bind _ _ ((Spec.SharedSlopeExec.allPairs tau kappa).length * 2) (tau + 3)
      (SharedSigner.collect_bounded _ 2 (fun pair => SharedSigner.commitCall_bounded S.layout _ S.variant salt _ _) _ _)
      fun commits => ?_)
  refine HashCipherProgram.bounded_mono _ _ _ (by simp [List.length_finRange])
    (HashCipherProgram.bounded_bind _ _ ((List.finRange tau).length * 1) 3
      (SharedSigner.collect_bounded _ 1 (fun e => SharedSigner.hashCall_bounded _) _ _) fun rowHashes => ?_)
  intro _ _ _
  trivial

/-- The tail is a single query. -/
theorem commitTail_bounded {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
    (data : PrefixData lambda tau kappa s wit rnd) : Bounded 1 (commitTail S salt witness data) := by
  intro _
  trivial

/-- The traced run of the commitment program is the prefix's run continued
by the tail's run. -/
theorem runFixed_commit_split {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) (witness : Fin wit → ZMod 2)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure family (commitBudget tau kappa) (commitProgram S salt root witness) table hashes ciphers log =
      (runFixed procedure family (prefixBudget tau kappa) (commitPrefix S salt root) table hashes ciphers log).bind
        (continueRun family 1 (commitTail S salt witness)) := by
  rw [commitBudget_eq, commitProgram_eq]
  exact runFixed_bind family (prefixBudget tau kappa) 1 (commitPrefix S salt root) (commitTail S salt witness)
    (commitPrefix_bounded S salt root) (commitTail_bounded S salt witness) table hashes ciphers log

/-- In the shared world, the signer's commitment run is the common prefix run
followed by the witness's tail. -/
theorem runProgram_commit_split {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) (witness : Fin wit → ZMod 2)
    (world : World lambda s wit rnd) :
    runProgram (commitBudget tau kappa) (commitProgram S salt root witness) world =
      ((runFixed procedure world.family (prefixBudget tau kappa) (commitPrefix S salt root) world.hashTable
          world.hashHistory world.cipherHistory world.trace).bind (continueRun world.family 1 (commitTail S salt witness))).map
        fun out => (out.state, ⟨world.family, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩) := by
  unfold runProgram
  rw [runFixed_commit_split]

end
end SDitH.Proofs.CommitSplitRun
