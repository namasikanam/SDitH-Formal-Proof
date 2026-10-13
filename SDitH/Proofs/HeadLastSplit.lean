import SDitH.Proofs.PrefixHeadSplit
import SDitH.Proofs.OuterFresh
import SDitH.Proofs.ThreeHashRun

/-! The head split at its last row query. The head is its initial part
(tree expansion, leaf commitments, the row hashes but the last) bound to
the last row query, which updates the row hashes at the last execution;
the initial part is bounded by the head budget less one and the last query
by one. A fresh last row query's run result has the newest trace entry at
that query with the recorded row hash, so a stored outer string over the
recorded row hashes is a mention event. -/

namespace SDitH.Proofs.HeadLastSplit

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives
open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle
open Spec.SlopeConsistencyGame (Out)
open CommitDecomposition RunBind PrefixLinesFresh PrefixHeadSplit CollectLast OuterFresh ThreeHashRun
open scoped Classical

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The head's initial part: tree, commitments and all row hashes but the
last, returning the nodes, commitments and partial row hashes. -/
def headInit {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt root : Bits lambda) : SignerProgram lambda s wit rnd (HeadData lambda tau kappa) :=
  Spec.HashCipherProgram.bind (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes =>
    Spec.HashCipherProgram.bind (collect (fun pair : Fin tau × Fin (2 ^ kappa) =>
        commitCall S.layout (tau * 2 ^ kappa) S.variant salt (nodes (leafNode pair.1 pair.2).val)
          (Spec.SeedTree.leafOffset pair.1 pair.2))
        (Spec.SharedSlopeExec.allPairs tau kappa) fun _ => fun _ => false) fun commits =>
      Spec.HashCipherProgram.bind (collect (fun e => hashCall (Spec.BAVCBinding.rowQuery (fun e i => commits (e, i)) e))
          (List.finRange tau).dropLast fun _ => fun _ => false) fun partialRows =>
        Program.done (nodes, commits, partialRows)

/-- The last row query from the head's initial data. -/
def lastRow (htau : tau ≠ 0) (data : HeadData lambda tau kappa) :
    SignerProgram lambda s wit rnd (HeadData lambda tau kappa) :=
  Spec.HashCipherProgram.bind (hashCall (Spec.BAVCBinding.rowQuery (fun e i => data.2.1 (e, i)) (lastIndex htau)))
    fun value => Program.done (data.1, data.2.1, Function.update data.2.2 (lastIndex htau) value)

/-- The head is its initial part bound to the last row query. -/
theorem prefixHead_eq_last {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) :
    prefixHead S salt root = Spec.HashCipherProgram.bind (headInit S salt root) (lastRow htau) := by
  unfold prefixHead headInit
  rw [bind_assoc]
  congr 1
  funext nodes
  rw [bind_assoc]
  congr 1
  funext commits
  rw [rows_collect_split htau, bind_assoc, bind_assoc]
  congr 1

end
end SDitH.Proofs.HeadLastSplit
