import SDitH.Proofs.SharedSigner

/-! The commitment program's decomposition into a witness-free prefix and a
witness-dependent tail. The prefix is the tree expansion, the leaf
commitments, the row hashes and the outer, auxiliary and mask queries,
returning their results; the tail is the lines query and the committed
result. The commitment program with any witness is the prefix bound to
that witness's tail, by associativity of the program bind. The honest
signer and the simulator therefore share the prefix exactly and differ
only in the tail. -/

namespace SDitH.Proofs.CommitDecomposition

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives
open Spec.SlopeConsistencyGame (Out)

noncomputable section

variable {I D K B : Type*}

/-- Associativity of the program bind. -/
theorem bind_assoc {A B' C : Type*} (p : Program I D K B A) (f : A → Program I D K B B')
    (g : B' → Program I D K B C) :
    Spec.HashCipherProgram.bind (Spec.HashCipherProgram.bind p f) g =
      Spec.HashCipherProgram.bind p (fun a => Spec.HashCipherProgram.bind (f a) g) := by
  induction p with
  | done value => rfl
  | hash input next ih =>
    simp only [Spec.HashCipherProgram.bind]
    congr 1
    funext answer
    exact ih answer
  | cipher request next ih =>
    simp only [Spec.HashCipherProgram.bind]
    congr 1
    funext answer
    exact ih answer

variable {lambda tau kappa s wit rnd : Nat}

/-- The data produced by the witness-free prefix: tree nodes, leaf
commitments, row hashes and the outer, auxiliary and mask answers. -/
abbrev PrefixData (lambda tau kappa s wit rnd : Nat) :=
  (Nat → Seed lambda) × (Fin tau × Fin (2 ^ kappa) → Digest lambda) × (Fin tau → Digest lambda) ×
    Out lambda s wit rnd × Out lambda s wit rnd × Out lambda s wit rnd

/-- The witness-free prefix of the commitment program. -/
def commitPrefix {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt root : Bits lambda) : SignerProgram lambda s wit rnd (PrefixData lambda tau kappa s wit rnd) :=
  Spec.HashCipherProgram.bind (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes =>
    Spec.HashCipherProgram.bind (collect (fun pair : Fin tau × Fin (2 ^ kappa) =>
        commitCall S.layout (tau * 2 ^ kappa) S.variant salt (nodes (leafNode pair.1 pair.2).val)
          (Spec.SeedTree.leafOffset pair.1 pair.2))
        (Spec.SharedSlopeExec.allPairs tau kappa) fun _ => fun _ => false) fun commits =>
      Spec.HashCipherProgram.bind (collect (fun e => hashCall (Spec.BAVCBinding.rowQuery (fun e i => commits (e, i)) e))
          (List.finRange tau) fun _ => fun _ => false) fun rowHashes =>
        Program.hash (outerString salt rowHashes) fun outer =>
          Program.hash (Spec.BLCHashChain.auxQuery outer.1 (Spec.BLCHashChain.sourceTail S.encoding
              (Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow
                (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)))))
            fun auxiliary =>
            Program.hash (maskInput auxiliary.1) fun maskAnswer =>
              Program.done (nodes, commits, rowHashes, outer, auxiliary, maskAnswer)

/-- The witness-dependent tail: the lines query and the committed result. -/
def commitTail {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (S : SignerSetting F lambda tau kappa s wit rnd)
    (salt : Bits lambda) (witness : Fin wit → ZMod 2) (data : PrefixData lambda tau kappa s wit rnd) :
    SignerProgram lambda s wit rnd (Committed F lambda tau kappa s wit rnd) :=
  let nodes := data.1
  let commits := data.2.1
  let rowHashes := data.2.2.1
  let outer := data.2.2.2.1
  let auxiliary := data.2.2.2.2.1
  let maskAnswer := data.2.2.2.2.2
  let random := Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough
  let arithmetic := Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow random maskAnswer.2 witness
  Program.hash (Spec.BLCHashChain.linesQuery auxiliary.1
      (S.linesTail arithmetic.plainCheck arithmetic.baseCheck arithmetic.witnessCorrection)) fun lines =>
    Program.done
      ⟨⟨arithmetic.witnessLines, arithmetic.randomnessLines, lines.1, ⟨fun a => nodes a.val, fun e i => commits (e, i)⟩,
        ⟨Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow random),
          arithmetic.plainCheck, arithmetic.witnessCorrection⟩⟩,
        fun e i => nodes (leafNode e i).val, rowHashes, outer.1, auxiliary.1, maskAnswer.2⟩

/-- The commitment program is the prefix bound to the witness's tail. -/
theorem commitProgram_eq {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) (witness : Fin wit → ZMod 2) :
    commitProgram S salt root witness =
      Spec.HashCipherProgram.bind (commitPrefix S salt root) (commitTail S salt witness) := by
  unfold commitProgram commitPrefix
  rw [bind_assoc]
  congr 1
  funext nodes
  rw [bind_assoc]
  congr 1
  funext commits
  rw [bind_assoc]
  congr 1

end
end SDitH.Proofs.CommitDecomposition
