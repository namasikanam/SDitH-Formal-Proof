import SDitH.Spec.SharedScheme
import SDitH.Spec.BLCCommit

/-! The honest signer's commitment phase as an executed hash/cipher program
in the shared model: Algorithm 7's complete seed-tree expansion and leaf
commitments as cipher calls, its row and outer hashes, then Algorithm 10's
PRG table, corrections, Hashaux, the consistency mask read from the mask
oracle at the auxiliary digest, the commit arithmetic and Hashlines. The
hash, cipher and consistency expansion are the shared oracles; only the PRG
is a supplied function. The Hashlines tail is a parameter: the literal
signer appends the witness correction, which the verifier's chain omits.
No PIOP, retry or opening step is included here. -/

namespace SDitH.Spec.SharedSigner

open BAVC DomainSeparation BAVCChainInputs HashCipherProgram SeedPrimitives
open Spec.SlopeConsistencyGame (Out Mask)
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

abbrev SignerProgram (lambda s wit rnd : Nat) (A : Type*) :=
  Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A

/-- ExpandSeed's two Enc* calls through the layout, left output first. -/
def expandCall (layout : BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (address : Nat) (seed : Bits lambda) :
    SignerProgram lambda s wit rnd (Bits lambda × Bits lambda) :=
  Program.cipher (.encrypt (layout.key seed) (layout.input (cipherInput variant salt address false))) fun left =>
    Program.cipher (.encrypt (layout.key seed) (layout.input (cipherInput variant salt address true))) fun right =>
      Program.done (layout.output left, layout.output right)

/-- CommitSeed: ExpandSeed at the leaf-count-shifted address, concatenated. -/
def commitCall (layout : BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (leafCount : Nat)
    (variant : Grinding) (salt seed : Bits lambda) (index : Nat) : SignerProgram lambda s wit rnd (Digest lambda) :=
  bind (expandCall layout variant salt (leafCount + index) seed) fun pair => Program.done (concatenate pair.1 pair.2)

/-- Algorithm 7 lines 1–3: the increasing-index expansion loop, reading each
parent and writing both children. -/
def treeThrough (layout : BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt root : Bits lambda) (initial : Nat → Seed lambda) :
    Nat → SignerProgram lambda s wit rnd (Nat → Seed lambda)
  | 0 => Program.done (Function.update initial 1 root)
  | steps + 1 => bind (treeThrough layout variant salt root initial steps) fun tree =>
      bind (expandCall layout variant salt (steps + 1) (tree (steps + 1))) fun children =>
        Program.done (Function.update (Function.update tree (2 * (steps + 1)) children.1)
          (2 * (steps + 1) + 1) children.2)

/-- Run one program per listed index in order, recording each value. -/
def collect {ι B : Type*} [DecidableEq ι] (call : ι → SignerProgram lambda s wit rnd B) :
    List ι → (ι → B) → SignerProgram lambda s wit rnd (ι → B)
  | [], acc => Program.done acc
  | k :: rest, acc => bind (call k) fun value => collect call rest (Function.update acc k value)

/-- One hash query, read by its digest component. -/
def hashCall (input : List Bool) : SignerProgram lambda s wit rnd (Digest lambda) :=
  Program.hash input fun answer => Program.done answer.1

/-- The signer's Hashlines payload after the auxiliary digest. -/
abbrev LinesTail (tau kappa s wit : Nat) :=
  (Fin s → ZMod 2) → (Fin s → Fin tau → Fin kappa → ZMod 2) → (Fin wit → ZMod 2) → List Bool

/-- Algorithm 10's literal payload: plain check, base and witness correction,
as in `ConcreteBLC.linesPayload`. -/
def literalLinesTail (encoding : ConcreteBLC.Serialization tau kappa s) : LinesTail tau kappa s wit :=
  fun plain base witnessCorrection =>
    encoding.vector plain ++ encoding.base base ++ encoding.vector witnessCorrection

/-- The tail hashed by `SharedScheme.verifyProgram`, which omits the witness correction. -/
def verifierLinesTail (encoding : ConcreteBLC.Serialization tau kappa s) : LinesTail tau kappa s wit :=
  fun plain base _ => encoding.vector plain ++ encoding.base base

structure SignerSetting (F : Type*) (lambda tau kappa s wit rnd : Nat) where
  layout : BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)
  variant : Grinding
  encoding : ConcreteBLC.Serialization tau kappa s
  /-- Only the PRG of these primitives is read; hash, cipher and consistency
  expansion are the shared oracles. -/
  p : BLCCommit.Primitives lambda tau kappa s wit rnd
  randomCount : Nat
  enough : s + (wit + rnd) ≤ 8 * randomCount
  xi : F
  linesTail : LinesTail tau kappa s wit

/-- Algorithm 10's result together with the seeds, digests and mask it used. -/
structure Committed (F : Type*) [CommRing F] (lambda tau kappa s wit rnd : Nat) where
  result : BLCCommit.Result F lambda tau kappa s wit rnd
  seeds : Fin tau → Fin (2 ^ kappa) → Seed lambda
  rowHashes : Fin tau → Digest lambda
  hcom : Digest lambda
  auxiliary : Digest lambda
  mask : Mask s wit rnd

/-- Algorithm 7 lines 1–11 and Algorithm 10 with the shared oracles. The
leaf commitments are made in `allPairs` order and the row hashes in
execution order; the outer, auxiliary, mask and lines queries follow. -/
def commitProgram {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) (witness : Fin wit → ZMod 2) :
    SignerProgram lambda s wit rnd (Committed F lambda tau kappa s wit rnd) :=
  bind (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes =>
    bind (collect (fun pair : Fin tau × Fin (2 ^ kappa) =>
        commitCall S.layout (tau * 2 ^ kappa) S.variant salt (nodes (leafNode pair.1 pair.2).val)
          (SeedTree.leafOffset pair.1 pair.2))
        (SharedSlopeExec.allPairs tau kappa) fun _ => fun _ => false) fun commits =>
      bind (collect (fun e => hashCall (BAVCBinding.rowQuery (fun e i => commits (e, i)) e)) (List.finRange tau)
          fun _ => fun _ => false) fun rowHashes =>
        Program.hash (outerString salt rowHashes) fun outer =>
          Program.hash (BLCHashChain.auxQuery outer.1 (BLCHashChain.sourceTail S.encoding
              (BLCCommit.positiveCorrections (BLC.correction GrayCode.grayFieldRow
                (BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)))))
            fun auxiliary =>
            Program.hash (maskInput auxiliary.1) fun maskAnswer =>
              Program.hash (BLCHashChain.linesQuery auxiliary.1 (S.linesTail
                  (BLC.commitArithmetic S.xi GrayCode.grayFieldRow
                    (BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                    maskAnswer.2 witness).plainCheck
                  (BLC.commitArithmetic S.xi GrayCode.grayFieldRow
                    (BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                    maskAnswer.2 witness).baseCheck
                  (BLC.commitArithmetic S.xi GrayCode.grayFieldRow
                    (BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                    maskAnswer.2 witness).witnessCorrection)) fun lines =>
                Program.done
                  ⟨⟨(BLC.commitArithmetic S.xi GrayCode.grayFieldRow
                      (BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                      maskAnswer.2 witness).witnessLines,
                    (BLC.commitArithmetic S.xi GrayCode.grayFieldRow
                      (BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                      maskAnswer.2 witness).randomnessLines,
                    lines.1, ⟨fun a => nodes a.val, fun e i => commits (e, i)⟩,
                    ⟨BLCCommit.positiveCorrections (BLC.correction GrayCode.grayFieldRow
                        (BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)),
                      (BLC.commitArithmetic S.xi GrayCode.grayFieldRow
                        (BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                        maskAnswer.2 witness).plainCheck,
                      (BLC.commitArithmetic S.xi GrayCode.grayFieldRow
                        (BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                        maskAnswer.2 witness).witnessCorrection⟩⟩,
                    fun e i => nodes (leafNode e i).val, rowHashes, outer.1, auxiliary.1, maskAnswer.2⟩

/-- Tree expansion, leaf commitments, row hashes, then the four chain queries. -/
def commitBudget (tau kappa : Nat) : Nat :=
  2 * (tau * 2 ^ kappa - 1) + 2 * (SharedSlopeExec.allPairs tau kappa).length + tau + 4

end
end SDitH.Spec.SharedSigner
