import SDitH.Proofs.RunCongr
import SDitH.Proofs.CommitDecomposition
import SDitH.Proofs.TreeHistoryExchange

/-! The commitment phase after the tree expansion. The commitment program is
the expansion followed by a rest: the leaf commitments, the row hashes and
the four chain queries. The rest queries the cipher only at the leaves'
keys, and it reads the tree only at the leaves except in its final value,
so replacing an internal node's value turns it into the rest followed by a
pure finish that sets that node in the committed tree. -/

namespace SDitH.Proofs.CommitPhaseExchange

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.HashCipherProgram Spec.SeedPrimitives Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out Mask)
open RunCongr CommitDecomposition PosteriorPrune
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {lambda tau kappa s wit rnd : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)

/-- The four chain queries and the committed value. -/
def commitFour (nodes : Nat → Seed lambda) (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda)
    (rowHashes : Fin tau → Digest lambda) : SignerProgram lambda s wit rnd (Committed F lambda tau kappa s wit rnd) :=
  Program.hash (outerString salt rowHashes) fun outer =>
    Program.hash (Spec.BLCHashChain.auxQuery outer.1 (Spec.BLCHashChain.sourceTail S.encoding
        (Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow
          (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)))))
      fun auxiliary =>
      Program.hash (maskInput auxiliary.1) fun maskAnswer =>
        Program.hash (Spec.BLCHashChain.linesQuery auxiliary.1 (S.linesTail
            (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
              (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
              maskAnswer.2 witness).plainCheck
            (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
              (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
              maskAnswer.2 witness).baseCheck
            (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
              (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
              maskAnswer.2 witness).witnessCorrection)) fun lines =>
          Program.done
            ⟨⟨(Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
                (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                maskAnswer.2 witness).witnessLines,
              (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
                (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                maskAnswer.2 witness).randomnessLines,
              lines.1, ⟨fun a => nodes a.val, fun e i => commits (e, i)⟩,
              ⟨Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow
                  (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)),
                (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
                  (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                  maskAnswer.2 witness).plainCheck,
                (Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow
                  (Spec.BLCCommit.randomTable S.p salt (fun e i => nodes (leafNode e i).val) S.randomCount S.enough)
                  maskAnswer.2 witness).witnessCorrection⟩⟩,
              fun e i => nodes (leafNode e i).val, rowHashes, outer.1, auxiliary.1, maskAnswer.2⟩

/-- The row hashes and the four chain queries. -/
def commitTail (nodes : Nat → Seed lambda) (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) :
    SignerProgram lambda s wit rnd (Committed F lambda tau kappa s wit rnd) :=
  bind (collect (fun e => hashCall (Spec.BAVCBinding.rowQuery (fun e i => commits (e, i)) e)) (List.finRange tau)
    fun _ => fun _ => false) fun rowHashes => commitFour S salt witness nodes commits rowHashes

/-- The rest of the commitment program after the tree expansion. -/
def commitRest (nodes : Nat → Seed lambda) : SignerProgram lambda s wit rnd (Committed F lambda tau kappa s wit rnd) :=
  bind (collect (fun pair : Fin tau × Fin (2 ^ kappa) =>
      commitCall S.layout (tau * 2 ^ kappa) S.variant salt (nodes (leafNode pair.1 pair.2).val)
        (Spec.SeedTree.leafOffset pair.1 pair.2))
      (Spec.SharedSlopeExec.allPairs tau kappa) fun _ => fun _ => false) fun commits => commitTail S salt witness nodes commits

/-- The commitment program is the expansion followed by the rest. -/
theorem commitProgram_eq (root : Bits lambda) :
    commitProgram S salt root witness =
      bind (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) (commitRest S salt witness) :=
  rfl

/-- The leaves' keys of a tree. -/
def leafKeys (nodes : Nat → Seed lambda) : Set (Bits lambda) :=
  {κ | ∃ (e : Fin tau) (i : Fin (2 ^ kappa)), κ = S.layout.key (nodes (leafNode e i).val)}

section Queries

variable {A B : Type*} (K : Set (Bits lambda))

theorem queriesIn_collect {ι : Type*} [DecidableEq ι] (call : ι → SignerProgram lambda s wit rnd B)
    (h : ∀ i, QueriesIn K (call i)) : ∀ (l : List ι) (acc : ι → B), QueriesIn K (collect call l acc) := by
  intro l
  induction l with
  | nil => intro acc; trivial
  | cons k rest ih => intro acc; exact queriesIn_bind K _ _ (h k) fun v => ih _

theorem queriesIn_hashCall (input : List Bool) :
    QueriesIn K (hashCall (lambda := lambda) (s := s) (wit := wit) (rnd := rnd) input) := fun _ => trivial

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
theorem queriesIn_commitCall (leafCount : Nat) (seed : Bits lambda) (index : Nat) (hk : S.layout.key seed ∈ K) :
    QueriesIn K (commitCall (s := s) (wit := wit) (rnd := rnd) S.layout leafCount S.variant salt seed index) :=
  queriesIn_bind K _ _ (And.intro hk fun _ => And.intro hk fun _ => trivial) fun _ => trivial

theorem queriesIn_commitFour (nodes : Nat → Seed lambda) (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda)
    (rowHashes : Fin tau → Digest lambda) : QueriesIn K (commitFour S salt witness nodes commits rowHashes) :=
  fun _ _ _ _ => trivial

theorem queriesIn_commitTail (nodes : Nat → Seed lambda) (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) :
    QueriesIn K (commitTail S salt witness nodes commits) :=
  queriesIn_bind K _ _ (queriesIn_collect K _ (fun _ => queriesIn_hashCall K _) _ _) fun rowHashes =>
    queriesIn_commitFour S salt witness K nodes commits rowHashes

/-- The rest queries the cipher only at the leaves' keys. -/
theorem queriesIn_commitRest (nodes : Nat → Seed lambda) : QueriesIn (leafKeys S nodes) (commitRest S salt witness nodes) := by
  unfold commitRest
  refine queriesIn_bind _ _ _ (queriesIn_collect _ _ (fun pair : Fin tau × Fin (2 ^ kappa) => ?_) _ _)
    fun commits => queriesIn_commitTail S salt witness _ nodes commits
  exact queriesIn_commitCall S salt (leafKeys S nodes) (tau * 2 ^ kappa) (nodes (leafNode pair.1 pair.2).val)
    (Spec.SeedTree.leafOffset pair.1 pair.2) ⟨pair.1, pair.2, rfl⟩

end Queries

section Update

/-- The committed value with one node of its tree set. -/
def setTree (b : Nat) (x : Seed lambda) (c : Committed F lambda tau kappa s wit rnd) : Committed F lambda tau kappa s wit rnd :=
  { c with result := { c.result with key := { c.result.key with tree := fun a => if a.val = b then x else c.result.key.tree a } } }

variable (nodes : Nat → Seed lambda) (b : Nat) (x : Seed lambda) (hb : ∀ (e : Fin tau) (i : Fin (2 ^ kappa)), (leafNode e i).val ≠ b)

omit [NeZero tau] in
include hb in
theorem leaves_update :
    (fun (e : Fin tau) (i : Fin (2 ^ kappa)) => Function.update nodes b x (leafNode e i).val) =
      fun e i => nodes (leafNode e i).val := by
  funext e i
  exact Function.update_of_ne (hb e i) _ _

include hb in
/-- The four chain queries with an internal node replaced: the same queries
with the node set in the committed tree. -/
theorem commitFour_update (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) (rowHashes : Fin tau → Digest lambda) :
    commitFour S salt witness (Function.update nodes b x) commits rowHashes =
      bind (commitFour S salt witness nodes commits rowHashes) fun c => .done (setTree b x c) := by
  have hleaf := leaves_update nodes b x hb
  have htree : (fun a : NodeAddress tau (2 ^ kappa) => Function.update nodes b x a.val) =
      fun a => if a.val = b then x else nodes a.val := by
    funext a
    by_cases h : a.val = b
    · rw [h, Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne h, if_neg h]
  simp only [commitFour, Spec.HashCipherProgram.bind, hleaf, setTree, htree]

include hb in
theorem commitTail_update (commits : Fin tau × Fin (2 ^ kappa) → Digest lambda) :
    commitTail S salt witness (Function.update nodes b x) commits =
      bind (commitTail S salt witness nodes commits) fun c => .done (setTree b x c) := by
  unfold commitTail
  rw [bind_assoc]
  congr 1
  funext rowHashes
  exact commitFour_update S salt witness nodes b x hb commits rowHashes

include hb in
/-- The rest with an internal node replaced: the rest with the node set in
the committed tree. -/
theorem commitRest_update :
    commitRest S salt witness (Function.update nodes b x) =
      bind (commitRest S salt witness nodes) fun c => .done (setTree b x c) := by
  unfold commitRest
  have hcalls : (fun pair : Fin tau × Fin (2 ^ kappa) =>
      commitCall (s := s) (wit := wit) (rnd := rnd) S.layout (tau * 2 ^ kappa) S.variant salt
        (Function.update nodes b x (leafNode pair.1 pair.2).val) (Spec.SeedTree.leafOffset pair.1 pair.2)) =
      fun pair => commitCall S.layout (tau * 2 ^ kappa) S.variant salt (nodes (leafNode pair.1 pair.2).val)
        (Spec.SeedTree.leafOffset pair.1 pair.2) := by
    funext pair
    rw [Function.update_of_ne (hb pair.1 pair.2)]
  rw [hcalls, bind_assoc]
  congr 1
  funext commits
  exact commitTail_update S salt witness nodes b x hb commits

end Update

end
end SDitH.Proofs.CommitPhaseExchange
