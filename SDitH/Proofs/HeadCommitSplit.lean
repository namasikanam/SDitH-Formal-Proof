import SDitH.Proofs.HeadLastRun
import SDitH.Proofs.CollectLast

/-! The head's initial part split at its last commitment call. The leaf
pairs end with the last execution's last leaf; the commitments'
collection splits there; so the head's initial part is the tree, the
commitments but the last, and the last leaf's first cipher call, followed
by the last leaf's second cipher call (whose output completes the last
commitment) and the partial row hashes. The traced run of the head's
initial part is the run before the last call continued by the run after
it, with exact budgets. -/

namespace SDitH.Proofs.HeadCommitSplit

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open CollectLast HeadLastSplit PrefixHeadSplit RunBind PrefixLinesFresh CommitDecomposition OuterFresh
open scoped Classical

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The leaf pairs are nonempty for a nonzero execution count. -/
theorem allPairs_ne_nil (htau : tau ≠ 0) : Spec.SharedSlopeExec.allPairs tau kappa ≠ [] := by
  intro h
  unfold Spec.SharedSlopeExec.allPairs at h
  rw [List.flatMap_eq_nil_iff] at h
  have := h ⟨0, Nat.pos_of_ne_zero htau⟩ (List.mem_finRange _)
  rw [List.map_eq_nil_iff, List.finRange_eq_nil_iff] at this
  exact absurd this (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos kappa))

/-- The last leaf pair. -/
def lastPair (htau : tau ≠ 0) : Fin tau × Fin (2 ^ kappa) :=
  (Spec.SharedSlopeExec.allPairs tau kappa).getLast (allPairs_ne_nil htau)

/-- The leaf pairs split at the last pair. -/
theorem allPairs_split (htau : tau ≠ 0) :
    (Spec.SharedSlopeExec.allPairs tau kappa).dropLast ++ [lastPair htau] = Spec.SharedSlopeExec.allPairs tau kappa :=
  List.dropLast_append_getLast (allPairs_ne_nil htau)

/-- The commitments' collection splits at the last pair. -/
theorem commit_collect_split {B : Type*} (htau : tau ≠ 0)
    (call : Fin tau × Fin (2 ^ kappa) → SignerProgram lambda s wit rnd B) (acc : Fin tau × Fin (2 ^ kappa) → B) :
    collect call (Spec.SharedSlopeExec.allPairs tau kappa) acc =
      Spec.HashCipherProgram.bind (collect call (Spec.SharedSlopeExec.allPairs tau kappa).dropLast acc) fun acc' =>
        Spec.HashCipherProgram.bind (call (lastPair (kappa := kappa) htau)) fun value =>
          Program.done (Function.update acc' (lastPair (kappa := kappa) htau) value) := by
  conv_lhs => rw [← allPairs_split htau]
  exact collect_append_single call _ (lastPair (kappa := kappa) htau) acc

/-- The address of the last leaf's commitment call. -/
def lastAddress (htau : tau ≠ 0) : Nat :=
  tau * 2 ^ kappa + Spec.SeedTree.leafOffset (lastPair (kappa := kappa) htau).1 (lastPair (kappa := kappa) htau).2

/-- The key of the last leaf's commitment calls from the tree. -/
def lastKey (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (htau : tau ≠ 0)
    (nodes : Nat → Seed lambda) : Bits lambda :=
  layout.key (nodes (leafNode (lastPair (kappa := kappa) htau).1 (lastPair (kappa := kappa) htau).2).val)

/-- The data before the last call: the tree, the commitments but the last,
and the last commitment's left half. -/
abbrev BeforeData (lambda tau kappa : Nat) :=
  (Nat → Seed lambda) × (Fin tau × Fin (2 ^ kappa) → Digest lambda) × Bits lambda

/-- The head's initial part before the last leaf's second cipher call. -/
def headBefore {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) :
    SignerProgram lambda s wit rnd (BeforeData lambda tau kappa) :=
  Spec.HashCipherProgram.bind (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes =>
    Spec.HashCipherProgram.bind (collect (fun pair : Fin tau × Fin (2 ^ kappa) =>
        commitCall S.layout (tau * 2 ^ kappa) S.variant salt (nodes (leafNode pair.1 pair.2).val)
          (Spec.SeedTree.leafOffset pair.1 pair.2))
        (Spec.SharedSlopeExec.allPairs tau kappa).dropLast fun _ => fun _ => false) fun acc' =>
      Program.cipher (.encrypt (lastKey (kappa := kappa) S.layout htau nodes)
          (S.layout.input (cipherInput S.variant salt (lastAddress (kappa := kappa) htau) false))) fun left =>
        Program.done (nodes, acc', S.layout.output left)

/-- The head's initial part after the last leaf's first cipher call: the
second call completing the last commitment, then the partial row hashes. -/
def headAfter {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (v : BeforeData lambda tau kappa) :
    SignerProgram lambda s wit rnd (HeadData lambda tau kappa) :=
  Program.cipher (.encrypt (lastKey (kappa := kappa) S.layout htau v.1)
      (S.layout.input (cipherInput S.variant salt (lastAddress (kappa := kappa) htau) true))) fun right =>
    Spec.HashCipherProgram.bind (collect (fun e => hashCall (Spec.BAVCBinding.rowQuery
        (fun e i => Function.update v.2.1 (lastPair (kappa := kappa) htau) (concatenate v.2.2 (S.layout.output right)) (e, i)) e))
        (List.finRange tau).dropLast fun _ => fun _ => false) fun partialRows =>
      Program.done (v.1, Function.update v.2.1 (lastPair (kappa := kappa) htau) (concatenate v.2.2 (S.layout.output right)), partialRows)

/-- The head's initial part is the part before the last call bound to the
part after it. -/
theorem headInit_eq_split {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) :
    headInit S salt root = Spec.HashCipherProgram.bind (headBefore htau S salt root) (headAfter htau S salt) := by
  unfold headInit headBefore headAfter
  simp only [CommitDecomposition.bind_assoc]
  congr 1
  funext nodes
  rw [commit_collect_split htau]
  simp only [CommitDecomposition.bind_assoc]
  congr 1

/-- The budget before the last call. -/
def beforeBudget (tau kappa : Nat) : Nat :=
  2 * (tau * 2 ^ kappa - 1) + 2 * ((Spec.SharedSlopeExec.allPairs tau kappa).length - 1) + 1

theorem headBudget_split (htau : tau ≠ 0) : headBudget tau kappa - 1 = beforeBudget tau kappa + tau := by
  have hpos : 0 < (Spec.SharedSlopeExec.allPairs tau kappa).length :=
    List.length_pos_of_ne_nil (allPairs_ne_nil htau)
  unfold headBudget beforeBudget
  omega

theorem headBefore_bounded {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) :
    Bounded (beforeBudget tau kappa) (headBefore htau S salt root) := by
  unfold headBefore beforeBudget
  refine HashCipherProgram.bounded_bind _ _ (2 * (tau * 2 ^ kappa - 1))
    (2 * ((Spec.SharedSlopeExec.allPairs tau kappa).length - 1) + 1)
    (SharedSigner.treeThrough_bounded S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes => ?_
  refine HashCipherProgram.bounded_mono _ _ _ (by rw [List.length_dropLast, Nat.mul_comm])
    (HashCipherProgram.bounded_bind _ _ ((Spec.SharedSlopeExec.allPairs tau kappa).dropLast.length * 2) 1
      (SharedSigner.collect_bounded _ 2 (fun pair => SharedSigner.commitCall_bounded S.layout _ S.variant salt _ _) _ _)
      fun acc' => ?_)
  intro _
  trivial

theorem headAfter_bounded {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (v : BeforeData lambda tau kappa) :
    Bounded tau (headAfter htau S salt v) := by
  unfold headAfter
  refine HashCipherProgram.bounded_mono _ _ _
    (show (List.finRange tau).dropLast.length * 1 + 1 ≤ tau by
      simp only [List.length_dropLast, List.length_finRange, Nat.mul_one]; omega) ?_
  intro right
  exact HashCipherProgram.bounded_bind _ _ ((List.finRange tau).dropLast.length * 1) 0
    (SharedSigner.collect_bounded _ 1 (fun e => SharedSigner.hashCall_bounded _) _ _) fun partialRows => trivial

/-- The head's initial run is the run before the last call continued by
the run after it. -/
theorem runFixed_headInit_split {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure family (headBudget tau kappa - 1) (headInit S salt root) table hashes ciphers log =
      (runFixed procedure family (beforeBudget tau kappa) (headBefore htau S salt root) table hashes ciphers log).bind
        (continueRun family tau (headAfter htau S salt)) := by
  rw [headBudget_split htau, headInit_eq_split htau]
  exact runFixed_bind family (beforeBudget tau kappa) tau (headBefore htau S salt root) (headAfter htau S salt)
    (headBefore_bounded htau S salt root) (headAfter_bounded htau S salt) table hashes ciphers log

end
end SDitH.Proofs.HeadCommitSplit
