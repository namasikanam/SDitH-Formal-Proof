import SDitH.Proofs.TreeGoodInduction
import SDitH.Proofs.HiddenLeafNode

/-! The tree expansion's run in closed form. The expansion makes only cipher
calls, so its run against a fixed family is a point: the finished tree is
the seed tree's increasing-index run through the family, and the recorded
entries are the two calls of every expanded node, latest first, over the
starting history. -/

namespace SDitH.Proofs.TreeRunClosed

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family)
open TreeRunEntries TreeGoodInduction RunBind HiddenLeafNode
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The entries recorded by the tree expansion through a number of steps,
latest first. -/
def treeHistory (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (family : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root : Bits lambda)
    (initial : Nat → Seed lambda) : Nat → List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))
  | 0 => []
  | k + 1 =>
      let tree := Spec.SeedTree.run (treeExpand layout family variant salt) root initial k
      Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true)))
          (family (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))) ::
        Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false)))
          (family (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false))) ::
        treeHistory layout family variant salt root initial k

/-- The tree expansion's run is the point at the seed tree's run and the
recorded entries. -/
theorem tree_run_eq (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (family : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root : Bits lambda)
    (initial : Nat → Seed lambda) :
    ∀ (k : Nat) (table : List Bool → Option (Out lambda s wit rnd)) (hashes : List (List Bool × Out lambda s wit rnd))
      (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
      (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))),
      runFixed procedure family (2 * k) (treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root initial k)
          table hashes ciphers log =
        PMF.pure ⟨.done (Spec.SeedTree.run (treeExpand layout family variant salt) root initial k), table, hashes,
          treeHistory layout family variant salt root initial k ++ ciphers, false, log⟩ := by
  intro k
  induction k with
  | zero =>
    intro table hashes ciphers log
    simp only [runFixed, treeThrough, Spec.SeedTree.run, treeHistory, List.nil_append]
  | succ k ih =>
    intro table hashes ciphers log
    rw [runFixed_tree_succ, ih, PMF.pure_bind]
    unfold continueRun
    simp only [expandStep_run_eq, PMF.pure_map, Bool.false_or]
    rfl

end
end SDitH.Proofs.TreeRunClosed
