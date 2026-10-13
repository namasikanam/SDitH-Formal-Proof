import SDitH.Proofs.SharedSigner
import SDitH.Proofs.HiddenLeafNode

/-! The commitment program's tree expansion records every internal node's
expansion entries, so every node within the expanded range has its ancestry
recorded in the cipher history. Combined with the determination of a node
by any family consistent with a history recording its ancestry, the hidden
leaf's parent (and the leaf itself) is fixed by the recorded history of the
commitment. -/

namespace SDitH.Proofs.TreeEntries

open Spec.DomainSeparation Spec.SharedSigner Spec.HashCipherEvaluation Spec.SeedTree Spec.SeedPrimitives
open Spec.BAVCCipherProgram Spec.IdealCipher
open SDitH.Proofs.SeedTree HiddenLeafNode
open Spec.SlopeConsistencyGame (Out)

noncomputable section

variable {lambda s wit rnd : Nat}
variable (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
  (table : List Bool → Option (Out lambda s wit rnd))
  (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))

/-- The tree expansion records the expansion entries of every internal node it
expands, at the node's tree value. -/
theorem treeThrough_entries (layout : Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt root : Bits lambda) (initial : Nat → Spec.BAVC.Seed lambda) (steps : Nat) (value : Nat → Spec.BAVC.Seed lambda)
    (h : Evaluates family table ciphers (treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root initial steps)
      value) :
    ∀ i, 0 < i → i ≤ steps →
      SharedSigner.expandEntries family ciphers layout variant salt i (node (treeExpand layout family variant salt) root i) := by
  induction steps generalizing value with
  | zero =>
    intro i hi hle
    omega
  | succ steps ih =>
    intro i hi hle
    obtain ⟨tree, htree, hv⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp h
    obtain ⟨children, hchildren, _⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp hv
    by_cases hlast : i = steps + 1
    · subst hlast
      obtain ⟨_, hentries⟩ :=
        SharedSigner.expandCall_evaluates family table ciphers layout variant salt _ _ children hchildren
      have htreeval := SharedSigner.treeThrough_evaluates family table ciphers layout variant salt root initial steps tree htree
      rw [htreeval, run_matches_node _ _ _ _ _ (by omega) (by omega)] at hentries
      exact hentries
    · exact ih tree htree i hi (by omega)

/-- Every node within the expanded range has its ancestry recorded. -/
theorem ancestry_recorded (layout : Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt root : Bits lambda) (initial : Nat → Spec.BAVC.Seed lambda) (steps : Nat) (value : Nat → Spec.BAVC.Seed lambda)
    (h : Evaluates family table ciphers (treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root initial steps)
      value) (a : Nat) (ha : a ≤ 2 * steps + 1) :
    AncestryRecorded layout family variant salt root ciphers a := by
  intro k hk
  have hb : a / 2 ^ k ≤ 2 * steps + 1 := (Nat.div_le_self _ _).trans ha
  have hentries := treeThrough_entries family table ciphers layout variant salt root initial steps value h (a / 2 ^ k / 2)
    (by omega) (by omega)
  have := hentries (decide (a / 2 ^ k % 2 = 1))
  unfold nodeEntry nodeTweak
  exact this

end
end SDitH.Proofs.TreeEntries
