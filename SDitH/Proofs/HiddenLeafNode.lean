import SDitH.Proofs.SeedTree
import SDitH.Spec.BAVCCipherProgram
import SDitH.Proofs.PosteriorLeafUniform

/-! A tree node as the cipher image of its parent, and its determination by
the recorded history. In the seed tree expanded through the cipher layout,
every node below the root is the layout's output of the family's encryption,
under the layout's key image of its parent, of the layout's input image of
the parent's tweak. If the expansion entries along a node's ancestry are
recorded in a history, every family consistent with that history computes
the same node; so, conditioned on the history, the node is determined, and
its own expansion under a fresh parent key is a uniform seed. -/

namespace SDitH.Proofs.HiddenLeafNode

open Spec.SeedTree Spec.SeedPrimitives Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation
open SDitH.Proofs.SeedTree

noncomputable section

variable {lambda : Nat} {Key Block : Type*}

/-- The tree expansion through the layout and a family. -/
def treeExpand (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding) (salt : Bits lambda) :
    Nat → Bits lambda → Bits lambda × Bits lambda :=
  expandSeed variant (encStar layout family) salt

/-- The tweak of a node's expansion from its parent: the parent's address and
the node's side. -/
def nodeTweak (variant : Grinding) (salt : Bits lambda) (a : Nat) : Bits lambda :=
  cipherInput variant salt (a / 2) (a % 2 = 1)

/-- A node below the root is the layout's output of the family's encryption of
its tweak under its parent. -/
theorem node_eq_child (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (a : Nat) (ha : 1 < a) :
    node (treeExpand layout family variant salt) root a =
      layout.output (family (layout.key (node (treeExpand layout family variant salt) root (a / 2)))
        (layout.input (nodeTweak variant salt a))) := by
  have hpos : 0 < a / 2 := by omega
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · have ha2 : a = 2 * (a / 2) := by omega
    rw [ha2, node_left _ _ _ hpos]
    simp only [nodeTweak, treeExpand, expandSeed, encStar, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [show decide (2 * (a / 2) % 2 = 1) = false from decide_eq_false (by omega)]
  · have ha2 : a = 2 * (a / 2) + 1 := by omega
    rw [ha2, node_right _ _ _ hpos]
    simp only [nodeTweak, treeExpand, expandSeed, encStar]
    have hdiv : (2 * (a / 2) + 1) / 2 = a / 2 := by omega
    rw [hdiv, show decide ((2 * (a / 2) + 1) % 2 = 1) = true from decide_eq_true (by omega)]

/-- The expansion entry of a node from its parent, as recorded by a family. -/
def nodeEntry (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding) (salt root : Bits lambda)
    (a : Nat) : Entry Key Block :=
  let parent := node (treeExpand layout family variant salt) root (a / 2)
  ⟨layout.key parent, layout.input (nodeTweak variant salt a),
    family (layout.key parent) (layout.input (nodeTweak variant salt a))⟩

/-- The node's ancestry (itself and its proper ancestors below the root) is
recorded in the history. -/
def AncestryRecorded (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (history : List (Entry Key Block)) (a : Nat) : Prop :=
  ∀ k, 1 < a / 2 ^ k → nodeEntry layout family variant salt root (a / 2 ^ k) ∈ history

theorem ancestryRecorded_parent (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (history : List (Entry Key Block)) (a : Nat)
    (h : AncestryRecorded layout family variant salt root history a) :
    AncestryRecorded layout family variant salt root history (a / 2) := by
  intro k hk
  have key : a / 2 / 2 ^ k = a / 2 ^ (k + 1) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
  rw [key] at hk ⊢
  exact h (k + 1) hk

/-- Every family consistent with a history recording a node's ancestry
computes the same node. -/
theorem node_determined (layout : Layout lambda Key Block) (family family' : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (history : List (Entry Key Block)) (hmatch : Matches family' history) (a : Nat)
    (hrec : AncestryRecorded layout family variant salt root history a) :
    node (treeExpand layout family' variant salt) root a = node (treeExpand layout family variant salt) root a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    by_cases ha : a ≤ 1
    · have h1 : node (treeExpand layout family' variant salt) root a = root := by
        rw [node]
        simp [ha]
      have h2 : node (treeExpand layout family variant salt) root a = root := by
        rw [node]
        simp [ha]
      rw [h1, h2]
    · have ha1 : 1 < a := by omega
      have hparent := ih (a / 2) (by omega) (ancestryRecorded_parent layout family variant salt root history a hrec)
      rw [node_eq_child layout family' variant salt root a ha1, node_eq_child layout family variant salt root a ha1, hparent]
      have hself := hrec 0 (by simpa using ha1)
      simp only [Nat.pow_zero, Nat.div_one] at hself
      have := hmatch _ hself
      exact congrArg layout.output this

end
end SDitH.Proofs.HiddenLeafNode
