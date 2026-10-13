import SDitH.Proofs.TreeRunClosed
import SDitH.Proofs.HiddenKeysAllExchange

/-! The tree of any family matching the recorded expansion. The expansion
records both children's entries of every expanded parent, so a family that
matches a history containing them computes the same tree below the root,
and the hidden keys of all executions are the same. This frees the pruning
keys from the family actually used: after the family is resampled
consistently with the history, the hidden keys are unchanged. -/

namespace SDitH.Proofs.TreeOfMatches

open Spec.SeedTree Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation Spec.SeedPrimitives Spec.BAVC
open Spec.HashCipherProgram Spec.SharedSigner
open HiddenLeafNode HiddenEntries HiddenKeys TreeRunClosed HiddenTuple HiddenKeysAllExchange
open scoped Classical

noncomputable section

variable {lambda : Nat} (layout : Layout lambda (Bits lambda) (Bits lambda)) (g : Family (Bits lambda) (Bits lambda))
  (variant : Grinding) (salt root : Bits lambda) (initial : Nat → Seed lambda)

/-- A node at or below address one is the root. -/
theorem node_of_le (expand : Nat → Seed lambda → Seed lambda × Seed lambda) (r : Seed lambda) {a : Nat} (ha : a ≤ 1) :
    node expand r a = r := by
  rw [node]
  simp [ha]

/-- A child's expansion entry: the parent's key, the child's tweak and the
family's output. -/
def childEntry (a : Nat) : Entry (Bits lambda) (Bits lambda) :=
  ⟨layout.key (node (treeExpand layout g variant salt) root (a / 2)), layout.input (nodeTweak variant salt a),
    g (layout.key (node (treeExpand layout g variant salt) root (a / 2))) (layout.input (nodeTweak variant salt a))⟩

/-- The expansion's history through a number of steps contains the even
child's entry of every parent up to that number. -/
theorem childEntry_even_mem (k p : Nat) (hp1 : 1 ≤ p) (hpk : p ≤ k) :
    childEntry layout g variant salt root (2 * p) ∈ treeHistory layout g variant salt root initial k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hpk' : p ≤ k
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hpk'))
    · have hp : p = k + 1 := by omega
      subst hp
      have hrun : Spec.SeedTree.run (treeExpand layout g variant salt) root initial k (k + 1) =
          node (treeExpand layout g variant salt) root (k + 1) :=
        SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)
      have hdiv : 2 * (k + 1) / 2 = k + 1 := by omega
      have hmod : decide (2 * (k + 1) % 2 = 1) = false := by simp
      simp only [treeHistory, List.mem_cons]
      right; left
      simp only [childEntry, nodeTweak, hdiv, hmod, hrun, Spec.IdealCipher.entry]

/-- The expansion's history through a number of steps contains the odd
child's entry of every parent up to that number. -/
theorem childEntry_odd_mem (k p : Nat) (hp1 : 1 ≤ p) (hpk : p ≤ k) :
    childEntry layout g variant salt root (2 * p + 1) ∈ treeHistory layout g variant salt root initial k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hpk' : p ≤ k
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hpk'))
    · have hp : p = k + 1 := by omega
      subst hp
      have hrun : Spec.SeedTree.run (treeExpand layout g variant salt) root initial k (k + 1) =
          node (treeExpand layout g variant salt) root (k + 1) :=
        SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)
      have hdiv : (2 * (k + 1) + 1) / 2 = k + 1 := by omega
      have hmod' : (2 * (k + 1) + 1) % 2 = 1 := by omega
      have hmod : decide ((2 * (k + 1) + 1) % 2 = 1) = true := by simp [hmod']
      simp only [treeHistory, List.mem_cons]
      left
      simp only [childEntry, nodeTweak, hdiv, hmod, hrun, Spec.IdealCipher.entry]

/-- A family matching a history that contains the expansion's entries
computes the same tree on the expanded addresses. -/
theorem node_eq_of_matches (g' : Family (Bits lambda) (Bits lambda)) (H : List (Entry (Bits lambda) (Bits lambda)))
    (hm : Matches g' H) (k : Nat) (hsub : ∀ e ∈ treeHistory layout g variant salt root initial k, e ∈ H)
    (a : Nat) (ha : a ≤ 2 * k + 1) :
    node (treeExpand layout g' variant salt) root a = node (treeExpand layout g variant salt) root a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    by_cases ha1 : a ≤ 1
    · rw [node_of_le _ _ ha1, node_of_le _ _ ha1]
    · rw [node_eq_child layout g' variant salt root a (by omega), node_eq_child layout g variant salt root a (by omega),
        ih (a / 2) (by omega) (by omega)]
      congr 1
      have hmem : childEntry layout g variant salt root a ∈ H := by
        apply hsub
        rcases Nat.even_or_odd' a with ⟨p, rfl | rfl⟩
        · exact childEntry_even_mem layout g variant salt root initial k p (by omega) (by omega)
        · exact childEntry_odd_mem layout g variant salt root initial k p (by omega) (by omega)
      exact hm _ hmem

/-- The hidden keys of all executions are the same for any family matching
a history that contains the expansion's entries. -/
theorem mem_hiddenKeysAll_of_matches {tau kappa : Nat} (g' : Family (Bits lambda) (Bits lambda))
    (H : List (Entry (Bits lambda) (Bits lambda))) (hm : Matches g' H)
    (hsub : ∀ e ∈ treeHistory layout g variant salt root initial (tau * 2 ^ kappa - 1), e ∈ H)
    (hidden : Fin tau → Fin (2 ^ kappa)) (x : Bits lambda) :
    x ∈ hiddenKeysAll layout g' variant salt root hidden ↔ x ∈ hiddenKeysAll layout g variant salt root hidden := by
  simp only [mem_hiddenKeysAll, mem_hiddenKeys]
  constructor
  · rintro ⟨e, b, hb, rfl⟩
    refine ⟨e, b, hb, ?_⟩
    rw [node_eq_of_matches layout g variant salt root initial g' H hm _ hsub b
      (by have := lt_of_mem_path hidden e b hb; omega)]
  · rintro ⟨e, b, hb, rfl⟩
    refine ⟨e, b, hb, ?_⟩
    rw [node_eq_of_matches layout g variant salt root initial g' H hm _ hsub b
      (by have := lt_of_mem_path hidden e b hb; omega)]

end
end SDitH.Proofs.TreeOfMatches
