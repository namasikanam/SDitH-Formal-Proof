import SDitH.Proofs.TreeDistinctBound
import SDitH.Proofs.TreeDistinct

/-! From the run's distinctness to the family's. The expansion's run is the
seed tree's run, which agrees with the tree on the allocated addresses, so
the family's tree keys are fresh and distinct whenever the run's are, and
the family's not-distinct event is bounded by the run's. -/

namespace SDitH.Proofs.DistinctBridge

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.RandomOracleTrap
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open TreeStepFresh CipherResample RowStoredAfter TreeGoodInduction TreeRunClosed TreeDistinctBound TreeDistinct
open HiddenLeafNode
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The family's tree keys are fresh and distinct when the run's are. -/
theorem distinct_of_distinctTo (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (g : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root : Bits lambda) (L : Nat) (hL1 : 1 ≤ L)
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (h : DistinctTo layout H (L - 1) (Spec.SeedTree.run (treeExpand layout g variant salt) root (fun _ => root) (L - 1))) :
    Distinct layout g variant salt root L H := by
  have hrun : ∀ c, 1 ≤ c → c < 2 * L →
      Spec.SeedTree.node (treeExpand layout g variant salt) root c =
        Spec.SeedTree.run (treeExpand layout g variant salt) root (fun _ => root) (L - 1) c := by
    intro c hc1 hc
    rw [SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)]
  constructor
  · intro c hc1 hc
    rw [hrun c hc1 hc]
    exact h.1 c hc1 (by omega)
  · intro c c' hc1 hc hc1' hc' hne
    rw [hrun c hc1 hc, hrun c' hc1' hc']
    exact h.2 c c' hc1 (by omega) hc1' (by omega) hne

/-- The family's tree keys are not fresh and distinct with probability at
most the root's indicator plus the steps times the step bound. -/
theorem distinct_family_le (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt root : Bits lambda) (hin : Function.Injective layout.input) (hl : 26 ≤ lambda) (L : Nat) (hL : 4 * L ≤ 2 ^ 24)
    (hL1 : 1 ≤ L) (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c)
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (hpos : ∃ family : Family (Bits lambda) (Bits lambda), Matches family H) (q : Nat)
    (hq : H.length + 2 * (L - 1) + 1 ≤ q) :
    ((posterior H).map fun g => decide (¬ Distinct layout g variant salt root L H)) true ≤
      indicator (decide (layout.key root ∈ keysOf H)) +
        (L - 1 : ℕ) * (2 * (((c * ((keysOf H).card + 2 * L) : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) +
          (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) := by
  have h := tree_distinct_le (s := 0) (wit := 0) (rnd := 0) layout variant salt root hin hl L hL c hfiber H hpos q
    (fun _ => none) [] [] (L - 1) (by omega) hq
  simp only [tree_run_eq, PMF.pure_map] at h
  refine le_trans ?_ h
  show ((posterior H).bind fun g => PMF.pure (decide (¬ Distinct layout g variant salt root L H))) true ≤ _
  refine bind_true_le_bind_true _ _ _ fun g _ => ?_
  rw [PMF.pure_apply, PMF.pure_apply]
  by_cases hd : Distinct layout g variant salt root L H
  · simp [hd]
  · have hdt : ¬ DistinctTo layout H (L - 1)
        (Spec.SeedTree.run (treeExpand layout g variant salt) root (fun _ => root) (L - 1)) :=
      fun hdt => hd (distinct_of_distinctTo layout g variant salt root L hL1 H hdt)
    simp [notDistinct, treeOf, hd, hdt]

end
end SDitH.Proofs.DistinctBridge
