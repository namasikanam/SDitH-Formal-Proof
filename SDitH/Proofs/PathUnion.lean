import SDitH.Proofs.HiddenKeys
import SDitH.Proofs.TreeStepFresh

/-! The union bound over the hidden path. A list of entries touches the
hidden keys of a leaf only if the key of the root, of a path node or of the
leaf is among the entries' keys, so the touching indicator is at most the
sum over those addresses of the indicators. -/

namespace SDitH.Proofs.PathUnion

open Spec.SeedTree Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat} (layout : Layout lambda (Bits lambda) (Bits lambda)) (g : Family (Bits lambda) (Bits lambda))
  (variant : Grinding) (salt root : Bits lambda) (a : Nat)

/-- The addresses of the hidden keys: the root and the path. -/
def pathSet : Finset Nat := (1 :: pathAddresses a).toFinset

/-- Touching the hidden keys is at most the sum over the root and the path
of touching the node's key. -/
theorem touch_le_sum (new : List (Entry (Bits lambda) (Bits lambda))) :
    indicator (decide (∃ e ∈ new, e.key ∈ hiddenKeys layout g variant salt root a)) ≤
      ∑ b ∈ pathSet a, indicator (decide (layout.key (node (treeExpand layout g variant salt) root b) ∈ keysOf new)) := by
  by_cases h : ∃ e ∈ new, e.key ∈ hiddenKeys layout g variant salt root a
  · obtain ⟨e, he, hκ⟩ := h
    obtain ⟨b, hb, hkey⟩ := (mem_hiddenKeys layout g variant salt root a e.key).mp hκ
    have hmem : b ∈ pathSet a := by
      simp only [pathSet, List.mem_toFinset, List.mem_cons]
      exact hb
    have hterm : indicator (decide (layout.key (node (treeExpand layout g variant salt) root b) ∈ keysOf new)) = 1 := by
      have : layout.key (node (treeExpand layout g variant salt) root b) ∈ keysOf new :=
        mem_keysOf.mpr ⟨e, he, hkey.symm⟩
      simp [this, indicator]
    have hex : ∃ e ∈ new, e.key ∈ hiddenKeys layout g variant salt root a := ⟨e, he, hκ⟩
    calc indicator (decide (∃ e ∈ new, e.key ∈ hiddenKeys layout g variant salt root a)) = 1 := by
          simp [indicator, hex]
      _ = indicator (decide (layout.key (node (treeExpand layout g variant salt) root b) ∈ keysOf new)) := hterm.symm
      _ ≤ _ := Finset.single_le_sum
          (f := fun b => indicator (decide (layout.key (node (treeExpand layout g variant salt) root b) ∈ keysOf new)))
          (fun _ _ => zero_le _) hmem
  · simp [h, indicator]

end
end SDitH.Proofs.PathUnion
