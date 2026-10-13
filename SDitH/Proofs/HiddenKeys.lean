import SDitH.Proofs.HiddenEntries

/-! The hidden keys of a leaf: the keys of the root, of the leaf's proper
ancestors below the root, and of the leaf itself. The leaf's key is needed
because its commitment is a cipher call at that key. The path's parent keys
are among the hidden keys, and every hidden key is fresh in the history
pruned at them. -/

namespace SDitH.Proofs.HiddenKeys

open Spec.SeedTree Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation
open HiddenLeafNode FreshKeyUniform HiddenEntries
open scoped Classical

noncomputable section

variable {lambda : Nat} {Key Block : Type*}

/-- The hidden keys: the keys of the root and of every node of the path. -/
def hiddenKeys (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding) (salt root : Bits lambda)
    (a : Nat) : List Key :=
  (1 :: pathAddresses a).map fun b => layout.key (node (treeExpand layout family variant salt) root b)

theorem mem_hiddenKeys (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (a : Nat) (κ : Key) :
    κ ∈ hiddenKeys layout family variant salt root a ↔
      ∃ b, (b = 1 ∨ b ∈ pathAddresses a) ∧ layout.key (node (treeExpand layout family variant salt) root b) = κ := by
  simp only [hiddenKeys, List.mem_map, List.mem_cons]

/-- The root's key is hidden. -/
theorem root_key_mem_hiddenKeys (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (a : Nat) : layout.key root ∈ hiddenKeys layout family variant salt root a := by
  rw [mem_hiddenKeys]
  refine ⟨1, Or.inl rfl, ?_⟩
  simp [node]

/-- The leaf's key is hidden. -/
theorem leaf_key_mem_hiddenKeys (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (a : Nat) (ha : 1 < a) :
    layout.key (node (treeExpand layout family variant salt) root a) ∈ hiddenKeys layout family variant salt root a := by
  rw [mem_hiddenKeys]
  exact ⟨a, Or.inr (self_mem_pathAddresses ha), rfl⟩

/-- A path node's parent is the root or a path node. -/
theorem parent_mem_pathAddresses {a b : Nat} (hb : b ∈ pathAddresses a) : b / 2 = 1 ∨ b / 2 ∈ pathAddresses a := by
  rw [mem_pathAddresses_iff] at hb ⊢
  obtain ⟨hb1, k, hk⟩ := hb
  by_cases h : 1 < b / 2
  · right
    refine ⟨h, k + 1, ?_⟩
    rw [← hk, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  · left
    omega

/-- The path's parent keys are hidden keys. -/
theorem pathKeys_subset_hiddenKeys (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (a : Nat) :
    ∀ κ ∈ pathKeys layout family variant salt root a, κ ∈ hiddenKeys layout family variant salt root a := by
  intro κ hκ
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hκ
  rw [mem_hiddenKeys]
  exact ⟨b / 2, parent_mem_pathAddresses hb, rfl⟩

/-- Every hidden key is fresh in the history pruned at the hidden keys. -/
theorem freshKey_hiddenKeys (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (a : Nat) (world : World Key Block) (κ : Key)
    (hκ : κ ∈ hiddenKeys layout family variant salt root a) :
    FreshKey (pruneWorld (hiddenKeys layout family variant salt root a) world) κ :=
  freshKey_pruneWorld _ world κ hκ

/-- A history pruned at the hidden keys is pruned at the path's parent keys. -/
theorem pruneAt_hiddenKeys_pruneAt_pathKeys (layout : Layout lambda Key Block) (family : Family Key Block)
    (variant : Grinding) (salt root : Bits lambda) (a : Nat) (history : List (Entry Key Block)) :
    pruneAt (pathKeys layout family variant salt root a) (pruneAt (hiddenKeys layout family variant salt root a) history) =
      pruneAt (hiddenKeys layout family variant salt root a) history := by
  refine pruneAt_of_fresh _ _ fun e he hk => ?_
  exact (mem_pruneAt.mp he).2 (pathKeys_subset_hiddenKeys layout family variant salt root a e.key hk)

end
end SDitH.Proofs.HiddenKeys
