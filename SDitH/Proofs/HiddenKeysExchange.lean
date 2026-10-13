import SDitH.Proofs.HiddenKeys
import SDitH.Proofs.TreeExchange

/-! The hidden keys under the exchange. Pruning depends on a key list only
through its members; and when the exchanged node lies on the hidden path,
the hidden keys of the exchanged family with the old key added have the
same members as the hidden keys of the family with the new key added,
since the exchange changes the tree only at the node. -/

namespace SDitH.Proofs.HiddenKeysExchange

open Spec.SeedTree Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation
open HiddenLeafNode HiddenEntries HiddenKeys TreeExchange
open scoped Classical

noncomputable section

variable {lambda : Nat} {Key Block : Type*}

/-- Pruning depends on the key list only through its members. -/
theorem pruneAt_congr_mem (K₁ K₂ : List Key) (h : ∀ x, x ∈ K₁ ↔ x ∈ K₂) (history : List (Entry Key Block)) :
    pruneAt K₁ history = pruneAt K₂ history := by
  unfold pruneAt
  refine List.filter_congr fun e _ => ?_
  simp [h e.key]

/-- A path address is at most the leaf's. -/
theorem le_of_mem_pathAddresses {a c : Nat} (hc : c ∈ pathAddresses a) : c ≤ a := by
  obtain ⟨-, k, hk⟩ := mem_pathAddresses_iff.mp hc
  rw [← hk]
  exact Nat.div_le_self a (2 ^ k)

/-- The hidden keys under the exchange of a path node: with the old key
added they have the members of the hidden keys with the new key added. -/
theorem mem_hiddenKeys_exchanged (layout : Layout lambda Key Block) (hin : Function.Injective layout.input)
    (hl : 26 ≤ lambda) (L : Nat) (hL : 4 * L ≤ 2 ^ 24) (f : Family Key Block) (variant : Grinding) (salt root : Bits lambda)
    (b : Nat) (hb : 1 < b) (hbL : b < 2 * L) (v' : Block)
    (hp : parentKey layout f variant salt root b ≠ layout.key (layout.output (nodeBlock layout f variant salt root b)))
    (hp' : parentKey layout f variant salt root b ≠ layout.key (layout.output v'))
    (G1 : ∀ c, 1 ≤ c → c < 2 * L → c ≠ b / 2 →
      layout.key (node (treeExpand layout f variant salt) root c) ≠ parentKey layout f variant salt root b)
    (G2 : ∀ c, 1 ≤ c → c < 2 * L → c ≠ b →
      layout.key (node (treeExpand layout f variant salt) root c) ≠
        layout.key (layout.output (nodeBlock layout f variant salt root b)))
    (G3 : ∀ c, 1 ≤ c → c < 2 * L → layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key (layout.output v'))
    (G4 : ∀ c, c < 2 * L → c / 2 = b / 2 → c ≠ b →
      f (parentKey layout f variant salt root b) (layout.input (nodeTweak variant salt c)) ≠ v')
    (a : Nat) (ha : a < 2 * L) (hpath : b ∈ pathAddresses a) (x : Key) :
    x ∈ layout.key (layout.output (nodeBlock layout f variant salt root b)) ::
        hiddenKeys layout (exchanged layout f variant salt root b v') variant salt root a ↔
      x ∈ layout.key (layout.output v') :: hiddenKeys layout f variant salt root a := by
  have hnode := node_exchanged layout hin hl L hL f variant salt root b hb hbL v' hp hp' G1 G2 G3 G4
  have hrange : ∀ c, (c = 1 ∨ c ∈ pathAddresses a) → c < 2 * L := by
    rintro c (rfl | hc)
    · omega
    · have := le_of_mem_pathAddresses hc
      omega
  have hb' : node (treeExpand layout f variant salt) root b = layout.output (nodeBlock layout f variant salt root b) :=
    node_eq_output_nodeBlock layout f variant salt root b hb
  simp only [List.mem_cons, mem_hiddenKeys]
  constructor
  · rintro (rfl | ⟨c, hc, rfl⟩)
    · exact Or.inr ⟨b, Or.inr hpath, by rw [hb']⟩
    · rw [hnode c (hrange c hc)]
      by_cases hcb : c = b
      · rw [if_pos hcb]
        exact Or.inl rfl
      · rw [if_neg hcb]
        exact Or.inr ⟨c, hc, rfl⟩
  · rintro (rfl | ⟨c, hc, rfl⟩)
    · exact Or.inr ⟨b, Or.inr hpath, by rw [hnode b hbL, if_pos rfl]⟩
    · by_cases hcb : c = b
      · subst hcb
        exact Or.inl (by rw [hb'])
      · exact Or.inr ⟨c, hc, by rw [hnode c (hrange c hc), if_neg hcb]⟩

end
end SDitH.Proofs.HiddenKeysExchange
