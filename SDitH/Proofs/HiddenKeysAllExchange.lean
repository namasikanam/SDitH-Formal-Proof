import SDitH.Proofs.HiddenTuple
import SDitH.Proofs.HiddenKeysExchange
import SDitH.Proofs.RootExchange

/-! The hidden keys of all executions under the exchanges. When the
exchanged node lies on the hidden path of some execution, the hidden keys
of all executions for the exchanged family with the old key added have the
members of the hidden keys for the family with the new key added; and
likewise for the root exchange. -/

namespace SDitH.Proofs.HiddenKeysAllExchange

open Spec.SeedTree Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation
open HiddenLeafNode HiddenEntries HiddenKeys HiddenKeysExchange TreeExchange HiddenTuple KeySwap RootExchange
open scoped Classical

noncomputable section

variable {lambda tau kappa : Nat} (layout : Layout lambda (Bits lambda) (Bits lambda)) (f : Family (Bits lambda) (Bits lambda))
  (variant : Grinding) (salt root : Bits lambda) (hidden : Fin tau → Fin (2 ^ kappa))

/-- Every address of an execution's hidden path lies below twice the leaf
count. -/
theorem lt_of_mem_path (e : Fin tau) (c : Nat) (hc : c = 1 ∨ c ∈ pathAddresses (leafAddress e (hidden e))) :
    c < 2 * (tau * 2 ^ kappa) := by
  have hb := SDitH.Proofs.SeedTree.leafAddress_bounds e (hidden e)
  rcases hc with rfl | hc
  · omega
  · have := le_of_mem_pathAddresses hc
    omega

/-- A node's key on an execution's hidden path is among the hidden keys of
all executions. -/
theorem key_mem_hiddenKeysAll (e : Fin tau) (c : Nat) (hc : c = 1 ∨ c ∈ pathAddresses (leafAddress e (hidden e))) :
    layout.key (node (treeExpand layout f variant salt) root c) ∈ hiddenKeysAll layout f variant salt root hidden := by
  rw [mem_hiddenKeysAll]
  exact ⟨e, (mem_hiddenKeys _ _ _ _ _ _ _).mpr ⟨c, hc, rfl⟩⟩

/-- The hidden keys of all executions under the exchange of a node on some
execution's hidden path. -/
theorem mem_hiddenKeysAll_exchanged (hin : Function.Injective layout.input) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24) (b : Nat) (hb : 1 < b) (hbL : b < 2 * (tau * 2 ^ kappa)) (v' : Bits lambda)
    (hp : parentKey layout f variant salt root b ≠ layout.key (layout.output (nodeBlock layout f variant salt root b)))
    (hp' : parentKey layout f variant salt root b ≠ layout.key (layout.output v'))
    (G1 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b / 2 →
      layout.key (node (treeExpand layout f variant salt) root c) ≠ parentKey layout f variant salt root b)
    (G2 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) → c ≠ b →
      layout.key (node (treeExpand layout f variant salt) root c) ≠
        layout.key (layout.output (nodeBlock layout f variant salt root b)))
    (G3 : ∀ c, 1 ≤ c → c < 2 * (tau * 2 ^ kappa) →
      layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key (layout.output v'))
    (G4 : ∀ c, c < 2 * (tau * 2 ^ kappa) → c / 2 = b / 2 → c ≠ b →
      f (parentKey layout f variant salt root b) (layout.input (nodeTweak variant salt c)) ≠ v')
    (e : Fin tau) (hpath : b ∈ pathAddresses (leafAddress e (hidden e))) (x : Bits lambda) :
    x ∈ layout.key (layout.output (nodeBlock layout f variant salt root b)) ::
        hiddenKeysAll layout (exchanged layout f variant salt root b v') variant salt root hidden ↔
      x ∈ layout.key (layout.output v') :: hiddenKeysAll layout f variant salt root hidden := by
  have hnode := node_exchanged layout hin hl (tau * 2 ^ kappa) hL f variant salt root b hb hbL v' hp hp' G1 G2 G3 G4
  have hb' : node (treeExpand layout f variant salt) root b = layout.output (nodeBlock layout f variant salt root b) :=
    node_eq_output_nodeBlock layout f variant salt root b hb
  simp only [List.mem_cons, mem_hiddenKeysAll, mem_hiddenKeys]
  constructor
  · rintro (rfl | ⟨e', c, hc, rfl⟩)
    · exact Or.inr ⟨e, b, Or.inr hpath, by rw [hb']⟩
    · rw [hnode c (lt_of_mem_path hidden e' c hc)]
      by_cases hcb : c = b
      · rw [if_pos hcb]
        exact Or.inl rfl
      · rw [if_neg hcb]
        exact Or.inr ⟨e', c, hc, rfl⟩
  · rintro (rfl | ⟨e', c, hc, rfl⟩)
    · exact Or.inr ⟨e, b, Or.inr hpath, by rw [hnode b hbL, if_pos rfl]⟩
    · by_cases hcb : c = b
      · subst hcb
        exact Or.inl (by rw [hb'])
      · exact Or.inr ⟨e', c, hc, by rw [hnode c (lt_of_mem_path hidden e' c hc), if_neg hcb]⟩

/-- The hidden keys of all executions under the root exchange. -/
theorem mem_hiddenKeysAll_root_exchanged (root' : Bits lambda)
    (G2 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
      layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key root)
    (G3 : ∀ c, 2 ≤ c → c < 2 * (tau * 2 ^ kappa) →
      layout.key (node (treeExpand layout f variant salt) root c) ≠ layout.key root')
    (e : Fin tau) (x : Bits lambda) :
    x ∈ layout.key root :: hiddenKeysAll layout (rootExchanged layout f root root') variant salt root' hidden ↔
      x ∈ layout.key root' :: hiddenKeysAll layout f variant salt root hidden := by
  have hnode := node_root_exchanged layout f variant salt root root' (tau * 2 ^ kappa) G2 G3
  have hroot : ∀ g : Family (Bits lambda) (Bits lambda), ∀ r : Bits lambda,
      node (treeExpand layout g variant salt) r 1 = r := fun g r => by
    rw [node]
    simp
  have h1 : 1 < 2 * (tau * 2 ^ kappa) := lt_of_mem_path hidden e 1 (Or.inl rfl)
  simp only [List.mem_cons, mem_hiddenKeysAll, mem_hiddenKeys]
  constructor
  · rintro (rfl | ⟨e', c, hc, rfl⟩)
    · exact Or.inr ⟨e, 1, Or.inl rfl, by rw [hroot]⟩
    · rw [hnode c (lt_of_mem_path hidden e' c hc)]
      by_cases hc1 : c ≤ 1
      · rw [if_pos hc1]
        exact Or.inl rfl
      · rw [if_neg hc1]
        exact Or.inr ⟨e', c, hc, rfl⟩
  · rintro (rfl | ⟨e', c, hc, rfl⟩)
    · exact Or.inr ⟨e, 1, Or.inl rfl, by rw [hnode 1 h1, if_pos le_rfl]⟩
    · by_cases hc1 : c ≤ 1
      · have hc1' : c = 1 := by
          rcases hc with rfl | hc
          · rfl
          · have := (mem_pathAddresses_iff.mp hc).1
            omega
        subst hc1'
        exact Or.inl (by rw [hroot])
      · exact Or.inr ⟨e', c, hc, by rw [hnode c (lt_of_mem_path hidden e' c hc), if_neg hc1]⟩

end
end SDitH.Proofs.HiddenKeysAllExchange
