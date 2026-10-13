import SDitH.Proofs.HiddenLeafNode
import SDitH.Proofs.FreshKeyUniform

/-! The hidden path's entries and the pruned history. The hidden path of a
leaf is the leaf and its proper ancestors below the root; its parent keys are
the layout's keys of the path nodes' parents. The entries at a list of keys
and the pruned history (the entries at other keys) split a history, a family
matches the history exactly when it matches both parts, and every parent key
of the hidden path is fresh in the history pruned at them. These are the named
objects of the identical-until-bad route for the witness swap: the hidden
entries that the signer records and the pruned world that a continuation is
compared against. -/

namespace SDitH.Proofs.HiddenEntries

open Spec.SeedTree Spec.BAVCCipherProgram Spec.IdealCipher Spec.DomainSeparation
open HiddenLeafNode FreshKeyUniform
open scoped Classical

noncomputable section

/-- The addresses of a node and its proper ancestors below the root. -/
def pathAddresses (a : Nat) : List Nat :=
  if h : a ≤ 1 then [] else a :: pathAddresses (a / 2)
termination_by a
decreasing_by omega

theorem pathAddresses_of_le {a : Nat} (ha : a ≤ 1) : pathAddresses a = [] := by
  rw [pathAddresses, dif_pos ha]

theorem pathAddresses_of_lt {a : Nat} (ha : 1 < a) : pathAddresses a = a :: pathAddresses (a / 2) := by
  rw [pathAddresses, dif_neg (by omega)]

theorem lt_of_mem_pathAddresses {a b : Nat} (hb : b ∈ pathAddresses a) : 1 < b := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    by_cases ha : a ≤ 1
    · rw [pathAddresses_of_le ha] at hb
      simp at hb
    · rw [pathAddresses_of_lt (by omega)] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · exact ih (a / 2) (by omega) hb

theorem self_mem_pathAddresses {a : Nat} (ha : 1 < a) : a ∈ pathAddresses a := by
  rw [pathAddresses_of_lt ha]
  exact List.mem_cons_self

/-- The path's addresses are the ancestors below the root. -/
theorem mem_pathAddresses_iff {a b : Nat} : b ∈ pathAddresses a ↔ 1 < b ∧ ∃ k, a / 2 ^ k = b := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    by_cases ha : a ≤ 1
    · rw [pathAddresses_of_le ha]
      simp only [List.not_mem_nil, false_iff, not_and, not_exists]
      intro hb k hk
      have : a / 2 ^ k ≤ a := Nat.div_le_self a (2 ^ k)
      omega
    · rw [pathAddresses_of_lt (by omega), List.mem_cons, ih (a / 2) (by omega)]
      constructor
      · rintro (rfl | ⟨hb, k, hk⟩)
        · exact ⟨by omega, 0, by simp⟩
        · refine ⟨hb, k + 1, ?_⟩
          rw [← hk, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      · rintro ⟨hb, k, hk⟩
        cases k with
        | zero => left; simpa using hk.symm
        | succ k =>
          right
          refine ⟨hb, k, ?_⟩
          rw [← hk, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

variable {lambda : Nat} {Key Block : Type*}

/-- The parent keys of the hidden path: the keys of the path nodes' parents. -/
def pathKeys (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding) (salt root : Bits lambda)
    (a : Nat) : List Key :=
  (pathAddresses a).map fun b => layout.key (node (treeExpand layout family variant salt) root (b / 2))

/-- The entries of a history at a list of keys. -/
def entriesAt (keys : List Key) (history : List (Entry Key Block)) : List (Entry Key Block) :=
  history.filter fun e => e.key ∈ keys

/-- The history pruned at a list of keys: its entries at other keys. -/
def pruneAt (keys : List Key) (history : List (Entry Key Block)) : List (Entry Key Block) :=
  history.filter fun e => e.key ∉ keys

theorem mem_entriesAt {keys : List Key} {history : List (Entry Key Block)} {e : Entry Key Block} :
    e ∈ entriesAt keys history ↔ e ∈ history ∧ e.key ∈ keys := by
  simp [entriesAt]

theorem mem_pruneAt {keys : List Key} {history : List (Entry Key Block)} {e : Entry Key Block} :
    e ∈ pruneAt keys history ↔ e ∈ history ∧ e.key ∉ keys := by
  simp [pruneAt]

theorem pruneAt_append (keys : List Key) (h₁ h₂ : List (Entry Key Block)) :
    pruneAt keys (h₁ ++ h₂) = pruneAt keys h₁ ++ pruneAt keys h₂ :=
  List.filter_append _ _

theorem entriesAt_append (keys : List Key) (h₁ h₂ : List (Entry Key Block)) :
    entriesAt keys (h₁ ++ h₂) = entriesAt keys h₁ ++ entriesAt keys h₂ :=
  List.filter_append _ _

theorem pruneAt_pruneAt (keys : List Key) (history : List (Entry Key Block)) :
    pruneAt keys (pruneAt keys history) = pruneAt keys history := by
  simp [pruneAt, List.filter_filter]

/-- A history pruned at keys that no entry uses is the history. -/
theorem pruneAt_of_fresh (keys : List Key) (history : List (Entry Key Block))
    (h : ∀ e ∈ history, e.key ∉ keys) : pruneAt keys history = history :=
  List.filter_eq_self.mpr fun e he => by simpa using h e he

/-- A family matches a history exactly when it matches the entries at the keys
and the pruned history. -/
theorem matches_iff (keys : List Key) (family : Family Key Block) (history : List (Entry Key Block)) :
    Matches family history ↔ Matches family (entriesAt keys history) ∧ Matches family (pruneAt keys history) := by
  constructor
  · intro h
    exact ⟨fun e he => h e (mem_entriesAt.mp he).1, fun e he => h e (mem_pruneAt.mp he).1⟩
  · rintro ⟨h₁, h₂⟩ e he
    by_cases hk : e.key ∈ keys
    · exact h₁ e (mem_entriesAt.mpr ⟨he, hk⟩)
    · exact h₂ e (mem_pruneAt.mpr ⟨he, hk⟩)

theorem matches_pruneAt (keys : List Key) (family : Family Key Block) (history : List (Entry Key Block))
    (h : Matches family history) : Matches family (pruneAt keys history) :=
  ((matches_iff keys family history).mp h).2

/-- A possible history stays possible when pruned. -/
theorem pruneAt_possible (keys : List Key) (history : List (Entry Key Block))
    (h : ∃ family : Family Key Block, Matches family history) :
    ∃ family : Family Key Block, Matches family (pruneAt keys history) :=
  h.imp fun family hf => matches_pruneAt keys family history hf

/-- The pruned world of a world, at a list of keys. -/
def pruneWorld (keys : List Key) (world : World Key Block) : World Key Block :=
  ⟨pruneAt keys world.history, pruneAt_possible keys world.history world.possible⟩

/-- Every key of the list is fresh in the pruned world. -/
theorem freshKey_pruneWorld (keys : List Key) (world : World Key Block) (key : Key) (hkey : key ∈ keys) :
    FreshKey (pruneWorld keys world) key := by
  intro e he hk
  exact (mem_pruneAt.mp he).2 (hk ▸ hkey)

/-- The parent key of every path node is fresh in the history pruned at the
path's parent keys. -/
theorem freshKey_pathKeys (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (a : Nat) (world : World Key Block) (b : Nat) (hb : b ∈ pathAddresses a) :
    FreshKey (pruneWorld (pathKeys layout family variant salt root a) world)
      (layout.key (node (treeExpand layout family variant salt) root (b / 2))) :=
  freshKey_pruneWorld _ world _ (List.mem_map.mpr ⟨b, hb, rfl⟩)

/-- The hidden entries of a history: its entries at the path's parent keys. -/
def hiddenEntries (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (a : Nat) (history : List (Entry Key Block)) : List (Entry Key Block) :=
  entriesAt (pathKeys layout family variant salt root a) history

/-- A path node's expansion entry is a hidden entry whenever recorded. -/
theorem nodeEntry_mem_hiddenEntries (layout : Layout lambda Key Block) (family : Family Key Block) (variant : Grinding)
    (salt root : Bits lambda) (a : Nat) (history : List (Entry Key Block)) (b : Nat) (hb : b ∈ pathAddresses a)
    (hmem : nodeEntry layout family variant salt root b ∈ history) :
    nodeEntry layout family variant salt root b ∈ hiddenEntries layout family variant salt root a history :=
  mem_entriesAt.mpr ⟨hmem, List.mem_map.mpr ⟨b, hb, rfl⟩⟩

end
end SDitH.Proofs.HiddenEntries
