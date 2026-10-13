import SDitH.Proofs.TreeRunEntries
import SDitH.Proofs.PosteriorFresh
import SDitH.Proofs.RowStoredCount
import SDitH.Proofs.ForkEventUnion
import SDitH.Proofs.SeedPrimitives

/-! One expansion step under the posterior family. A tree is good for a
key set up to a step when no node's key within the expanded range lies
in the set. When the node being expanded has its key outside the starting
history's keys, both of its expansion calls are fresh inputs in the
history so far (the tree's earlier calls use other addresses, and the
starting history does not use the key), so under the posterior family
each child's key lies in the set with probability at most the fiber bound
times the set's size over the remaining block count; and the updated tree
is good at the next step when the children's keys are outside the set. -/

namespace SDitH.Proofs.TreeStepFresh

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives
open Spec.IdealCipher (Family Matches)
open IdealCipherFresh CipherResample PosteriorFresh RowStoredCount TreeRunEntries
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat}

/-- The keys of a history. -/
def keysOf (history : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) : Finset (Bits lambda) :=
  (history.map Spec.IdealCipher.Entry.key).toFinset

theorem keysOf_card_le (history : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) :
    (keysOf history).card ≤ history.length :=
  (List.toFinset_card_le _).trans (by rw [List.length_map])

theorem mem_keysOf {history : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))} {key : Bits lambda} :
    key ∈ keysOf history ↔ ∃ e ∈ history, e.key = key := by
  unfold keysOf
  rw [List.mem_toFinset, List.mem_map]

/-- A tree is good for a key set up to a step: no node's key within the
expanded range lies in the set. -/
def Good (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (K : Finset (Bits lambda)) (k : Nat)
    (tree : Nat → Seed lambda) : Prop :=
  ∀ b, b ≤ 2 * k + 1 → layout.key (tree b) ∉ K

/-- The cipher outputs whose key through the layout lies in a finite set
number at most the fiber bound times the set's size. -/
theorem count_key_hits (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c) (K : Finset (Bits lambda))
    (inst : Fintype {r : Bits lambda // layout.key (layout.output r) ∈ K}) :
    @Fintype.card {r : Bits lambda // layout.key (layout.output r) ∈ K} inst ≤ c * K.card := by
  rw [card_instance_eq inst inferInstance, Fintype.card_subtype]
  refine Finset.card_le_mul_card_image_of_maps_to (f := fun r => layout.key (layout.output r)) (t := K)
    (fun r hr => (Finset.mem_filter.mp hr).2) c (fun κ _ => ?_)
  calc _ ≤ (Finset.univ.filter fun r : Bits lambda => layout.key (layout.output r) = κ).card :=
        Finset.card_le_card fun r hr => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          exact hr.2
    _ = Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} := (Fintype.card_subtype _).symm
    _ ≤ c := hfiber κ

/-- Under the posterior family at a fresh input, the output's key lies in a
finite set with probability at most the fiber bound times the set's size
over the remaining block count. -/
theorem posterior_key_le (world : Spec.IdealCipher.World (Bits lambda) (Bits lambda)) (key input : Bits lambda)
    (hfresh : FreshInput world key input) (q : Nat) (hlen : world.history.length ≤ q)
    (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c) (K : Finset (Bits lambda)) :
    ((posterior world.history).map (fun f => decide (layout.key (layout.output (f key input)) ∈ K))) true ≤
      ((c * K.card : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞) := by
  have h := posterior_event_le world key input hfresh q hlen (fun r => layout.key (layout.output r) ∈ K)
  refine le_trans ?_ (h.trans (ENNReal.div_le_div_right
    ((Nat.cast_le (α := ℝ≥0∞)).mpr (count_key_hits layout c hfiber K _)) _))
  exact le_of_eq (congrArg (fun p : PMF Bool => p true) (congrArg (fun g => PMF.map g (posterior world.history))
    (funext fun f => by congr)))

/-- Both calls expanding a node whose key is outside the starting history's
keys are fresh inputs in the history so far. -/
theorem step_inputs_fresh (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (salt : Bits lambda) (hin : Function.Injective layout.input) (hl : 26 ≤ lambda) (L : Nat)
    (hL : 4 * L ≤ 2 ^ 24) (k : Nat) (hk : k + 1 < 2 * L)
    (H new : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (hnew : ∀ e ∈ new, TreeInput layout variant salt k e.input) (tree : Nat → Seed lambda)
    (hkey : layout.key (tree (k + 1)) ∉ keysOf H)
    (hpos : ∃ family : Family (Bits lambda) (Bits lambda), Matches family (new ++ H)) (b : Bool) :
    FreshInput (⟨new ++ H, hpos⟩ : Spec.IdealCipher.World (Bits lambda) (Bits lambda)) (layout.key (tree (k + 1)))
      (layout.input (cipherInput variant salt (k + 1) b)) := by
  intro e he hek hei
  rcases List.mem_append.mp he with hnew' | hH
  · obtain ⟨i, b', hi, hik, hx⟩ := hnew e hnew'
    rw [hx] at hei
    have := (SeedPrimitives.cipherInput_injective hl hL (by omega) hk variant salt b' b (hin hei)).1
    omega
  · exact hkey (mem_keysOf.mpr ⟨e, hH, hek⟩)

/-- Under the posterior family at the history so far, a child's key of a
node whose key is outside the starting keys lies in a finite set with
probability at most the fiber bound times the set's size over the
remaining block count. -/
theorem child_key_le (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (salt : Bits lambda) (hin : Function.Injective layout.input) (hl : 26 ≤ lambda) (L : Nat)
    (hL : 4 * L ≤ 2 ^ 24) (k : Nat) (hk : k + 1 < 2 * L)
    (H new : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (hnew : ∀ e ∈ new, TreeInput layout variant salt k e.input) (tree : Nat → Seed lambda)
    (hkey : layout.key (tree (k + 1)) ∉ keysOf H)
    (hpos : ∃ family : Family (Bits lambda) (Bits lambda), Matches family (new ++ H)) (q : Nat)
    (hlen : (new ++ H).length ≤ q) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c) (K : Finset (Bits lambda))
    (b : Bool) :
    ((posterior (new ++ H)).map (fun f => decide (layout.key (layout.output
        (f (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) b)))) ∈ K))) true ≤
      ((c * K.card : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞) :=
  posterior_key_le (⟨new ++ H, hpos⟩ : Spec.IdealCipher.World (Bits lambda) (Bits lambda)) _ _
    (step_inputs_fresh layout variant salt hin hl L hL k hk H new hnew tree hkey hpos b) q hlen layout c hfiber K

/-- The step's event: a child's key lies in the set. -/
theorem step_le (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (salt : Bits lambda) (hin : Function.Injective layout.input) (hl : 26 ≤ lambda) (L : Nat)
    (hL : 4 * L ≤ 2 ^ 24) (k : Nat) (hk : k + 1 < 2 * L)
    (H new : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (hnew : ∀ e ∈ new, TreeInput layout variant salt k e.input) (tree : Nat → Seed lambda)
    (hkey : layout.key (tree (k + 1)) ∉ keysOf H)
    (hpos : ∃ family : Family (Bits lambda) (Bits lambda), Matches family (new ++ H)) (q : Nat)
    (hlen : (new ++ H).length ≤ q) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c) (K : Finset (Bits lambda)) :
    ((posterior (new ++ H)).map (fun f =>
        decide (layout.key (layout.output
          (f (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false)))) ∈ K) ||
        decide (layout.key (layout.output
          (f (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true)))) ∈ K))) true ≤
      2 * (((c * K.card : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) := by
  refine (ForkEventUnion.map_or_le _ _ _).trans ?_
  rw [two_mul]
  exact add_le_add (child_key_le layout variant salt hin hl L hL k hk H new hnew tree hkey hpos q hlen c hfiber K false)
    (child_key_le layout variant salt hin hl L hL k hk H new hnew tree hkey hpos q hlen c hfiber K true)

/-- The updated tree is good at the next step when the tree is good and the
children's keys are outside the set. -/
theorem good_step (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (K : Finset (Bits lambda))
    (k : Nat) (tree : Nat → Seed lambda) (hgood : Good layout K k tree) (left right : Seed lambda)
    (hleft : layout.key left ∉ K) (hright : layout.key right ∉ K) :
    Good layout K (k + 1) (Function.update (Function.update tree (2 * (k + 1)) left) (2 * (k + 1) + 1) right) := by
  intro b hb
  by_cases h1 : b = 2 * (k + 1) + 1
  · subst h1
    rw [Function.update_self]
    exact hright
  · rw [Function.update_of_ne h1]
    by_cases h2 : b = 2 * (k + 1)
    · subst h2
      rw [Function.update_self]
      exact hleft
    · rw [Function.update_of_ne h2]
      exact hgood b (by omega)

end
end SDitH.Proofs.TreeStepFresh
