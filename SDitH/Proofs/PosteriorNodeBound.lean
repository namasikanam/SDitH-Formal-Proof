import SDitH.Proofs.FiberCountingSided
import SDitH.Proofs.NodeExchange
import SDitH.Proofs.TreeExchange
import SDitH.Proofs.TreeStepFresh

/-! The posterior bound on a hidden node's block. Fix a possible history, a
parent seed and a block. Against the posterior family, for a weight that is
at most one and is invariant under the exchange of the node's block on the
good fiber, the weighted mass of the fiber in which the parent is the seed
and the node's block is the block is at most the total weight over the
number of blocks less the bad targets: the exchange with a target block is
a posterior-preserving map carrying the good fiber to the target's fiber
without changing the weight, unless the target's key is among the
history's, the parent's or the tree's keys or the target is the sibling's
block. -/

namespace SDitH.Proofs.PosteriorNodeBound

open Spec.SeedTree Spec.BAVCCipherProgram Spec.DomainSeparation Spec.SeedPrimitives
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode NodeExchange TreeExchange CipherResample ChargeExpect FiberCounting FiberCountingBad
open FiberCountingSided TreeStepFresh ChargeCutExpect
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat} (layout : Layout lambda (Bits lambda) (Bits lambda)) (hin : Function.Injective layout.input)
  (hl : 26 ≤ lambda) (L : Nat) (hL : 4 * L ≤ 2 ^ 24) (variant : Grinding) (salt root : Bits lambda)
  (b : Nat) (hb : 1 < b) (hbL : b < 2 * L) (q v : Bits lambda)

/-- The fiber: the parent is the seed and the node's block is the block. -/
def OnFiber (g : Family (Bits lambda) (Bits lambda)) : Prop :=
  node (treeExpand layout g variant salt) root (b / 2) = q ∧ nodeBlock layout g variant salt root b = v

/-- The goodness of a family for the fixed parent key and block key. -/
def Good (g : Family (Bits lambda) (Bits lambda)) : Prop :=
  (∀ c, 1 ≤ c → c < 2 * L → c ≠ b / 2 → layout.key (node (treeExpand layout g variant salt) root c) ≠ layout.key q) ∧
  (∀ c, 1 ≤ c → c < 2 * L → c ≠ b →
    layout.key (node (treeExpand layout g variant salt) root c) ≠ layout.key (layout.output v))

/-- A bad target block for a family: its key is the parent's, one of the
tree's, or fresh nowhere, or it is the sibling's block. -/
def Bad (H₀ : List (Entry (Bits lambda) (Bits lambda))) (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) : Prop :=
  layout.key (layout.output v') ∈ keysOf H₀ ∨ layout.key (layout.output v') = layout.key q ∨
  (∃ c, c < 2 * L ∧ layout.key (node (treeExpand layout g variant salt) root c) = layout.key (layout.output v')) ∨
  (∃ c, c < 2 * L ∧ c / 2 = b / 2 ∧ c ≠ b ∧ g (layout.key q) (layout.input (nodeTweak variant salt c)) = v')

/-- The exchange with a target block, as a fixed map on families. -/
def exchangeTo (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) : Family (Bits lambda) (Bits lambda) :=
  swapNode (layout.key q) v v' (layout.key (layout.output v)) (layout.key (layout.output v')) g

omit hin hl hL hb hbL in
/-- On the fiber the exchange is the family's exchange of the node. -/
theorem exchangeTo_eq (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) (hg : OnFiber layout variant salt root b q v g) :
    exchangeTo layout q v v' g = exchanged layout g variant salt root b v' := by
  unfold exchangeTo exchanged
  have hparent : parentKey layout g variant salt root b = layout.key q := by
    unfold parentKey
    rw [hg.1]
  rw [hparent, hg.2]

include hin hl hL hb hbL in
/-- The goodness hypotheses of the node exchange on the good fiber. -/
theorem goodness (H₀ : List (Entry (Bits lambda) (Bits lambda))) (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hg : OnFiber layout variant salt root b q v g)
    (hgood : Good layout L variant salt root b q v g) (hbad : ¬ Bad layout L variant salt root b q H₀ v' g)
    (hpκ : layout.key q ≠ layout.key (layout.output v)) :
    ∀ c, c < 2 * L →
      node (treeExpand layout (exchanged layout g variant salt root b v') variant salt) root c =
        if c = b then layout.output v' else node (treeExpand layout g variant salt) root c := by
  have hparent : parentKey layout g variant salt root b = layout.key q := by
    unfold parentKey
    rw [hg.1]
  simp only [Bad, not_or, not_exists, not_and] at hbad
  obtain ⟨-, hbp, hb3, hb4⟩ := hbad
  refine node_exchanged layout hin hl L hL g variant salt root b hb hbL v' ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hparent, hg.2]
    exact hpκ
  · rw [hparent]
    exact fun h => hbp h.symm
  · intro c h1 hc hcb
    rw [hparent]
    exact hgood.1 c h1 hc hcb
  · intro c h1 hc hcb
    rw [hg.2]
    exact hgood.2 c h1 hc hcb
  · intro c _ hc
    exact hb3 c hc
  · intro c hc hsib hcb
    rw [hparent]
    exact hb4 c hc hsib hcb


/-- The label: the parent and the node's block when the family is good. -/
def label (g : Family (Bits lambda) (Bits lambda)) : Option (Bits lambda × Bits lambda) :=
  if Good layout L variant salt root b q v g then
    some (node (treeExpand layout g variant salt) root (b / 2), nodeBlock layout g variant salt root b)
  else none

omit hin hl hL hb hbL in
theorem label_eq_iff (g : Family (Bits lambda) (Bits lambda)) :
    label layout L variant salt root b q v g = some (q, v) ↔
      Good layout L variant salt root b q v g ∧ OnFiber layout variant salt root b q v g := by
  unfold label OnFiber
  split
  · simp [*]
  · simp [*]

include hin hl hL hb hbL in
/-- The label of the exchanged family on the good fiber. -/
theorem label_exchangeTo (H₀ : List (Entry (Bits lambda) (Bits lambda))) (hpκ : layout.key q ≠ layout.key (layout.output v))
    (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda)) (hg : OnFiber layout variant salt root b q v g)
    (hgood : Good layout L variant salt root b q v g) (hbad : ¬ Bad layout L variant salt root b q H₀ v' g) :
    label layout L variant salt root b q v (exchangeTo layout q v v' g) = some (q, v') := by
  have hnode := goodness layout hin hl L hL variant salt root b hb hbL q v H₀ v' g hg hgood hbad hpκ
  have hparent : parentKey layout g variant salt root b = layout.key q := by
    unfold parentKey
    rw [hg.1]
  have hblock : g (layout.key q) (layout.input (nodeTweak variant salt b)) = v := by
    have := hg.2
    unfold nodeBlock at this
    rw [hparent] at this
    exact this
  have hhalf : node (treeExpand layout (exchanged layout g variant salt root b v') variant salt) root (b / 2) = q := by
    rw [hnode (b / 2) (by omega), if_neg (by omega), hg.1]
  have hgood' : Good layout L variant salt root b q v (exchanged layout g variant salt root b v') := by
    simp only [Bad, not_or, not_exists, not_and] at hbad
    obtain ⟨-, hbp, -, -⟩ := hbad
    constructor
    · intro c h1 hc hcb
      rw [hnode c hc]
      by_cases hcb' : c = b
      · rw [if_pos hcb']
        exact hbp
      · rw [if_neg hcb']
        exact hgood.1 c h1 hc hcb
    · intro c h1 hc hcb
      rw [hnode c hc, if_neg hcb]
      exact hgood.2 c h1 hc hcb
  rw [exchangeTo_eq layout variant salt root b q v v' g hg]
  unfold label
  rw [if_pos hgood', hhalf]
  congr 2
  unfold nodeBlock parentKey
  rw [hhalf]
  show exchanged layout g variant salt root b v' (layout.key q) (layout.input (nodeTweak variant salt b)) = v'
  unfold exchanged
  rw [hparent, hg.2, swapNode_apply_parent]
  simp only [Equiv.trans_apply]
  rw [hblock]
  convert Equiv.swap_apply_left v v'

/-- The sibling's address: the only other address with the same parent. -/
theorem sibling_unique (c c' : Nat) (hc : c / 2 = b / 2) (hc' : c' / 2 = b / 2) (hcb : c ≠ b) (hcb' : c' ≠ b) : c = c' := by
  omega

omit hin hl hL hb hbL in
/-- The bad targets of a family number at most the fiber bound times the
keys of the history, the parent and the tree, plus one. -/
theorem bad_card_le (H₀ : List (Entry (Bits lambda) (Bits lambda))) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c)
    (g : Family (Bits lambda) (Bits lambda)) :
    (Finset.univ.filter fun v' => Bad layout L variant salt root b q H₀ v' g).card ≤
      c * ((keysOf H₀).card + 1 + 2 * L) + 1 := by
  set K : Finset (Bits lambda) := keysOf H₀ ∪ {layout.key q} ∪
    (Finset.range (2 * L)).image fun c => layout.key (node (treeExpand layout g variant salt) root c) with hK
  have hKcard : K.card ≤ (keysOf H₀).card + 1 + 2 * L := by
    calc K.card ≤ (keysOf H₀ ∪ {layout.key q}).card +
          ((Finset.range (2 * L)).image fun c => layout.key (node (treeExpand layout g variant salt) root c)).card :=
          Finset.card_union_le _ _
      _ ≤ ((keysOf H₀).card + 1) + 2 * L := by
          refine add_le_add ((Finset.card_union_le _ _).trans ?_) (Finset.card_image_le.trans (by simp))
          simp
  have hsub : (Finset.univ.filter fun v' => Bad layout L variant salt root b q H₀ v' g) ⊆
      (Finset.univ.filter fun v' => layout.key (layout.output v') ∈ K) ∪
        ((Finset.range (2 * L)).filter fun c => c / 2 = b / 2 ∧ c ≠ b).image
          fun c => g (layout.key q) (layout.input (nodeTweak variant salt c)) := by
    intro v' hv'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv'
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    rcases hv' with h | h | ⟨c, hc, h⟩ | ⟨c, hc, hsib, hcb, h⟩
    · left
      simp [hK, h]
    · left
      simp [hK, h]
    · left
      simp only [hK, Finset.mem_union, Finset.mem_image, Finset.mem_range]
      exact Or.inr ⟨c, hc, h⟩
    · right
      exact ⟨c, ⟨hc, hsib, hcb⟩, h⟩
  have hsibcard : (((Finset.range (2 * L)).filter fun c => c / 2 = b / 2 ∧ c ≠ b).image
      fun c => g (layout.key q) (layout.input (nodeTweak variant salt c))).card ≤ 1 := by
    refine Finset.card_image_le.trans (Finset.card_le_one.mpr fun c hc c' hc' => ?_)
    simp only [Finset.mem_filter] at hc hc'
    exact sibling_unique b c c' hc.2.1 hc'.2.1 hc.2.2 hc'.2.2
  have hhits : (Finset.univ.filter fun v' => layout.key (layout.output v') ∈ K).card ≤ c * K.card := by
    have h := count_key_hits layout c hfiber K (Subtype.fintype fun r => layout.key (layout.output r) ∈ K)
    rw [Fintype.card_subtype] at h
    convert h using 2
  calc (Finset.univ.filter fun v' => Bad layout L variant salt root b q H₀ v' g).card
      ≤ ((Finset.univ.filter fun v' => layout.key (layout.output v') ∈ K) ∪
          ((Finset.range (2 * L)).filter fun c => c / 2 = b / 2 ∧ c ≠ b).image
            fun c => g (layout.key q) (layout.input (nodeTweak variant salt c))).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun v' => layout.key (layout.output v') ∈ K).card + 1 :=
        (Finset.card_union_le _ _).trans (add_le_add_right hsibcard _)
    _ ≤ c * K.card + 1 := add_le_add_left hhits _
    _ ≤ c * ((keysOf H₀).card + 1 + 2 * L) + 1 := add_le_add_left (Nat.mul_le_mul_left c hKcard) _


section Counting

variable {α γ : Type*}

omit layout hin hl hL variant salt root hb hbL q v in
/-- A sum of weighted means is the mean of the weighted sum. -/
theorem sum_mean_mul (p : PMF α) (ψ : α → ℝ≥0∞) (F : γ → α → ℝ≥0∞) (T : Finset γ) :
    ∑ v' ∈ T, mean p (fun a => ψ a * F v' a) = mean p (fun a => ψ a * ∑ v' ∈ T, F v' a) := by
  induction T using Finset.induction_on with
  | empty => simp [mean_const]
  | insert v T hv ih =>
    rw [Finset.sum_insert hv, ih]
    simp only [Finset.sum_insert hv, mul_add]
    rw [mean_add]

omit layout hin hl hL variant salt root hb hbL q v in
/-- The sum over a set of targets of the bad-target masses. -/
theorem sum_bad_mass_on (p : PMF α) (ψ : α → ℝ≥0∞) (Bad : γ → α → Prop) (T : Finset γ) :
    ∑ v' ∈ T, mean p (fun a => ψ a * indicator (decide (Bad v' a))) =
      mean p (fun a => ψ a * ((T.filter fun v' => Bad v' a).card : ℝ≥0∞)) := by
  have hcount : ∀ a, ((T.filter fun v' => Bad v' a).card : ℝ≥0∞) = ∑ v' ∈ T, indicator (decide (Bad v' a)) := by
    intro a
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun v' _ => ?_
    by_cases h : Bad v' a <;> simp [h, indicator]
  simp only [hcount]
  exact sum_mean_mul p ψ (fun v' a => indicator (decide (Bad v' a))) T

omit layout hin hl hL variant salt root hb hbL q v in
/-- A label value's mass when exchanged with all targets of a set but a
bounded number of bad ones. -/
theorem label_mass_le_of_bad_on (p : PMF α) (φ : α → ℝ≥0∞) (hφ : ∀ a, φ a ≤ 1) (ℓ : α → γ) (v : γ)
    (T : Finset γ) (Bad : γ → α → Prop) (M : ℕ) (hM : ∀ a, (T.filter fun v' => Bad v' a).card ≤ M)
    (h : ∀ v' ∈ T, mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (¬ Bad v' a))) ≤
      mean p (fun a => φ a * indicator (decide (ℓ a = v')))) :
    ((T.card - M : ℕ) : ℝ≥0∞) * mean p (fun a => φ a * indicator (decide (ℓ a = v))) ≤ mean p φ := by
  set m := mean p (fun a => φ a * indicator (decide (ℓ a = v))) with hm
  have hmle : m ≤ 1 := mean_le_const _ _ 1 fun a _ => by
    calc φ a * indicator (decide (ℓ a = v)) ≤ 1 * 1 :=
          mul_le_mul' (hφ a) (by by_cases h : ℓ a = v <;> simp [h, indicator])
      _ = 1 := mul_one _
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hmle
  have hsplit : (T.card : ℝ≥0∞) * m ≤ mean p φ + (M : ℝ≥0∞) * m := by
    have hsum : (T.card : ℝ≥0∞) * m = ∑ v' ∈ T, m := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    calc ∑ v' ∈ T, m
        = ∑ v' ∈ T, (mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (¬ Bad v' a))) +
            mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (Bad v' a)))) :=
          Finset.sum_congr rfl fun v' _ => mean_split p _ (Bad v')
      _ = ∑ v' ∈ T, mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (¬ Bad v' a))) +
            ∑ v' ∈ T, mean p (fun a => φ a * indicator (decide (ℓ a = v)) * indicator (decide (Bad v' a))) :=
          Finset.sum_add_distrib
      _ ≤ ∑ v' ∈ T, mean p (fun a => φ a * indicator (decide (ℓ a = v'))) +
            mean p (fun a => φ a * indicator (decide (ℓ a = v)) * ((T.filter fun v' => Bad v' a).card : ℝ≥0∞)) :=
          add_le_add (Finset.sum_le_sum fun v' hv' => h v' hv') (le_of_eq (sum_bad_mass_on p _ Bad T))
      _ ≤ mean p φ + mean p (fun a => φ a * indicator (decide (ℓ a = v)) * (M : ℝ≥0∞)) :=
          add_le_add (sum_label_le p φ ℓ T) (mean_le_mean _ _ _ fun a _ =>
            mul_le_mul' le_rfl (Nat.cast_le.mpr (hM a)))
      _ = mean p φ + (M : ℝ≥0∞) * m := by
          rw [show (fun a => φ a * indicator (decide (ℓ a = v)) * (M : ℝ≥0∞)) =
            fun a => (M : ℝ≥0∞) * (φ a * indicator (decide (ℓ a = v))) from funext fun a => mul_comm _ _, mean_mul_left]
  calc ((T.card - M : ℕ) : ℝ≥0∞) * m ≤ (T.card : ℝ≥0∞) * m - (M : ℝ≥0∞) * m := by
        rw [ENNReal.natCast_sub, ENNReal.sub_mul fun _ _ => hmtop]
    _ ≤ mean p φ := tsub_le_iff_right.mpr hsplit

end Counting

/-- A bad target among the labels: a label not of the parent's fiber, or a
bad block. -/
def BadT (H₀ : List (Entry (Bits lambda) (Bits lambda))) (t : Option (Bits lambda × Bits lambda))
    (g : Family (Bits lambda) (Bits lambda)) : Prop :=
  ∀ v', t = some (q, v') → Bad layout L variant salt root b q H₀ v' g

include hin hl hL hb hbL in
/-- The posterior bound on the node's block: the weighted mass of the good
fiber at the block is at most the total weight over the number of blocks
less the bad targets. -/
theorem posterior_node_bound (H₀ : List (Entry (Bits lambda) (Bits lambda)))
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g H₀)
    (hfp : ∀ e ∈ H₀, e.key ≠ layout.key q) (hfκ : ∀ e ∈ H₀, e.key ≠ layout.key (layout.output v))
    (hpκ : layout.key q ≠ layout.key (layout.output v))
    (W : Family (Bits lambda) (Bits lambda) → ℝ≥0∞) (hW : ∀ g, W g ≤ 1)
    (hWex : ∀ v' g, OnFiber layout variant salt root b q v g → Good layout L variant salt root b q v g →
      ¬ Bad layout L variant salt root b q H₀ v' g → W g ≤ W (exchanged layout g variant salt root b v'))
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf H₀).card + 1 + 2 * L) + 1) : ℕ) : ℝ≥0∞) *
        mean (posterior H₀) (fun g => W g * indicator (decide (label layout L variant salt root b q v g = some (q, v)))) ≤
      mean (posterior H₀) W := by
  have hinj : Function.Injective fun v' : Bits lambda => (some (q, v') : Option (Bits lambda × Bits lambda)) :=
    fun x y h => by simpa using h
  have hT : (Finset.univ.image fun v' : Bits lambda => (some (q, v') : Option (Bits lambda × Bits lambda))).card =
      Fintype.card (Bits lambda) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [← hT]
  convert label_mass_le_of_bad_on (posterior H₀) W hW (label layout L variant salt root b q v) (some (q, v)) _
    (BadT layout L variant salt root b q H₀) (c * ((keysOf H₀).card + 1 + 2 * L) + 1) (fun g => ?_) (fun t ht => ?_)
    using 3
  · -- the same weight up to the decidability of the label test
    funext g
    congr
  · -- the bad targets' count
    rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
    refine (Finset.card_le_card fun v' hv' => ?_).trans (bad_card_le layout L variant salt root b q H₀ c hfiber g)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv' ⊢
    exact hv' v' rfl
  · -- the exchange with a target
    obtain ⟨v', -, rfl⟩ := Finset.mem_image.mp
      (by assumption : t ∈ Finset.univ.image fun v' : Bits lambda => (some (q, v') : Option (Bits lambda × Bits lambda)))
    by_cases hglob : layout.key (layout.output v') ∈ keysOf H₀ ∨ layout.key (layout.output v') = layout.key q
    · refine le_trans (le_of_eq ((mean_le_const _ _ 0 fun g _ => ?_).antisymm (zero_le _))) (zero_le _)
      have hbad : BadT layout L variant salt root b q H₀ (some (q, v')) g := by
        intro v'' hv''
        simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hv''
        subst hv''
        rcases hglob with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      simp [hbad, indicator]
    · push_neg at hglob
      have hfκ' : ∀ e ∈ H₀, e.key ≠ layout.key (layout.output v') := fun e he h =>
        hglob.1 (by rw [← h]; exact mem_keysOf.mpr ⟨e, he, rfl⟩)
      have hp' : layout.key q ≠ layout.key (layout.output v') := fun h => hglob.2 h.symm
      have hmap : (posterior H₀).map (exchangeTo layout q v v') = posterior H₀ :=
        posterior_swapNode _ _ _ _ _ H₀ hpos hpκ hp' hfp hfκ hfκ'
      refine mean_label_le_of_map (posterior H₀) _ hmap W _ (some (q, v)) (some (q, v'))
        (BadT layout L variant salt root b q H₀ (some (q, v'))) ?_ ?_
      · intro g hg hbad
        obtain ⟨hgood, hfib⟩ := (label_eq_iff layout L variant salt root b q v g).mp hg
        have hbad' : ¬ Bad layout L variant salt root b q H₀ v' g := fun h => hbad fun v'' hv'' => by
          simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hv''
          subst hv''
          exact h
        rw [exchangeTo_eq layout variant salt root b q v v' g hfib]
        exact hWex v' g hfib hgood hbad'
      · intro g hg hbad
        obtain ⟨hgood, hfib⟩ := (label_eq_iff layout L variant salt root b q v g).mp hg
        have hbad' : ¬ Bad layout L variant salt root b q H₀ v' g := fun h => hbad fun v'' hv'' => by
          simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hv''
          subst hv''
          exact h
        exact label_exchangeTo layout hin hl L hL variant salt root b hb hbL q v H₀ hpκ v' g hfib hgood hbad'

end
end SDitH.Proofs.PosteriorNodeBound
