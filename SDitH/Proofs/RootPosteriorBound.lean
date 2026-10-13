import SDitH.Proofs.PosteriorNodeBound
import SDitH.Proofs.ProductSwap
import SDitH.Proofs.RootExchange

/-! The posterior bound on the root. Against the joint draw of a uniform
root and the posterior family, for a weight at most one that does not
decrease under the root exchange on the good fiber, the weighted mass of
the good pairs with a given root is at most the total weight over the
number of seeds less the bad targets: exchanging the root with a target
seed while swapping the two roots' keys preserves the joint draw and
carries the good fiber to the target's, unless the target's key is among
the history's or the tree's keys. -/

namespace SDitH.Proofs.RootPosteriorBound

open Spec.SeedTree Spec.BAVCCipherProgram Spec.DomainSeparation Spec.SeedPrimitives
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode KeySwap RootExchange ProductSwap CipherResample ChargeExpect FiberCounting FiberCountingBad
open FiberCountingSided TreeStepFresh ChargeCutExpect PosteriorNodeBound
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat} (layout : Layout lambda (Bits lambda) (Bits lambda)) (L : Nat) (variant : Grinding) (salt : Bits lambda)

/-- The joint draw of a uniform root and the posterior family. -/
def rootDraw (H₀ : List (Entry (Bits lambda) (Bits lambda))) : PMF (Bits lambda × Family (Bits lambda) (Bits lambda)) :=
  product (PMF.uniformOfFintype (Bits lambda)) (posterior H₀)

/-- The goodness of a pair: no node of the tree below the root has the
root's key. -/
def GoodR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : Prop :=
  ∀ c, 2 ≤ c → c < 2 * L → layout.key (node (treeExpand layout x.2 variant salt) x.1 c) ≠ layout.key x.1

/-- A bad target root for a pair: its key is among the history's or the
tree's keys. -/
def BadR (H₀ : List (Entry (Bits lambda) (Bits lambda))) (root' : Bits lambda)
    (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : Prop :=
  layout.key root' ∈ keysOf H₀ ∨
    ∃ c, c < 2 * L ∧ layout.key (node (treeExpand layout x.2 variant salt) x.1 c) = layout.key root'

/-- The exchange with a target root, as a fixed map on pairs. -/
def exchangeR (root root' : Bits lambda) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    Bits lambda × Family (Bits lambda) (Bits lambda) :=
  (Equiv.swap root root' x.1, swapKeys (layout.key root) (layout.key root') x.2)

/-- On the fiber the exchange is the root exchange. -/
theorem exchangeR_eq (root root' : Bits lambda) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) (hx : x.1 = root) :
    exchangeR layout root root' x = (root', rootExchanged layout x.2 root root') := by
  unfold exchangeR rootExchanged
  rw [hx, Equiv.swap_apply_left]

/-- The label: the root when the pair is good. -/
def labelR (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : Option (Bits lambda) :=
  if GoodR layout L variant salt x then some x.1 else none

theorem labelR_eq_iff (x : Bits lambda × Family (Bits lambda) (Bits lambda)) (root : Bits lambda) :
    labelR layout L variant salt x = some root ↔ GoodR layout L variant salt x ∧ x.1 = root := by
  unfold labelR
  split
  · simp [*]
  · simp [*]

/-- The tree of the exchanged pair on the good fiber with a target that is
not bad: the new root, then the old tree. -/
theorem node_exchangeR (H₀ : List (Entry (Bits lambda) (Bits lambda))) (root root' : Bits lambda)
    (x : Bits lambda × Family (Bits lambda) (Bits lambda)) (hx : x.1 = root) (hgood : GoodR layout L variant salt x)
    (hbad : ¬ BadR layout L variant salt H₀ root' x) :
    ∀ c, c < 2 * L →
      node (treeExpand layout (rootExchanged layout x.2 root root') variant salt) root' c =
        if c ≤ 1 then root' else node (treeExpand layout x.2 variant salt) x.1 c := by
  simp only [BadR, not_or, not_exists, not_and] at hbad
  obtain ⟨-, hb2⟩ := hbad
  subst hx
  exact node_root_exchanged layout x.2 variant salt x.1 root' L (fun c h2 hc => hgood c h2 hc) (fun c _ hc => hb2 c hc)

/-- The label of the exchanged pair on the good fiber. -/
theorem labelR_exchangeR (H₀ : List (Entry (Bits lambda) (Bits lambda))) (root root' : Bits lambda)
    (x : Bits lambda × Family (Bits lambda) (Bits lambda)) (hx : x.1 = root) (hgood : GoodR layout L variant salt x)
    (hbad : ¬ BadR layout L variant salt H₀ root' x) :
    labelR layout L variant salt (exchangeR layout root root' x) = some root' := by
  rw [exchangeR_eq layout root root' x hx]
  have hnode := node_exchangeR layout L variant salt H₀ root root' x hx hgood hbad
  have hgood' : GoodR layout L variant salt (root', rootExchanged layout x.2 root root') := by
    intro c h2 hc
    show layout.key (node (treeExpand layout (rootExchanged layout x.2 root root') variant salt) root' c) ≠ layout.key root'
    rw [hnode c hc, if_neg (by omega)]
    simp only [BadR, not_or, not_exists, not_and] at hbad
    exact hbad.2 c hc
  unfold labelR
  rw [if_pos hgood']

/-- The seeds whose key lies in a finite set number at most the fiber bound
times the set's size. -/
theorem count_root_hits (c : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // layout.key r = κ} ≤ c)
    (K : Finset (Bits lambda)) :
    (Finset.univ.filter fun r : Bits lambda => layout.key r ∈ K).card ≤ c * K.card := by
  refine Finset.card_le_mul_card_image_of_maps_to (f := fun r => layout.key r) (t := K)
    (fun r hr => (Finset.mem_filter.mp hr).2) c (fun κ _ => ?_)
  calc _ ≤ (Finset.univ.filter fun r : Bits lambda => layout.key r = κ).card :=
        Finset.card_le_card fun r hr => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          exact hr.2
    _ = Fintype.card {r : Bits lambda // layout.key r = κ} := (Fintype.card_subtype _).symm
    _ ≤ c := hfiberR κ

/-- The bad targets of a pair number at most the fiber bound times the keys
of the history and the tree. -/
theorem badR_card_le (H₀ : List (Entry (Bits lambda) (Bits lambda))) (c : Nat)
    (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // layout.key r = κ} ≤ c)
    (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    (Finset.univ.filter fun root' => BadR layout L variant salt H₀ root' x).card ≤ c * ((keysOf H₀).card + 2 * L) := by
  set K : Finset (Bits lambda) := keysOf H₀ ∪
    (Finset.range (2 * L)).image fun c => layout.key (node (treeExpand layout x.2 variant salt) x.1 c) with hK
  have hKcard : K.card ≤ (keysOf H₀).card + 2 * L := by
    calc K.card ≤ (keysOf H₀).card +
          ((Finset.range (2 * L)).image fun c => layout.key (node (treeExpand layout x.2 variant salt) x.1 c)).card :=
          Finset.card_union_le _ _
      _ ≤ (keysOf H₀).card + 2 * L := Nat.add_le_add_left (Finset.card_image_le.trans (Finset.card_range _).le) _
  have hsub : (Finset.univ.filter fun root' => BadR layout L variant salt H₀ root' x) ⊆
      Finset.univ.filter fun root' => layout.key root' ∈ K := by
    intro v' hv'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv' ⊢
    rcases hv' with h | ⟨c, hc, h⟩
    · simp [hK, h]
    · simp only [hK, Finset.mem_union, Finset.mem_image, Finset.mem_range]
      exact Or.inr ⟨c, hc, h⟩
  calc _ ≤ (Finset.univ.filter fun root' => layout.key root' ∈ K).card := Finset.card_le_card hsub
    _ ≤ c * K.card := count_root_hits layout c hfiberR K
    _ ≤ c * ((keysOf H₀).card + 2 * L) := Nat.mul_le_mul_left c hKcard

/-- The joint draw is invariant under the exchange when both roots' keys
are fresh. -/
theorem rootDraw_map_exchangeR (H₀ : List (Entry (Bits lambda) (Bits lambda)))
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g H₀) (root root' : Bits lambda)
    (hfκ : ∀ e ∈ H₀, e.key ≠ layout.key root) (hfκ' : ∀ e ∈ H₀, e.key ≠ layout.key root') :
    (rootDraw H₀).map (exchangeR layout root root') = rootDraw H₀ := by
  unfold rootDraw exchangeR
  convert product_map_eq _ _ _ _ (uniform_map_swap root root')
    (posterior_swapKeys (layout.key root) (layout.key root') H₀ hpos hfκ hfκ') using 7

/-- A bad target among the labels. -/
def BadTR (H₀ : List (Entry (Bits lambda) (Bits lambda))) (t : Option (Bits lambda))
    (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : Prop :=
  ∀ root', t = some root' → BadR layout L variant salt H₀ root' x

/-- The posterior bound on the root: the weighted mass of the good pairs
with the root is at most the total weight over the number of seeds less
the bad targets. -/
theorem posterior_root_bound (H₀ : List (Entry (Bits lambda) (Bits lambda)))
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g H₀) (root : Bits lambda)
    (hfκ : ∀ e ∈ H₀, e.key ≠ layout.key root)
    (W : Bits lambda × Family (Bits lambda) (Bits lambda) → ℝ≥0∞) (hW : ∀ x, W x ≤ 1)
    (hWex : ∀ root' x, x.1 = root → GoodR layout L variant salt x → ¬ BadR layout L variant salt H₀ root' x →
      W x ≤ W (root', rootExchanged layout x.2 root root'))
    (c : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // layout.key r = κ} ≤ c) :
    ((Fintype.card (Bits lambda) - c * ((keysOf H₀).card + 2 * L) : ℕ) : ℝ≥0∞) *
        mean (rootDraw H₀) (fun x => W x * indicator (decide (labelR layout L variant salt x = some root))) ≤
      mean (rootDraw H₀) W := by
  have hinj : Function.Injective fun r : Bits lambda => (some r : Option (Bits lambda)) :=
    fun x y h => by simpa using h
  have hT : (Finset.univ.image fun r : Bits lambda => (some r : Option (Bits lambda))).card =
      Fintype.card (Bits lambda) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [← hT]
  convert label_mass_le_of_bad_on (rootDraw H₀) W hW (labelR layout L variant salt) (some root) _
    (BadTR layout L variant salt H₀) (c * ((keysOf H₀).card + 2 * L)) (fun x => ?_) (fun t ht => ?_)
    using 3
  · -- the same weight up to the decidability of the label test
    funext x
    congr
  · -- the bad targets' count
    rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
    refine (Finset.card_le_card fun r hr => ?_).trans (badR_card_le layout L variant salt H₀ c hfiberR x)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact hr r rfl
  · -- the exchange with a target
    obtain ⟨root', -, rfl⟩ := Finset.mem_image.mp
      (by assumption : t ∈ Finset.univ.image fun r : Bits lambda => (some r : Option (Bits lambda)))
    by_cases hglob : layout.key root' ∈ keysOf H₀
    · refine le_trans (le_of_eq ((mean_le_const _ _ 0 fun x _ => ?_).antisymm (zero_le _))) (zero_le _)
      have hbad : BadTR layout L variant salt H₀ (some root') x := by
        intro r hr
        simp only [Option.some.injEq] at hr
        subst hr
        exact Or.inl hglob
      simp [hbad, indicator]
    · have hfκ' : ∀ e ∈ H₀, e.key ≠ layout.key root' := fun e he h =>
        hglob (by rw [← h]; exact mem_keysOf.mpr ⟨e, he, rfl⟩)
      have hmap := rootDraw_map_exchangeR layout H₀ hpos root root' hfκ hfκ'
      refine mean_label_le_of_map (rootDraw H₀) _ hmap W _ (some root) (some root')
        (BadTR layout L variant salt H₀ (some root')) ?_ ?_
      · intro x hx hbad
        obtain ⟨hgood, hfib⟩ := (labelR_eq_iff layout L variant salt x root).mp hx
        have hbad' : ¬ BadR layout L variant salt H₀ root' x := fun h => hbad fun r hr => by
          simp only [Option.some.injEq] at hr
          subst hr
          exact h
        rw [exchangeR_eq layout root root' x hfib]
        exact hWex root' x hfib hgood hbad'
      · intro x hx hbad
        obtain ⟨hgood, hfib⟩ := (labelR_eq_iff layout L variant salt x root).mp hx
        have hbad' : ¬ BadR layout L variant salt H₀ root' x := fun h => hbad fun r hr => by
          simp only [Option.some.injEq] at hr
          subst hr
          exact h
        exact labelR_exchangeR layout L variant salt H₀ root root' x hfib hgood hbad'

end
end SDitH.Proofs.RootPosteriorBound
