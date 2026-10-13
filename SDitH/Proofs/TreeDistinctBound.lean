import SDitH.Proofs.TreeGoodInduction
import SDitH.Proofs.TreeRunClosed
import SDitH.Proofs.CommitHistoryKeys
import SDitH.Proofs.SiblingKeys

/-! The probability that the tree's keys are not fresh and pairwise distinct.
Along the expansion, each step's two children must have keys outside the
starting history's keys and the keys of the nodes so far, and distinct from
each other; under the posterior family at the history so far, each child's
key hits that set with probability at most the fiber bound times the set's
size over the remaining block count, and the two keys coincide with
probability at most the fiber bound over the remaining block count. -/

namespace SDitH.Proofs.TreeDistinctBound

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.RandomOracleTrap
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open TreeRunEntries TreeStepFresh RowStoredPosterior RowStoredAfter CipherResample RunBind RowsSupport
open PrefixOrMention RunHybrid InputPresentTail TreeGoodInduction TreeRunClosed CommitHistoryKeys SiblingKeys
open FreshKeyUniform HiddenLeafNode
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The tree's keys up to a step are outside the starting keys and pairwise
distinct. -/
def DistinctTo (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (k : Nat) (tree : Nat → Seed lambda) : Prop :=
  (∀ b, 1 ≤ b → b ≤ 2 * k + 1 → layout.key (tree b) ∉ keysOf H) ∧
  (∀ b b', 1 ≤ b → b ≤ 2 * k + 1 → 1 ≤ b' → b' ≤ 2 * k + 1 → b ≠ b' → layout.key (tree b) ≠ layout.key (tree b'))

/-- The keys so far: the starting keys and the nodes' keys up to a step. -/
def keysTo (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (k : Nat) (tree : Nat → Seed lambda) :
    Finset (Bits lambda) :=
  keysOf H ∪ (Finset.Icc 1 (2 * k + 1)).image fun b => layout.key (tree b)

theorem keysTo_card_le (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (k : Nat) (tree : Nat → Seed lambda) :
    (keysTo layout H k tree).card ≤ (keysOf H).card + (2 * k + 1) := by
  unfold keysTo
  refine (Finset.card_union_le _ _).trans (add_le_add_right (Finset.card_image_le.trans ?_) _)
  simp

/-- The event that the tree at a run's result is not distinct. -/
def notDistinct (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (steps : Nat) (root : Seed lambda)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Nat → Seed lambda))) : Bool :=
  decide (¬ DistinctTo layout H steps (treeOf root out))

/-- The updated tree is distinct at the next step when the tree is distinct,
the children's keys are outside the keys so far, and they differ. -/
theorem distinct_step (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (k : Nat) (tree : Nat → Seed lambda)
    (hd : DistinctTo layout H k tree) (left right : Seed lambda)
    (hleft : layout.key left ∉ keysTo layout H k tree) (hright : layout.key right ∉ keysTo layout H k tree)
    (hlr : layout.key left ≠ layout.key right) :
    DistinctTo layout H (k + 1) (Function.update (Function.update tree (2 * (k + 1))  left) (2 * (k + 1) + 1) right) := by
  have hleftH : layout.key left ∉ keysOf H := fun h => hleft (Finset.mem_union_left _ h)
  have hrightH : layout.key right ∉ keysOf H := fun h => hright (Finset.mem_union_left _ h)
  have hleftT : ∀ b, 1 ≤ b → b ≤ 2 * k + 1 → layout.key left ≠ layout.key (tree b) := fun b hb1 hbk h =>
    hleft (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_Icc.mpr ⟨hb1, hbk⟩, h.symm⟩))
  have hrightT : ∀ b, 1 ≤ b → b ≤ 2 * k + 1 → layout.key right ≠ layout.key (tree b) := fun b hb1 hbk h =>
    hright (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_Icc.mpr ⟨hb1, hbk⟩, h.symm⟩))
  have hval : ∀ b, 1 ≤ b → b ≤ 2 * (k + 1) + 1 →
      Function.update (Function.update tree (2 * (k + 1)) left) (2 * (k + 1) + 1) right b =
        if b = 2 * (k + 1) + 1 then right else if b = 2 * (k + 1) then left else tree b := by
    intro b _ _
    by_cases h1 : b = 2 * (k + 1) + 1
    · subst h1
      simp
    · rw [Function.update_of_ne h1, if_neg h1]
      by_cases h2 : b = 2 * (k + 1)
      · subst h2
        simp
      · rw [Function.update_of_ne h2, if_neg h2]
  constructor
  · intro b hb1 hbk
    rw [hval b hb1 hbk]
    split_ifs with h1 h2
    · exact hrightH
    · exact hleftH
    · exact hd.1 b hb1 (by omega)
  · intro b b' hb1 hbk hb1' hbk' hne
    rw [hval b hb1 hbk, hval b' hb1' hbk']
    split_ifs
    all_goals first
      | (exfalso; omega)
      | exact hlr.symm
      | exact hlr
      | exact (hrightT b' hb1' (by omega))
      | exact (hleftT b' hb1' (by omega))
      | exact (hrightT b hb1 (by omega)).symm
      | exact (hleftT b hb1 (by omega)).symm
      | exact hd.2 b b' hb1 (by omega) hb1' (by omega) hne

/-- The keys of the expansion's recorded entries are the keys of expanded
nodes of the tree so far. -/
theorem treeHistory_key_le (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (family : Family (Bits lambda) (Bits lambda)) (variant : Grinding) (salt root : Bits lambda) (k : Nat)
    (e : Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))
    (he : e ∈ treeHistory layout family variant salt root (fun _ => root) k) :
    ∃ c, 1 ≤ c ∧ c ≤ k ∧ e.key = layout.key (Spec.SeedTree.run (treeExpand layout family variant salt) root (fun _ => root) k c) := by
  obtain ⟨c, h1, hk, hc⟩ := treeHistory_key layout family variant salt root (fun _ => root) k e he
  refine ⟨c, h1, hk, ?_⟩
  rw [hc, SDitH.Proofs.SeedTree.run_matches_node _ _ _ _ _ (by omega) (by omega)]

/-- The tree's keys are not distinct with probability at most the root's
indicator plus the steps times the step bound. -/
theorem tree_distinct_le (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt root : Bits lambda) (hin : Function.Injective layout.input) (hl : 26 ≤ lambda) (L : Nat) (hL : 4 * L ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c)
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (hpos : ∃ family : Family (Bits lambda) (Bits lambda), Matches family H) (q : Nat)
    (table : List Bool → Option (Out lambda s wit rnd)) (hashes : List (List Bool × Out lambda s wit rnd))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    ∀ steps : Nat, steps ≤ L → H.length + 2 * steps + 1 ≤ q →
      ((posterior H).bind fun family =>
        (runFixed procedure family (2 * steps) (treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root (fun _ => root) steps)
          table hashes H log).map (notDistinct layout H steps root)) true ≤
      indicator (decide (layout.key root ∈ keysOf H)) +
        steps * (2 * (((c * ((keysOf H).card + 2 * L) : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) +
          (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) := by
  intro steps
  induction steps with
  | zero =>
    intro _ _
    simp only [runFixed, treeThrough, PMF.pure_map, PMF.bind_const, Nat.cast_zero, zero_mul, add_zero]
    rw [PMF.pure_apply]
    by_cases hP : layout.key root ∈ keysOf H
    · rw [decide_eq_true hP, RandomOracleTrap.indicator_true]
      split_ifs <;> simp
    · rw [decide_eq_false hP, RandomOracleTrap.indicator_false]
      have hng : ∀ R : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
          (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Nat → Seed lambda)),
          R.state = .done (Function.update (fun _ => root) 1 root) → notDistinct layout H 0 root R = false := by
        intro R hR
        unfold notDistinct treeOf
        rw [hR]
        simp only [decide_eq_false_iff_not, not_not]
        refine ⟨fun b hb1 hb => ?_, fun b b' hb1 hb hb1' hb' hne => ?_⟩
        · have : b = 1 := by omega
          subst this
          rw [Function.update_self]
          exact hP
        · omega
      rw [if_neg (by rw [hng _ rfl]; decide)]
  | succ k ih =>
    intro hk hq
    set B : ℝ≥0∞ := 2 * (((c * ((keysOf H).card + 2 * L) : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) +
      (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞) with hB
    have hstep : ((posterior H).bind fun family =>
        (runFixed procedure family (2 * k) (treeThrough layout variant salt root (fun _ => root) k)
          table hashes H log).map (notDistinct layout H k root)) true ≤
        indicator (decide (layout.key root ∈ keysOf H)) + k * B :=
      ih (by omega) (by omega)
    simp only [runFixed_tree_succ, PMF.map_bind]
    have hres := runFixed_resample procedure (2 * k) (treeThrough layout variant salt root (fun _ => root) k) table hashes
      (⟨H, hpos⟩ : Spec.IdealCipher.World (Bits lambda) (Bits lambda)) log
      (fun out family => (continueRun family 2 (expandStep layout variant salt k) out).map (notDistinct layout H (k + 1) root))
    dsimp only at hres
    rw [hres]
    calc _ ≤ ((posterior H).bind fun family =>
          (runFixed procedure family (2 * k) (treeThrough layout variant salt root (fun _ => root) k)
            table hashes H log).map (notDistinct layout H k root)) true + B := by
          refine bind_le_bind_add_const' _ _ _ _ true fun family hf => ?_
          refine bind_true_le_event_add _ _ _ B fun out hout hgood => ?_
          -- the run is the closed point
          have hclosed := tree_run_eq layout family variant salt root (fun _ => root) k table hashes H log
          rw [hclosed, PMF.mem_support_pure_iff] at hout
          subst hout
          have hgood' : DistinctTo layout H k (Spec.SeedTree.run (treeExpand layout family variant salt) root (fun _ => root) k) := by
            unfold notDistinct treeOf at hgood
            simpa using hgood
          set tree := Spec.SeedTree.run (treeExpand layout family variant salt) root (fun _ => root) k with htreedef
          set new := treeHistory layout family variant salt root (fun _ => root) k with hnewdef
          have hform : ∀ e ∈ new, TreeInput layout variant salt k e.input := by
            intro e he
            obtain ⟨new', hnew', hform'⟩ := tree_entries layout variant salt root (fun _ => root) family k table hashes H log _
              (by rw [hclosed]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
            simp only at hnew'
            have : new = new' := List.append_cancel_right hnew'
            rw [this] at he
            exact hform' e he
          have hpos' : ∃ family : Family (Bits lambda) (Bits lambda), Matches family (new ++ H) :=
            ⟨family, runFixed_cipher_matches procedure family _ _ _ _ _ _ _
              (by rw [hclosed]; exact (PMF.mem_support_pure_iff _ _).mpr rfl) (posterior_support_matches H hpos family hf)⟩
          have hlenrun : (new ++ H).length ≤ H.length + 2 * k :=
            runFixed_cipher_length_le procedure family _ _ _ _ _ _ _
              (by rw [hclosed]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
          have hlen : (new ++ H).length ≤ q := by omega
          have hlen1 : (new ++ H).length + 1 ≤ q := by omega
          have hkey : layout.key (tree (k + 1)) ∉ keysOf H := hgood'.1 (k + 1) (by omega) (by omega)
          -- the parent key is fresh in the history so far
          have hfreshp : FreshKey (⟨new ++ H, hpos'⟩ : Spec.IdealCipher.World (Bits lambda) (Bits lambda)) (layout.key (tree (k + 1))) := by
            intro e he
            rcases List.mem_append.mp he with hnew | hH
            · obtain ⟨c', hc1, hck, hc⟩ := treeHistory_key_le layout family variant salt root k e hnew
              rw [hc]
              exact hgood'.2 c' (k + 1) hc1 (by omega) (by omega) (by omega) (by omega)
            · intro h
              exact hkey (mem_keysOf.mpr ⟨e, hH, h⟩)
          have hcont : ∀ family', (continueRun family' 2 (expandStep layout variant salt k)
              ⟨.done tree, table, hashes, new ++ H, false, log⟩).map (notDistinct layout H (k + 1) root) =
              PMF.pure (notDistinct layout H (k + 1) root ⟨.done (Function.update (Function.update tree (2 * (k + 1))
                (layout.output (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false)))))
                (2 * (k + 1) + 1)
                (layout.output (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))))),
                table, hashes,
                Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) true)))
                    (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))) ::
                  Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) false)))
                    (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false))) ::
                  (new ++ H), false, log⟩) := by
            intro family'
            unfold continueRun
            simp only
            rw [PMF.map_comp, expandStep_run_eq, PMF.pure_map]
            rfl
          simp only [hcont]
          -- the step's event: a child's key among the keys so far, or the two children's keys equal
          calc _ ≤ ((posterior (new ++ H)).bind fun family' => PMF.pure
                ((decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                  (layout.input (cipherInput variant salt (k + 1) false)))) ∈ keysTo layout H k tree) ||
                decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                  (layout.input (cipherInput variant salt (k + 1) true)))) ∈ keysTo layout H k tree)) ||
                decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                  (layout.input (cipherInput variant salt (k + 1) true)))) =
                  layout.key (layout.output (family' (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) false))))))) true :=
                bind_true_le_bind_true _ _ _ fun family' _ => by
                  rw [PMF.pure_apply, PMF.pure_apply]
                  by_cases hng : notDistinct layout H (k + 1) root ⟨.done (Function.update (Function.update tree (2 * (k + 1))
                      (layout.output (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false)))))
                      (2 * (k + 1) + 1)
                      (layout.output (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))))),
                      table, hashes,
                      Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
                          (layout.input (cipherInput variant salt (k + 1) true)))
                          (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))) ::
                        Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
                          (layout.input (cipherInput variant salt (k + 1) false)))
                          (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false))) ::
                        (new ++ H), false, log⟩ = true
                  · have hor : ((decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                        (layout.input (cipherInput variant salt (k + 1) false)))) ∈ keysTo layout H k tree) ||
                        decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                          (layout.input (cipherInput variant salt (k + 1) true)))) ∈ keysTo layout H k tree)) ||
                        decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                          (layout.input (cipherInput variant salt (k + 1) true)))) =
                          layout.key (layout.output (family' (layout.key (tree (k + 1)))
                            (layout.input (cipherInput variant salt (k + 1) false)))))) = true := by
                      unfold notDistinct treeOf at hng
                      simp only [decide_eq_true_eq, Bool.or_eq_true] at hng ⊢
                      by_contra hor
                      push_neg at hor
                      exact hng (distinct_step layout H k tree hgood' _ _ hor.1.1 hor.1.2 (Ne.symm hor.2))
                    rw [hng, hor]
                  · rw [Bool.eq_false_iff.mpr hng]
                    simp
            _ ≤ B := by
                show ((posterior (new ++ H)).map fun family' =>
                  (decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) false)))) ∈ keysTo layout H k tree) ||
                  decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) true)))) ∈ keysTo layout H k tree)) ||
                  decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) true)))) =
                    layout.key (layout.output (family' (layout.key (tree (k + 1)))
                      (layout.input (cipherInput variant salt (k + 1) false)))))) true ≤ B
                refine (ForkEventUnion.map_or_le _ _ _).trans (add_le_add ?_ ?_)
                · refine (step_le layout variant salt hin hl L hL k (by omega) H new hform tree hkey hpos' q hlen c hfiber
                    (keysTo layout H k tree)).trans ?_
                  refine mul_le_mul' le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left c ?_)) _)
                  exact (keysTo_card_le layout H k tree).trans (by omega)
                · exact sibling_keys_le layout c hfiber ⟨new ++ H, hpos'⟩ (layout.key (tree (k + 1))) _ _
                    (fun h => by
                      have := SeedPrimitives.cipherInput_injective hl hL (by omega : k + 1 < 2 * L) (by omega : k + 1 < 2 * L)
                        variant salt false true (hin h)
                      simp at this)
                    hfreshp q hlen1
      _ ≤ _ := by
          refine (add_le_add_left hstep B).trans (le_of_eq ?_)
          push_cast
          ring

end
end SDitH.Proofs.TreeDistinctBound
