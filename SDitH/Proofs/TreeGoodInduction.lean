import SDitH.Proofs.TreeStepFresh
import SDitH.Proofs.RowStoredPosterior

/-! The tree's goodness along the expansion under the posterior family.
Over a family drawn from the posterior of the starting history, the tree
expansion's result fails to be good for the starting history's keys with
probability at most the indicator of the root's key being among them plus
the number of steps times the step bound: at each step the family is
resampled at the history so far, and a good tree's node has fresh
expansion calls, so its children's keys fall among the starting keys with
probability at most the step bound. -/

namespace SDitH.Proofs.TreeGoodInduction

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.RandomOracleTrap
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open TreeRunEntries TreeStepFresh RowStoredPosterior RowStoredAfter CipherResample RunBind RowsSupport
open PrefixOrMention RunHybrid InputPresentTail
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The tree at a run's result, or the root everywhere when unfinished. -/
def treeOf (root : Seed lambda)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Nat → Seed lambda))) : Nat → Seed lambda :=
  match out.state with
  | .done tree => tree
  | _ => fun _ => root

/-- The event that the tree at a run's result is not good. -/
def notGood (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (K : Finset (Bits lambda))
    (steps : Nat) (root : Seed lambda)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Nat → Seed lambda))) : Bool :=
  decide (¬ Good layout K steps (treeOf root out))

/-- The expansion step's run from a finished tree is pure. -/
theorem expandStep_run_eq (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (salt : Bits lambda) (k : Nat) (tree : Nat → Seed lambda)
    (family : Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure family 2 (expandStep (s := s) (wit := wit) (rnd := rnd) layout variant salt k tree) table hashes ciphers log =
      PMF.pure ⟨.done (Function.update (Function.update tree (2 * (k + 1))
          (layout.output (family (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false)))))
          (2 * (k + 1) + 1)
          (layout.output (family (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))))),
        table, hashes,
        Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true)))
            (family (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))) ::
          Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false)))
            (family (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false))) :: ciphers,
        false, log⟩ := by
  simp only [expandStep, expandCall, Spec.HashCipherProgram.bind, runFixed, step_cipher, PMF.pure_bind]
  rfl

/-- The tree expansion's result is not good for the starting keys with
probability at most the root's indicator plus the steps times the step
bound. -/
theorem tree_good_le (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt root : Bits lambda) (hin : Function.Injective layout.input) (hl : 26 ≤ lambda) (L : Nat) (hL : 4 * L ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c)
    (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (hpos : ∃ family : Family (Bits lambda) (Bits lambda), Matches family H) (q : Nat)
    (table : List Bool → Option (Out lambda s wit rnd)) (hashes : List (List Bool × Out lambda s wit rnd))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    ∀ steps : Nat, steps < 2 * L → H.length + 2 * steps ≤ q →
      ((posterior H).bind fun family =>
        (runFixed procedure family (2 * steps) (treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root (fun _ => root) steps)
          table hashes H log).map (notGood layout (keysOf H) steps root)) true ≤
      indicator (decide (layout.key root ∈ keysOf H)) +
        steps * (2 * (((c * (keysOf H).card : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞))) := by
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
          R.state = .done (Function.update (fun _ => root) 1 root) → notGood layout (keysOf H) 0 root R = false := by
        intro R hR
        unfold notGood treeOf
        rw [hR]
        simp only [decide_eq_false_iff_not, not_not]
        intro b hb
        by_cases hb1 : b = 1
        · subst hb1
          rw [Function.update_self]
          exact hP
        · rw [Function.update_of_ne hb1]
          exact hP
      rw [if_neg (by rw [hng _ rfl]; decide)]
  | succ k ih =>
    intro hk hq
    have hstep : ((posterior H).bind fun family =>
        (runFixed procedure family (2 * k) (treeThrough layout variant salt root (fun _ => root) k)
          table hashes H log).map (notGood layout (keysOf H) k root)) true ≤
        indicator (decide (layout.key root ∈ keysOf H)) +
          k * (2 * (((c * (keysOf H).card : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞))) :=
      ih (by omega) (by omega)
    set B : ℝ≥0∞ := 2 * (((c * (keysOf H).card : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) with hB
    simp only [runFixed_tree_succ, PMF.map_bind]
    have hres := runFixed_resample procedure (2 * k) (treeThrough layout variant salt root (fun _ => root) k) table hashes
      (⟨H, hpos⟩ : Spec.IdealCipher.World (Bits lambda) (Bits lambda)) log
      (fun out family => (continueRun family 2 (expandStep layout variant salt k) out).map (notGood layout (keysOf H) (k + 1) root))
    dsimp only at hres
    rw [hres]
    calc _ ≤ ((posterior H).bind fun family =>
          (runFixed procedure family (2 * k) (treeThrough layout variant salt root (fun _ => root) k)
            table hashes H log).map (notGood layout (keysOf H) k root)) true + B := by
          refine bind_le_bind_add_const' _ _ _ _ true fun family hf => ?_
          refine bind_true_le_event_add _ _ _ B fun out hout hgood => ?_
          obtain ⟨tree, htree⟩ := runFixed_bounded_done family _ _
            (SharedSigner.treeThrough_bounded layout variant salt root (fun _ => root) k) _ _ _ _ out hout
          have hgood' : Good layout (keysOf H) k tree := by
            unfold notGood treeOf at hgood
            rw [htree] at hgood
            simpa using hgood
          obtain ⟨new, hnew, hform⟩ := tree_entries layout variant salt root (fun _ => root) family k table hashes H log out hout
          have hpos' : ∃ family : Family (Bits lambda) (Bits lambda), Matches family (new ++ H) := by
            rw [← hnew]
            exact ⟨family, runFixed_cipher_matches procedure family _ _ _ _ _ _ out hout
              (posterior_support_matches H hpos family hf)⟩
          have hlen : (new ++ H).length ≤ q := by
            rw [← hnew]
            exact (runFixed_cipher_length_le procedure family _ _ _ _ _ _ out hout).trans (by omega)
          have hkey : layout.key (tree (k + 1)) ∉ keysOf H := hgood' (k + 1) (by omega)
          have hcont : ∀ family', (continueRun family' 2 (expandStep layout variant salt k) out).map
              (notGood layout (keysOf H) (k + 1) root) =
              PMF.pure (notGood layout (keysOf H) (k + 1) root ⟨.done (Function.update (Function.update tree (2 * (k + 1))
                (layout.output (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false)))))
                (2 * (k + 1) + 1)
                (layout.output (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))))),
                out.hashTable, out.hashHistory,
                Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) true)))
                    (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))) ::
                  Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) false)))
                    (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false))) ::
                  out.cipherHistory, false, out.trace⟩) := by
            intro family'
            unfold continueRun
            rw [htree, PMF.map_comp, expandStep_run_eq, PMF.pure_map]
            rfl
          simp only [hcont]
          rw [hnew]
          calc _ ≤ ((posterior (new ++ H)).bind fun family' => PMF.pure
                (decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                  (layout.input (cipherInput variant salt (k + 1) false)))) ∈ keysOf H) ||
                decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                  (layout.input (cipherInput variant salt (k + 1) true)))) ∈ keysOf H))) true :=
                bind_true_le_bind_true _ _ _ fun family' _ => by
                  rw [PMF.pure_apply, PMF.pure_apply]
                  by_cases hng : notGood layout (keysOf H) (k + 1) root ⟨.done (Function.update (Function.update tree (2 * (k + 1))
                      (layout.output (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false)))))
                      (2 * (k + 1) + 1)
                      (layout.output (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))))),
                      out.hashTable, out.hashHistory,
                      Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
                          (layout.input (cipherInput variant salt (k + 1) true)))
                          (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))) ::
                        Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
                          (layout.input (cipherInput variant salt (k + 1) false)))
                          (family' (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false))) ::
                        (new ++ H), false, out.trace⟩ = true
                  · have hor : (decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                        (layout.input (cipherInput variant salt (k + 1) false)))) ∈ keysOf H) ||
                        decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                          (layout.input (cipherInput variant salt (k + 1) true)))) ∈ keysOf H)) = true := by
                      unfold notGood treeOf at hng
                      simp only [decide_eq_true_eq, Bool.or_eq_true] at hng ⊢
                      by_contra hor
                      push_neg at hor
                      exact hng (good_step layout (keysOf H) k tree hgood' _ _ hor.1 hor.2)
                    rw [hng, hor]
                  · rw [Bool.eq_false_iff.mpr hng]
                    simp
            _ ≤ B := by
                show ((posterior (new ++ H)).map fun family' =>
                  decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) false)))) ∈ keysOf H) ||
                  decide (layout.key (layout.output (family' (layout.key (tree (k + 1)))
                    (layout.input (cipherInput variant salt (k + 1) true)))) ∈ keysOf H)) true ≤ B
                exact step_le layout variant salt hin hl L hL k (by omega) H new hform tree hkey hpos' q hlen c hfiber
                  (keysOf H)
      _ ≤ _ := by
          refine (add_le_add_left hstep B).trans (le_of_eq ?_)
          push_cast
          ring

end
end SDitH.Proofs.TreeGoodInduction
