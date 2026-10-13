import SDitH.Proofs.TouchAssembly
import SDitH.Proofs.DistinctBridge
import SDitH.Proofs.StaleTermBound

/-! The total touching bound. The internal path of a leaf has at most the
binary logarithm of the leaf count many nodes; the pairs whose tree keys
are not fresh and distinct have the distinctness failure probability; so
the touching probability under the joint draw is at most that failure
probability plus the assembled bound on the good pairs. -/

namespace SDitH.Proofs.TouchTotal

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys HiddenKeysExchange TreeExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange NodeTouchBound RootPosteriorBound TouchSplit TouchAssembly TreeDistinct DistinctBridge StaleTermBound HiddenTuple
open CipherResample ChargeExpect ChargeCutExpect TreeStepFresh
open scoped Classical ENNReal

noncomputable section

section Depth

/-- The path of an address has at most its binary logarithm many nodes. -/
theorem pathAddresses_length_le (a : Nat) : (pathAddresses a).length ≤ Nat.log 2 a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    by_cases ha : a ≤ 1
    · rw [pathAddresses_of_le ha]
      simp
    · rw [pathAddresses_of_lt (by omega), List.length_cons]
      have h1 := ih (a / 2) (by omega)
      have h2 : Nat.log 2 (a / 2) = Nat.log 2 a - 1 := Nat.log_div_base 2 a
      have h3 : 0 < Nat.log 2 a := Nat.log_pos (by norm_num) (by omega)
      omega

/-- The internal path of a leaf has at most the binary logarithm of the
leaf count many nodes. -/
theorem innerPath_card_le {tau kappa : Nat} (e : Fin tau) (i : Fin (2 ^ kappa)) :
    (innerPath (leafAddress e i)).card ≤ Nat.log 2 (tau * 2 ^ kappa) := by
  have hb := SDitH.Proofs.SeedTree.leafAddress_bounds e i
  unfold innerPath
  refine (List.toFinset_card_le _).trans ((pathAddresses_length_le _).trans (Nat.log_mono_right ?_))
  omega

end Depth

section Decide

variable {α : Type*}

/-- The probability of a decided event is the mean of its indicator. -/
theorem map_decide_eq_mean (p : PMF α) (P : α → Prop) [DecidablePred P] :
    (p.map fun a => decide (P a)) true = mean p fun a => indicator (decide (P a)) :=
  RandomOracleTrap.map_true_eq p fun a => decide (P a)

end Decide

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w₀ : World lambda s wit rnd) {Sig β : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
  (hidden : Sig → Fin tau → Fin (2 ^ kappa))
  (cont : Sig × World lambda s wit rnd → PMF β) (new : β → List (Entry (Bits lambda) (Bits lambda)))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The probability, under the joint draw, that the tree's keys are not
fresh and distinct. -/
theorem bad_tree_le (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hL1 : 1 ≤ tau * 2 ^ kappa) (c : Nat)
    (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ cKey)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory) (q : Nat)
    (hq : w₀.cipherHistory.length + 2 * (tau * 2 ^ kappa - 1) + 1 ≤ q) :
    mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (¬ GoodTree S salt w₀ x))) ≤
      ((cKey * (keysOf w₀.cipherHistory).card : Nat) : ℝ≥0∞) * (Fintype.card (Bits lambda) : ℝ≥0∞)⁻¹ +
        (tau * 2 ^ kappa - 1 : ℕ) *
          (2 * (((c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) /
              ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) +
            (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) := by
  rw [mean_rootDraw]
  calc mean (PMF.uniformOfFintype (Bits lambda)) (fun r => mean (posterior w₀.cipherHistory) fun g =>
          indicator (decide (¬ GoodTree S salt w₀ (r, g))))
      ≤ mean (PMF.uniformOfFintype (Bits lambda)) (fun r => indicator (decide (S.layout.key r ∈ keysOf w₀.cipherHistory)) +
          (tau * 2 ^ kappa - 1 : ℕ) *
            (2 * (((c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) /
                ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) +
              (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞))) := by
        refine mean_le_mean _ _ _ fun r _ => ?_
        have h := distinct_family_le S.layout S.variant salt r hin hl (tau * 2 ^ kappa) hL hL1 c hfiber w₀.cipherHistory hpos q hq
        rw [map_decide_eq_mean] at h
        exact h
    _ = ((PMF.uniformOfFintype (Bits lambda)).map fun r => decide (S.layout.key r ∈ keysOf w₀.cipherHistory)) true +
          (tau * 2 ^ kappa - 1 : ℕ) *
            (2 * (((c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) /
                ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) +
              (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) := by
        rw [mean_add, mean_const, map_decide_eq_mean]
    _ ≤ _ := add_le_add (root_key_le S.layout cKey hfiberR (keysOf w₀.cipherHistory)) le_rfl

/-- The touching probability is at most one. -/
theorem touchAll_le_one (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    touchAll S salt witness w₀ post hidden cont new x ≤ 1 :=
  mean_le_const _ _ 1 fun v _ => mean_le_const _ _ 1 fun y _ => by
    by_cases h : ∃ e ∈ new y, e.key ∈ hiddenKeysAll S.layout x.2 S.variant salt x.1 (hidden v.1) <;> simp [h, indicator]

/-- The total touching bound under the joint draw: the distinctness
failure probability, plus the assembled bound with the internal path
depth the binary logarithm of the leaf count, plus the leaf term. -/
theorem touch_total (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hpost : ∀ b, b < tau * 2 ^ kappa → ∀ c x, post (.done (setTree b x c)) = post (.done c))
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ cKey)
    (hNb : c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (q : Nat) (hq : w₀.cipherHistory.length + 2 * (tau * 2 ^ kappa - 1) + 1 ≤ q) :
    mean (rootDraw w₀.cipherHistory) (touchAll S salt witness w₀ post hidden cont new) ≤
      (((cKey * (keysOf w₀.cipherHistory).card : Nat) : ℝ≥0∞) * (Fintype.card (Bits lambda) : ℝ≥0∞)⁻¹ +
        (tau * 2 ^ kappa - 1 : ℕ) *
          (2 * (((c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) /
              ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) +
            (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞))) +
      ((tau : ℝ≥0∞) *
          ((cKey : ℝ≥0∞) / ((Fintype.card (Bits lambda) - cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) +
            (Nat.log 2 (tau * 2 ^ kappa) : ℝ≥0∞) * ((c : ℝ≥0∞) /
              ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞))) *
          mean (rootDraw w₀.cipherHistory) (expLen S salt witness w₀ post hidden cont new) +
        leafTerm S salt witness w₀ post hidden cont new) := by
  calc mean (rootDraw w₀.cipherHistory) (touchAll S salt witness w₀ post hidden cont new)
      ≤ mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (¬ GoodTree S salt w₀ x)) +
          indicator (decide (GoodTree S salt w₀ x)) * touchAll S salt witness w₀ post hidden cont new x) := by
        refine mean_le_mean _ _ _ fun x _ => ?_
        by_cases hd : GoodTree S salt w₀ x
        · simp [hd, indicator]
        · simp only [hd, not_false_eq_true, decide_true, decide_false, RandomOracleTrap.indicator_true,
            RandomOracleTrap.indicator_false, zero_mul, add_zero]
          exact touchAll_le_one S salt witness w₀ post hidden cont new x
    _ = mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (¬ GoodTree S salt w₀ x))) +
          mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
            touchAll S salt witness w₀ post hidden cont new x) := mean_add _ _ _
    _ ≤ _ := add_le_add
        (bad_tree_le S salt w₀ hin hl hL (by omega) c hfiber cKey hfiberR hpos q hq)
        (touch_assembly S salt witness w₀ post hidden cont new hL2 hin hl hL hpost hpos c hfiber cKey hfiberR hNb hNR
          (Nat.log 2 (tau * 2 ^ kappa)) fun e i => innerPath_card_le e i)

end
end SDitH.Proofs.TouchTotal
