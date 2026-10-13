import SDitH.Proofs.PosteriorNodeBound

/-! The sum over blocks of the hit weights. For a distribution over results
carrying a list of recorded entries, the sum over all blocks of the
probability that the block's key is among the recorded keys is at most the
fiber bound times the expected number of recorded entries: a block's key is
recorded only if it is one of the recorded keys, and each key is the key of
at most the fiber bound many blocks. -/

namespace SDitH.Proofs.KeyWeightSum

open Spec.BAVCCipherProgram Spec.DomainSeparation
open Spec.IdealCipher (Entry)
open Spec.RandomOracleTrap (indicator)
open ChargeExpect ChargeCutExpect PosteriorNodeBound TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat} {α : Type*} (layout : Layout lambda (Bits lambda) (Bits lambda)) (c : Nat)
  (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c)

include hfiber in
/-- The blocks whose key is among a list's keys number at most the fiber
bound times the list's length. -/
theorem card_hits_le (N : List (Entry (Bits lambda) (Bits lambda))) :
    (Finset.univ.filter fun v : Bits lambda => layout.key (layout.output v) ∈ keysOf N).card ≤ c * N.length := by
  have h := count_key_hits layout c hfiber (keysOf N) (Subtype.fintype fun r => layout.key (layout.output r) ∈ keysOf N)
  rw [Fintype.card_subtype] at h
  calc (Finset.univ.filter fun v : Bits lambda => layout.key (layout.output v) ∈ keysOf N).card
      ≤ c * (keysOf N).card := by convert h using 2
    _ ≤ c * N.length := Nat.mul_le_mul_left c (keysOf_card_le N)

include hfiber in
/-- The sum over blocks of the hit weights is at most the fiber bound times
the expected number of recorded entries. -/
theorem sum_hit_weight_le (p : PMF α) (N : α → List (Entry (Bits lambda) (Bits lambda))) :
    ∑ v : Bits lambda, mean p (fun x => indicator (decide (layout.key (layout.output v) ∈ keysOf (N x)))) ≤
      (c : ℝ≥0∞) * mean p (fun x => ((N x).length : ℝ≥0∞)) := by
  have hsum := sum_mean_mul p (fun _ => (1 : ℝ≥0∞))
    (fun v x => indicator (decide (layout.key (layout.output v) ∈ keysOf (N x)))) Finset.univ
  simp only [one_mul] at hsum
  rw [hsum, ← mean_mul_left]
  refine mean_le_mean _ _ _ fun x _ => ?_
  have hcount : ∑ v : Bits lambda, indicator (decide (layout.key (layout.output v) ∈ keysOf (N x))) =
      ((Finset.univ.filter fun v : Bits lambda => layout.key (layout.output v) ∈ keysOf (N x)).card : ℝ≥0∞) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : layout.key (layout.output v) ∈ keysOf (N x) <;> simp [h, indicator]
  rw [hcount]
  calc ((Finset.univ.filter fun v : Bits lambda => layout.key (layout.output v) ∈ keysOf (N x)).card : ℝ≥0∞)
      ≤ ((c * (N x).length : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr (card_hits_le layout c hfiber (N x))
    _ = (c : ℝ≥0∞) * ((N x).length : ℝ≥0∞) := by push_cast; rfl

end
end SDitH.Proofs.KeyWeightSum
