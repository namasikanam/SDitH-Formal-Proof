import SDitH.Proofs.SHAKE
import Mathlib.Data.List.GetD

/-! Direct bit formulas for padded input reads. Besides exposing the exact
delimiter positions, these avoid repeatedly traversing long zero lists when
the kernel checks concrete absorption certificates. -/

namespace SDitH.Proofs.SHAKE

open Spec.SHAKE

theorem getD_append_if {α : Type*} (left right : List α) (i : Nat) (fallback : α) :
    (left ++ right).getD i fallback =
      if i < left.length then left.getD i fallback else right.getD (i - left.length) fallback := by
  split_ifs with h
  · exact List.getD_append left right fallback i h
  · exact List.getD_append_right left right fallback i (Nat.le_of_not_lt h)

theorem padding_bit (r : Rate) (m i : Nat) :
    (padding r m).getD i false = decide (i = 0 ∨ i = padZeros r m + 1) := by
  cases i with
  | zero => simp [padding]
  | succ i =>
    simp only [padding, List.getD_cons_succ, getD_append_if, List.length_replicate]
    by_cases h : i < padZeros r m
    · simp only [h, if_true, List.getD_replicate false h]
      have hn : ¬(i + 1 = 0 ∨ i + 1 = padZeros r m + 1) := by omega
      simp only [hn, decide_false]
    · have he : i - padZeros r m = 0 ↔ i = padZeros r m := by omega
      by_cases hz : i = padZeros r m <;>
        simp [h, List.getD_eq_getElem?_getD, he, hz]

theorem padded_bit (r : Rate) (input : List Bool) (i : Nat) :
    (padded r input).getD i false =
      if i < input.length then input.getD i false
      else decide (i = input.length ∨ i = input.length + padZeros r input.length + 1) := by
  rw [padded, getD_append_if]
  split_ifs with h
  · rfl
  · rw [padding_bit]
    have he : (i - input.length = 0 ∨ i - input.length = padZeros r input.length + 1) ↔
        (i = input.length ∨ i = input.length + padZeros r input.length + 1) := by omega
    simp only [he]

end SDitH.Proofs.SHAKE
