import SDitH.Proofs.Rijndael

namespace SDitH.Proofs.RijndaelSchedule

open Spec.Rijndael Spec.RijndaelByte

theorem columns_positive (p : Profile) : 0 < columns p := by cases p <;> decide

theorem expandedThrough_preserves (p : Profile) (key : State p) (n i : Nat)
    (hi : i < columns p + n) :
    (expandedThrough p key (n + 1))[i] = (expandedThrough p key n)[i] := by
  rw [expandedThrough]
  exact Vector.getElem_push_lt hi

theorem expandedThrough_prefix (p : Profile) (key : State p) (m n i : Nat)
    (hm : m ≤ n) (hi : i < columns p + m) :
    (expandedThrough p key m)[i] = (expandedThrough p key n)[i] := by
  induction n with
  | zero =>
    have h : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    by_cases he : m = n + 1
    · subst m
      rfl
    · have hm' : m ≤ n := by omega
      rw [expandedThrough_preserves p key n i (by omega)]
      exact ih hm'

theorem expandedThrough_newWord (p : Profile) (key : State p) (n : Nat) :
    (expandedThrough p key (n + 1))[columns p + n] =
      xorWord ((expandedThrough p key n)[n]'(by have := columns_positive p; omega))
        (scheduleTransform p (columns p + n)
          ((expandedThrough p key n)[columns p + n - 1]'(by have := columns_positive p; omega))) := by
  rw [expandedThrough]
  exact Vector.getElem_push_eq

/-- Every produced word satisfies the specified backward recurrence, even
when read from the completed schedule rather than its construction stage. -/
theorem expandedThrough_recurrence (p : Profile) (key : State p) (n stage : Nat)
    (hs : stage < n) :
    (expandedThrough p key n)[columns p + stage] =
      xorWord ((expandedThrough p key n)[stage]'(by omega))
        (scheduleTransform p (columns p + stage)
          ((expandedThrough p key n)[columns p + stage - 1]'(by omega))) := by
  have hc := columns_positive p
  calc
    _ = (expandedThrough p key (stage + 1))[columns p + stage] :=
      (expandedThrough_prefix p key (stage + 1) n (columns p + stage) (by omega) (by omega)).symm
    _ = xorWord ((expandedThrough p key stage)[stage]'(by omega))
        (scheduleTransform p (columns p + stage)
          ((expandedThrough p key stage)[columns p + stage - 1]'(by omega))) :=
      expandedThrough_newWord p key stage
    _ = _ := congrArg₂ xorWord
      (expandedThrough_prefix p key stage n stage (by omega) (by omega))
      (congrArg (scheduleTransform p (columns p + stage))
        (expandedThrough_prefix p key stage n (columns p + stage - 1) (by omega) (by omega)))

theorem expandedKey_initial (p : Profile) (key : State p) (i : Fin (columns p)) :
    (expandedKey p key)[i.val]'(by
      have := i.isLt
      cases p <;> simp only [columns, rounds] at * <;> omega) = (initialWords p key)[i] := by
  simp only [expandedKey, Vector.getElem_cast, Fin.getElem_fin]
  exact (expandedThrough_prefix p key 0 (columns p * rounds p) i.val (by omega) (by omega)).symm

theorem expandedKey_recurrence (p : Profile) (key : State p) (i : Nat)
    (hlo : columns p ≤ i) (hhi : i < columns p * (rounds p + 1)) :
    (expandedKey p key)[i] =
      xorWord ((expandedKey p key)[i - columns p]'(by omega))
        (scheduleTransform p i ((expandedKey p key)[i - 1]'(by omega))) := by
  simp only [expandedKey, Vector.getElem_cast]
  have hs : i - columns p < columns p * rounds p := by
    rw [Nat.mul_add, Nat.mul_one] at hhi
    omega
  have h := expandedThrough_recurrence p key (columns p * rounds p) (i - columns p) hs
  simpa only [Nat.add_sub_of_le hlo] using h

theorem rcon_positive_index (p : Profile) (i : Nat) (hi : columns p ≤ i) :
    1 ≤ i / columns p := Nat.one_le_div_iff (columns_positive p) |>.mpr hi

theorem submitted_lengths :
    columns .aes128 * (rounds .aes128 + 1) = 44 ∧
    columns .rijndael256 * (rounds .rijndael256 + 1) = 120 := by decide

end SDitH.Proofs.RijndaelSchedule
