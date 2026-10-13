import SDitH.Spec.GrayCode
import Mathlib.Tactic

namespace SDitH.Proofs.GrayCode

open Spec.GrayCode
open scoped BigOperators

theorem grayWord_injective : Function.Injective grayWord := by
  intro a b h
  have he := congrArg (fun x => a ^^^ x ^^^ (b / 2)) h
  have hx : a ^^^ b = (a / 2) ^^^ (b / 2) := by
    simpa [grayWord, Nat.xor_assoc] using he.symm
  have hd : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
    simpa [Nat.shiftRight_eq_div_pow] using
      (Nat.shiftRight_xor_distrib (a := a) (b := b) (i := 1))
  have hz : a ^^^ b = 0 := by omega
  exact Nat.xor_eq_zero_iff.mp hz

theorem grayWord_bound {kappa : Nat} (i : Fin (2 ^ kappa)) :
    grayWord i.val < 2 ^ kappa :=
  Nat.xor_lt_two_pow i.isLt (lt_of_le_of_lt (Nat.div_le_self _ _) i.isLt)

/-- Each output bit is exactly the XOR of adjacent binary bits. This includes
the leading zero introduced by the right shift because i < 2^kappa. -/
theorem grayRow_formula {kappa : Nat} (i : Fin (2 ^ kappa)) (j : Fin kappa) :
    grayRow i j = Bool.xor (i.val.testBit (kappa - 1 - j.val))
      (i.val.testBit (kappa - j.val)) := by
  have hj := j.isLt
  have he : kappa - 1 - j.val + 1 = kappa - j.val := by omega
  simp [grayRow, grayWord, Nat.testBit_div_two, he]

theorem grayRow_injective {kappa : Nat} :
    Function.Injective (grayRow (kappa := kappa)) := by
  intro a b h
  apply Fin.ext
  apply grayWord_injective
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < kappa
  · let j : Fin kappa := ⟨kappa - 1 - k, by omega⟩
    have he := congrFun h j
    have hr : kappa - 1 - j.val = k := by dsimp [j]; omega
    simpa only [grayRow, hr] using he
  · have hp : 2 ^ kappa ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow ((grayWord_bound a).trans_le hp),
      Nat.testBit_lt_two_pow ((grayWord_bound b).trans_le hp)]

theorem grayFieldRow_injective {kappa : Nat} :
    Function.Injective (grayFieldRow (kappa := kappa)) := by
  intro a b h
  apply grayRow_injective
  funext j
  have he := congrFun h j
  simp only [grayFieldRow] at he
  cases ha : grayRow a j <;> cases hb : grayRow b j <;> simp_all

theorem grayWord_div_two (n : Nat) : grayWord n / 2 = grayWord (n / 2) := by
  simp [grayWord, Nat.xor_div_two]

/-- Consecutive Gray words differ by exactly one power-of-two bit. -/
theorem grayWord_consecutive (n : Nat) :
    ∃ k : Nat, grayWord n ^^^ grayWord (n + 1) = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n % 2 = 0
    · have hd : (grayWord n ^^^ grayWord (n + 1)) / 2 = 0 := by
        rw [Nat.xor_div_two, grayWord_div_two, grayWord_div_two,
          show (n + 1) / 2 = n / 2 by omega, Nat.xor_self]
      have hn : grayWord n ^^^ grayWord (n + 1) ≠ 0 := by
        intro hz
        have heq := grayWord_injective (Nat.xor_eq_zero_iff.mp hz)
        omega
      exact ⟨0, by simp only [pow_zero]; omega⟩
    · have ho : n % 2 = 1 := by omega
      obtain ⟨k, hk⟩ := ih (n / 2) (by omega)
      have hd : (grayWord n ^^^ grayWord (n + 1)) / 2 = 2 ^ k := by
        rw [Nat.xor_div_two, grayWord_div_two, grayWord_div_two,
          show (n + 1) / 2 = n / 2 + 1 by omega, hk]
      have hm : (grayWord n ^^^ grayWord (n + 1)) % 2 = 0 := by
        have ha : grayWord n % 2 = (n + n / 2) % 2 := Nat.xor_mod_two_eq
        have hb : grayWord (n + 1) % 2 = (n + 1 + (n + 1) / 2) % 2 := Nat.xor_mod_two_eq
        rw [Nat.xor_mod_two_eq, Nat.add_mod, ha, hb]
        omega
      refine ⟨k + 1, ?_⟩
      rw [Nat.pow_succ]
      omega

/-- The changed bit is within the submitted kappa-bit range. -/
theorem grayWord_consecutive_bounded {kappa n : Nat} (hn : n + 1 < 2 ^ kappa) :
    ∃ k < kappa, grayWord n ^^^ grayWord (n + 1) = 2 ^ k := by
  obtain ⟨k, hk⟩ := grayWord_consecutive n
  refine ⟨k, ?_, hk⟩
  have ha := grayWord_bound (⟨n, by omega⟩ : Fin (2 ^ kappa))
  have hb := grayWord_bound (⟨n + 1, hn⟩ : Fin (2 ^ kappa))
  have hp : 2 ^ k < 2 ^ kappa := hk ▸ Nat.xor_lt_two_pow ha hb
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp hp

/-- The final Gray word also differs in one bit from the forced zero boundary
row. This is the wrap-around case needed in equation (5). -/
theorem grayWord_last {kappa : Nat} (hk : 0 < kappa) :
    grayWord (2 ^ kappa - 1) = 2 ^ (kappa - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [grayWord, Nat.testBit_xor, Nat.testBit_div_two,
    Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  by_cases h₁ : j < kappa
  · by_cases h₂ : j + 1 < kappa
    · have h₃ : kappa - 1 ≠ j := by omega
      simp [h₁, h₂, h₃]
    · have h₃ : kappa - 1 = j := by omega
      simp [h₁, h₂, h₃]
  · have h₂ : ¬ j + 1 < kappa := by omega
    have h₃ : kappa - 1 ≠ j := by omega
    simp [h₁, h₂, h₃]

theorem prefixAcc_formula {K : Type*} [AddCommMonoid K] (random : Nat → K) (n : Nat) :
    prefixAcc random n = ∑ i ∈ Finset.range n, random i := by
  induction n with
  | zero => simp [prefixAcc]
  | succ n ih => simp [prefixAcc, ih, Finset.sum_range_succ]

/-- The exact finite telescoping identity, including its boundary term. -/
theorem differenceFold_formula {K : Type*} [CommRing K] (random phi : Nat → K) (N : Nat) :
    differenceFold random phi N =
      (∑ i ∈ Finset.range N, random i * phi i) - prefixAcc random N * phi N := by
  induction N with
  | zero => simp [differenceFold, prefixAcc]
  | succ N ih =>
    unfold differenceFold at ih ⊢
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, prefixAcc]
    ring

/-- Equations (4)–(5) equal the direct weighted fold when the expressly stated
last Gray row is zero. No bit-operation count or timing claim is assumed. -/
theorem differenceFold_eq_direct {K : Type*} [CommRing K]
    (random phi : Nat → K) (N : Nat) (hboundary : phi N = 0) :
    differenceFold random phi N = ∑ i ∈ Finset.range N, random i * phi i := by
  rw [differenceFold_formula, hboundary, mul_zero, sub_zero]

end SDitH.Proofs.GrayCode
