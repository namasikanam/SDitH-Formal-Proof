import SDitH.Spec.CipherGrinding
import Mathlib.Tactic

namespace SDitH.Proofs.CipherGrinding

open Spec.DomainSeparation Spec.CipherGrinding

theorem prepareKey_first {lambda : Nat} (hl : 0 < lambda) (bit : Bool) (key : Bits lambda) :
    prepareKey bit key ⟨0, hl⟩ = bit := by simp [prepareKey]

theorem prepareKey_tail {lambda : Nat} (bit : Bool) (key : Bits lambda)
    (j : Fin lambda) (hj : j.val ≠ 0) : prepareKey bit key j = key j := by
  simp [prepareKey, hj]

/-- The two keys are distinct regardless of the XOF-derived material. This
does not imply unequal ciphertexts or any cipher-security property. -/
theorem prepared_keys_distinct {lambda : Nat} (hl : 0 < lambda) (first second : Bits lambda) :
    prepareKey false first ≠ prepareKey true second := by
  intro h
  have he := congrFun h ⟨0, hl⟩
  simp [prepareKey] at he

theorem preparePlaintext_counter {lambda : Nat} (hl : 33 ≤ lambda)
    (counter : Bits 32) (plaintext : Bits lambda) (j : Fin 32) :
    preparePlaintext counter plaintext ⟨j.val, by have hj := j.isLt; omega⟩ = counter j := by
  have hj := j.isLt
  have htop : j.val + 1 ≠ lambda := by omega
  simp [preparePlaintext, htop, hj]

theorem preparePlaintext_top {lambda : Nat} (hl : 0 < lambda)
    (counter : Bits 32) (plaintext : Bits lambda) :
    preparePlaintext counter plaintext ⟨lambda - 1, by omega⟩ = true := by
  simp [preparePlaintext, Nat.sub_add_cancel hl]

theorem preparePlaintext_middle {lambda : Nat} (counter : Bits 32) (plaintext : Bits lambda)
    (j : Fin lambda) (hlo : 32 ≤ j.val) (hhi : j.val + 1 < lambda) :
    preparePlaintext counter plaintext j = plaintext j := by
  simp [preparePlaintext, show ¬ j.val < 32 by omega, show j.val + 1 ≠ lambda by omega]

/-- The encoded counter is recoverable even if the initial material differs. -/
theorem preparePlaintext_counter_injective {lambda : Nat} (hl : 33 ≤ lambda)
    (first second : Bits 32) (p q : Bits lambda)
    (h : preparePlaintext first p = preparePlaintext second q) : first = second := by
  funext j
  have he := congrFun h ⟨j.val, by have hj := j.isLt; omega⟩
  simpa only [preparePlaintext_counter hl] using he

theorem counterBitsLE_injective : Function.Injective counterBitsLE := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 32
  · exact congrFun h ⟨j, hj⟩
  · have hp : 2 ^ 32 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hp), Nat.testBit_lt_two_pow (b.isLt.trans_le hp)]

theorem distinct_counters_distinct_plaintexts {lambda : Nat} (hl : 33 ≤ lambda)
    (a b : Spec.BLCRetry.Counter) (hab : a ≠ b) (p q : Bits lambda) :
    preparePlaintext (counterBitsLE a) p ≠ preparePlaintext (counterBitsLE b) q := by
  intro h
  exact hab (counterBitsLE_injective (preparePlaintext_counter_injective hl _ _ _ _ h))

end SDitH.Proofs.CipherGrinding
