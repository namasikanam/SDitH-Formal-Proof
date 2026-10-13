import SDitH.Spec.DomainSeparation
import Mathlib.Tactic

namespace SDitH.Proofs.DomainSeparation

open Spec.DomainSeparation

theorem tweak_low_bits {lambda : Nat} (hl : 26 ≤ lambda) (variant : Grinding)
    (salt : Bits lambda) (tweak : Tweak) (bit : Bool) (j : Fin lambda) (hj : j.val < 24) :
    tweakSalt variant salt tweak bit j = tweak.val.testBit j.val := by
  have ht : j.val + 1 ≠ lambda := by omega
  cases variant with
  | hash => simp [tweakSalt, ht, hj]
  | cipher =>
    have ht' : j.val + 2 ≠ lambda := by omega
    simp [tweakSalt, ht, ht', hj]

theorem hash_top_bit {lambda : Nat} (hl : 0 < lambda) (salt : Bits lambda)
    (tweak : Tweak) (bit : Bool) :
    tweakSalt .hash salt tweak bit ⟨lambda - 1, by omega⟩ = bit := by
  simp [tweakSalt, Nat.sub_add_cancel hl]

theorem cipher_second_bit {lambda : Nat} (hl : 2 ≤ lambda) (salt : Bits lambda)
    (tweak : Tweak) (bit : Bool) :
    tweakSalt .cipher salt tweak bit ⟨lambda - 2, by omega⟩ = bit := by
  have ht : lambda - 2 + 1 ≠ lambda := by omega
  simp [tweakSalt, ht, Nat.sub_add_cancel hl]

/-- For fixed salt and variant, the 24-bit tweak is recoverable from the output.
This is a statement about plaintext domain encoding, not cipher security. -/
theorem tweak_recoverable {lambda : Nat} (hl : 26 ≤ lambda) (variant : Grinding)
    (salt : Bits lambda) (t₁ t₂ : Tweak) (b₁ b₂ : Bool)
    (h : tweakSalt variant salt t₁ b₁ = tweakSalt variant salt t₂ b₂) : t₁ = t₂ := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 24
  · let bitIndex : Fin lambda := ⟨j, by omega⟩
    have he := congrFun h bitIndex
    rw [tweak_low_bits hl variant salt t₁ b₁ bitIndex hj,
      tweak_low_bits hl variant salt t₂ b₂ bitIndex hj] at he
    exact he
  · have hp : 2 ^ 24 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (t₁.isLt.trans_le hp),
      Nat.testBit_lt_two_pow (t₂.isLt.trans_le hp)]

/-- The encoded domain bit is recoverable within each grinding variant. -/
theorem domain_bit_recoverable {lambda : Nat} (hl : 26 ≤ lambda) (variant : Grinding)
    (salt : Bits lambda) (t₁ t₂ : Tweak) (b₁ b₂ : Bool)
    (h : tweakSalt variant salt t₁ b₁ = tweakSalt variant salt t₂ b₂) : b₁ = b₂ := by
  cases variant with
  | hash =>
    have he := congrFun h ⟨lambda - 1, by omega⟩
    simpa only [hash_top_bit (lambda := lambda) (by omega) salt t₁ b₁,
      hash_top_bit (lambda := lambda) (by omega) salt t₂ b₂] using he
  | cipher =>
    have he := congrFun h ⟨lambda - 2, by omega⟩
    simpa only [cipher_second_bit (lambda := lambda) (by omega) salt t₁ b₁,
      cipher_second_bit (lambda := lambda) (by omega) salt t₂ b₂] using he

/-- Distinct domain bytes give distinct inputs, even for different payloads.
This deliberately does not assert that the corresponding hash outputs differ. -/
theorem hash_domains_disjoint (a b : Byte) (ha : a ≠ b) (x y : List Byte) :
    hashInput a x ≠ hashInput b y := by
  intro h
  exact ha (List.cons.inj h).1

end SDitH.Proofs.DomainSeparation
