import SDitH.Spec.SeedPairing
import SDitH.Proofs.SeedPrimitives
import Mathlib.Data.Nat.Bits

namespace SDitH.Proofs.SeedPairing

open Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedPairing

theorem companion_involutive {n : Nat} : Function.Involutive (@companion n) := by
  intro input
  funext i
  by_cases hi : i.val = 0 <;> simp [companion, hi]

theorem companion_ne {n : Nat} (hn : 0 < n) (input : Bits n) : companion input ≠ input := by
  intro he
  have h := congrFun he ⟨0, hn⟩
  simp only [companion, ↓reduceIte] at h
  cases hv : input ⟨0, hn⟩ <;> simp [hv] at h

theorem callTweak_bits {L address : Nat} (hL : 4 * L ≤ 2 ^ 24)
    (ha : address < 2 * L) (side : Bool) (j : Nat) :
    (callTweak address side).val.testBit j =
      if j = 0 then side else address.testBit (j - 1) := by
  rw [SeedPrimitives.callTweak_exact hL ha side]
  have he : 2 * address + (if side then 1 else 0) = Nat.bit side address := by
    cases side <;> simp [Nat.bit]
  rw [he]
  cases j with
  | zero => simp
  | succ j => simp [Nat.testBit_bit_succ]

/-- The two plaintexts at any submitted seed address differ by this one fixed
involution. Neither a key, salt nor adaptively chosen address changes it. -/
theorem cipherInput_companion {lambda L address : Nat} (hl : 26 ≤ lambda)
    (hL : 4 * L ≤ 2 ^ 24) (ha : address < 2 * L)
    (variant : Grinding) (salt : Bits lambda) :
    cipherInput variant salt address true = companion (cipherInput variant salt address false) := by
  funext i
  by_cases hi : i.val = 0
  · have hj : i.val < 24 := by omega
    simp only [companion, hi, ↓reduceIte]
    simp only [cipherInput, DomainSeparation.tweak_low_bits hl variant salt _ true i hj,
      callTweak_bits hL ha, hi, ↓reduceIte, Bool.not_false]
  · have hb : (callTweak address true).val.testBit i.val =
        (callTweak address false).val.testBit i.val := by
      simp only [callTweak_bits hL ha, hi, ↓reduceIte]
    cases variant <;> simp only [cipherInput, tweakSalt, companion, hi, ↓reduceIte, hb]

theorem pad192_companion (input : Bits 192) :
    pad192 (companion input) = companion (pad192 input) := by
  funext i
  by_cases hi : i.val < 192
  · simp [pad192, companion, hi]
  · have hz : i.val ≠ 0 := by omega
    simp [pad192, companion, hi, hz]

theorem padded_cipherInput_companion {L address : Nat} (hL : 4 * L ≤ 2 ^ 24)
    (ha : address < 2 * L) (variant : Grinding) (salt : Bits 192) :
    pad192 (cipherInput variant salt address true) =
      companion (pad192 (cipherInput variant salt address false)) := by
  rw [cipherInput_companion (by decide) hL ha, pad192_companion]

end SDitH.Proofs.SeedPairing
