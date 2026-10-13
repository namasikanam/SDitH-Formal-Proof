import SDitH.Spec.SeedPrimitives
import SDitH.Spec.Parameters
import SDitH.Proofs.DomainSeparation
import Mathlib.Tactic

namespace SDitH.Proofs.SeedPrimitives

open Spec.DomainSeparation Spec.SeedPrimitives

theorem callTweak_exact {L address : Nat} (hL : 4 * L ≤ 2 ^ 24)
    (ha : address < 2 * L) (right : Bool) :
    (callTweak address right).val = 2 * address + if right then 1 else 0 := by
  apply Nat.mod_eq_of_lt
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Recovering the tweak recovers both the tree address and the left/right bit. -/
theorem callTweak_injective {L a b : Nat} (hL : 4 * L ≤ 2 ^ 24)
    (ha : a < 2 * L) (hb : b < 2 * L) (r s : Bool)
    (h : callTweak a r = callTweak b s) : a = b ∧ r = s := by
  have he := congrArg Fin.val h
  rw [callTweak_exact hL ha r, callTweak_exact hL hb s] at he
  cases r <;> cases s <;> simp_all
  all_goals omega

theorem cipherInput_injective {lambda L a b : Nat} (hl : 26 ≤ lambda)
    (hL : 4 * L ≤ 2 ^ 24) (ha : a < 2 * L) (hb : b < 2 * L)
    (variant : Grinding) (salt : Bits lambda) (r s : Bool)
    (h : cipherInput variant salt a r = cipherInput variant salt b s) : a = b ∧ r = s := by
  apply callTweak_injective hL ha hb r s
  exact DomainSeparation.tweak_recoverable hl variant salt _ _ true true h

/-- Internal-node expansion and leaf commitment use disjoint plaintext tweaks.
This proves separation of inputs, not independence or inequality of outputs. -/
theorem expansion_commitment_inputs_disjoint {lambda L parent index : Nat}
    (hl : 26 ≤ lambda) (hL : 4 * L ≤ 2 ^ 24) (hp : parent < L) (hi : index < L)
    (variant : Grinding) (salt : Bits lambda) (r s : Bool) :
    cipherInput variant salt parent r ≠ cipherInput variant salt (L + index) s := by
  intro h
  have he := (cipherInput_injective hl hL (by omega) (by omega) variant salt r s h).1
  omega

/-- Both submitted binary proof-parameter tables fit the 24-bit tweak domain,
including leaf commitment calls. This says nothing about their other bounds. -/
theorem submitted_tweak_bounds :
    (Spec.hashProofParameters ++ Spec.cipherProofParameters).all
      (fun p => decide (4 * (p.tau * 2 ^ p.kappa) ≤ 2 ^ 24)) = true := by
  decide

theorem concatenate_left {lambda : Nat} (left right : Bits lambda) (j : Fin lambda) :
    concatenate left right ⟨j.val, by have hj := j.isLt; omega⟩ = left j := by
  simp [concatenate, j.isLt]

theorem concatenate_right {lambda : Nat} (left right : Bits lambda) (j : Fin lambda) :
    concatenate left right ⟨lambda + j.val, by have hj := j.isLt; omega⟩ = right j := by
  simp [concatenate, show ¬lambda + j.val < lambda by omega]

theorem pad192_preserves (input : Bits 192) (j : Fin 192) :
    pad192 input ⟨j.val, by have hj := j.isLt; omega⟩ = input j := by
  simp [pad192, j.isLt]

theorem pad192_zeroes (input : Bits 192) (j : Fin 64) :
    pad192 input ⟨192 + j.val, by have hj := j.isLt; omega⟩ = false := by
  simp [pad192]

end SDitH.Proofs.SeedPrimitives
