import SDitH.Proofs.WitnessExpansion
import SDitH.Spec.PIOPArithmetic

namespace SDitH.Proofs.WitnessConstraints

open Spec Spec.WitnessExpansion Spec.PIOPArithmetic
open scoped BigOperators

variable {F : Type*} [Field F]

theorem prefix_elementary_sum {n N : Nat} (bound : n ≤ N) (position : Fin N)
    (weight : Nat → F) :
    (∑ k : Fin n, weight k.val * elementary position (k.castLE bound)) =
      if position.val < n then weight position.val else 0 := by
  classical
  by_cases hp : position.val < n
  · rw [if_pos hp]
    let p : Fin n := ⟨position.val, hp⟩
    calc
      _ = ∑ k : Fin n, if k = p then weight k.val else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k.val = position.val <;>
          simp [elementary, Fin.ext_iff, p, hk]
      _ = weight position.val :=
        Finset.sum_ite_eq_of_mem' Finset.univ p (fun k => weight k.val) (Finset.mem_univ p)
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro k _
    have hk : k.val ≠ position.val := by have hb := k.isLt; omega
    simp [elementary, Fin.ext_iff, hk]

/-- Every selector actually produced by Algorithm 1 passes the printed unitary
arithmetic for every challenge. No independence or field-basis property is
needed for this honest-input direction. -/
theorem unitary_omitted_elementary (xi : F) {r : Nat} (position : Fin (r + 1)) :
    unitaryCheck xi (fun k : Fin r => elementary position k.castSucc) = 0 := by
  change
    (∑ k : Fin r, xi ^ k.val * elementary position (k.castLE (Nat.le_succ r))) *
      (∑ k : Fin (r - 1), xi ^ (r * k.val) * elementary position
        (k.castLE (Nat.le_trans (Nat.sub_le r 1) (Nat.le_succ r)))) -
      (∑ k : Fin (r - 1), xi ^ ((r + 1) * k.val) * elementary position
        (k.castLE (Nat.le_trans (Nat.sub_le r 1) (Nat.le_succ r)))) = 0
  rw [prefix_elementary_sum (Nat.le_succ r) position (fun k => xi ^ k),
    prefix_elementary_sum (Nat.le_trans (Nat.sub_le r 1) (Nat.le_succ r)) position
      (fun k => xi ^ (r * k)),
    prefix_elementary_sum (Nat.le_trans (Nat.sub_le r 1) (Nat.le_succ r)) position
      (fun k => xi ^ ((r + 1) * k))]
  by_cases hp : position.val < r - 1
  · have hp' : position.val < r := by omega
    simp only [if_pos hp, if_pos hp']
    rw [← pow_add]
    have he : position.val + r * position.val = (r + 1) * position.val := by ring
    rw [he, sub_self]
  · simp [hp]

theorem expanded_selector_unitary {d : Nat} (width : Fin d → Nat) (position : Nat)
    (j : Fin d) (xi : F) : unitaryCheck xi (selector width position j) = 0 :=
  unitary_omitted_elementary xi ((splitPosition width position).digits j)

end SDitH.Proofs.WitnessConstraints
