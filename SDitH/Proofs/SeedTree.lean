import SDitH.Spec.SeedTree
import Mathlib.Tactic

namespace SDitH.Proofs.SeedTree

open Spec.SeedTree

variable {Seed : Type*}

theorem node_root (expand : Nat → Seed → Seed × Seed) (root : Seed) :
    node expand root 1 = root := by rw [node]; simp

theorem node_left (expand : Nat → Seed → Seed × Seed) (root : Seed)
    (i : Nat) (hi : 0 < i) :
    node expand root (2 * i) = (expand i (node expand root i)).1 := by
  rw [node]
  simp [show ¬ 2 * i ≤ 1 by omega]

theorem node_right (expand : Nat → Seed → Seed × Seed) (root : Seed)
    (i : Nat) (hi : 0 < i) :
    node expand root (2 * i + 1) = (expand i (node expand root i)).2 := by
  rw [node]
  have hd : (2 * i + 1) / 2 = i := by omega
  have hm : (2 * i + 1) % 2 = 1 := by omega
  simp [show ¬ 2 * i + 1 ≤ 1 by omega, hd, hm]

/-- Loop invariant: after `steps` parent expansions, all addresses 1 through
`2*steps+1` are initialized with exactly their mathematical tree value. -/
theorem run_matches_node (expand : Nat → Seed → Seed × Seed) (root : Seed)
    (initial : Nat → Seed) (steps address : Nat)
    (hpos : 0 < address) (hbound : address ≤ 2 * steps + 1) :
    run expand root initial steps address = node expand root address := by
  induction steps generalizing address with
  | zero =>
    have ha : address = 1 := by omega
    subst address
    simp [run, node_root]
  | succ steps ih =>
    have hparent := ih (steps + 1) (by omega) (by omega)
    by_cases hr : address = 2 * (steps + 1) + 1
    · subst address
      rw [node_right expand root (steps + 1) (by omega)]
      simp [run, expandStep, hparent]
    · by_cases hl : address = 2 * (steps + 1)
      · subst address
        rw [node_left expand root (steps + 1) (by omega)]
        simp [run, expandStep, hparent]
      · have ha : address ≤ 2 * steps + 1 := by omega
        simp only [run, expandStep, Function.update_of_ne hr, Function.update_of_ne hl]
        exact ih address hpos ha

/-- No uninitialized-cell choice affects any allocated tree node. -/
theorem run_independent_of_initial (expand : Nat → Seed → Seed × Seed) (root : Seed)
    (first second : Nat → Seed) (steps address : Nat)
    (hpos : 0 < address) (hbound : address ≤ 2 * steps + 1) :
    run expand root first steps address = run expand root second steps address := by
  rw [run_matches_node expand root first steps address hpos hbound,
    run_matches_node expand root second steps address hpos hbound]

theorem leafOffset_lt {tau N : Nat} (execution : Fin tau) (index : Fin N) :
    leafOffset execution index < tau * N := by
  have hi := index.isLt
  have he := execution.isLt
  have hm := Nat.mul_le_mul_left tau hi
  unfold leafOffset
  nlinarith

theorem leafAddress_bounds {tau N : Nat} (execution : Fin tau) (index : Fin N) :
    0 < leafAddress execution index ∧ leafAddress execution index < 2 * (tau * N) := by
  have h := leafOffset_lt execution index
  unfold leafAddress
  omega

/-- Interleaving does not identify two committed slots. -/
theorem leafOffset_injective {tau N : Nat} (e₁ e₂ : Fin tau) (i₁ i₂ : Fin N)
    (h : leafOffset e₁ i₁ = leafOffset e₂ i₂) : e₁ = e₂ ∧ i₁ = i₂ := by
  have he₁ := e₁.isLt
  have he₂ := e₂.isLt
  have ht : 0 < tau := by omega
  have hmod := congrArg (fun n => n % tau) h
  simp [leafOffset, Nat.add_mod, Nat.mod_eq_of_lt he₁, Nat.mod_eq_of_lt he₂] at hmod
  have he : e₁ = e₂ := Fin.ext hmod
  have hm : i₁.val * tau = i₂.val * tau := by
    simp only [leafOffset] at h
    omega
  exact ⟨he, Fin.ext (Nat.eq_of_mul_eq_mul_right ht hm)⟩

end SDitH.Proofs.SeedTree
