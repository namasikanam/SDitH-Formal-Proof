import SDitH.Spec.BAVCOpening
import SDitH.Proofs.BAVC
import Mathlib.Tactic

namespace SDitH.Proofs.BAVC

open Spec.BAVC

/-- A successful literal loop never appends more than Topen seed blocks. -/
theorem openLoop_bound {lambda tau N : Nat} (tree : Tree lambda tau N)
    (Topen : Nat) (hl : 0 < lambda) (queue : List Nat)
    (path output : List (Seed lambda)) (hbound : path.length ≤ Topen)
    (hresult : openLoop tree Topen queue path = .ok output) : output.length ≤ Topen := by
  induction queue, path using openLoop.induct tree Topen generalizing output with
  | case1 path => simp [openLoop.eq_def] at hresult
  | case2 rest path =>
    rw [openLoop.eq_def] at hresult
    have he : path = output := by simpa using hresult
    simpa [← he] using hbound
  | case3 j path hne hgt hlen => simp at hlen
  | case4 j path hne hgt tail sibling hlen ih =>
    dsimp only [sibling] at *
    rw [openLoop.eq_def] at hresult
    simp only [if_neg hne, if_pos hgt, if_pos hlen] at hresult
    exact ih output hbound hresult
  | case5 j path hne hgt k tail sibling hks hcap hs hlen ih =>
    dsimp only [sibling] at *
    rw [openLoop.eq_def] at hresult
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks,
      if_pos hcap] at hresult
    rw [dif_pos hs] at hresult
    have hb : path.length < Topen := (Nat.mul_lt_mul_right hl).mp hcap
    exact ih output (by simpa using hb) hresult
  | case6 j path hne hgt k tail sibling hks hcap hs hlen =>
    dsimp only [sibling] at *
    rw [openLoop.eq_def] at hresult
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks,
      if_pos hcap, dif_neg hs] at hresult
    contradiction
  | case7 j path hne hgt k tail sibling hks hcap hlen =>
    dsimp only [sibling] at *
    rw [openLoop.eq_def] at hresult
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_neg hcap] at hresult
    contradiction
  | case8 j rest path hne hgt hlen ih =>
    rw [openLoop.eq_def] at hresult
    simp only [if_neg hne, if_pos hgt, if_neg hlen] at hresult
    exact ih output hbound hresult
  | case9 j rest path hne hgt =>
    rw [openLoop.eq_def] at hresult
    simp [hne, hgt] at hresult

theorem blocks_bit_length {lambda : Nat} (blocks : List (Seed lambda)) :
    (blocks.flatMap List.ofFn).length = blocks.length * lambda := by
  induction blocks with
  | nil => simp
  | cons head tail ih => simp [ih, Nat.add_mul, Nat.add_comm]

/-- The exact padded size printed on Algorithm 8 line 17, proved from the
actual loop and not added as an input invariant. -/
theorem openCommitment_path_length {lambda tau N : Nat} (key : Key lambda tau N)
    (hidden : Fin tau → Fin N) (Topen : Nat) (hl : 0 < lambda)
    (result : Opening lambda tau) (h : openCommitment key hidden Topen = .ok result) :
    result.path.length = Topen * lambda := by
  unfold openCommitment at h
  cases he : openLoop key.tree Topen (openingQueue hidden) [] with
  | error err => simp [he] at h
  | ok blocks =>
    have hb := openLoop_bound key.tree Topen hl (openingQueue hidden) [] blocks (by simp) he
    have hm := Nat.mul_le_mul_right lambda hb
    simp [he] at h
    subst result
    simp [Nat.add_sub_of_le hm]

/-- On a singleton queue the printed post-dequeue guard always skips the sibling
step. This proves the behavior of that literal branch, not opening correctness. -/
theorem openLoop_singleton {lambda tau N : Nat} (tree : Tree lambda tau N)
    (Topen j : Nat) (hj : 0 < j) (path : List (Seed lambda)) :
    openLoop tree Topen [j] path = .ok path := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rw [openLoop]
    by_cases h1 : j = 1
    · simp [h1]
    · have hgt : 1 < j := by omega
      simp only [if_neg h1, if_pos hgt, List.length_nil, Nat.reduceLeDiff,
        ↓reduceIte, List.nil_append]
      exact ih (j / 2) (by omega) (by omega)

/-- One execution produces no sibling seeds under the printed queue guard.
Only zero padding and the hidden commitment remain in the opening. -/
theorem one_execution_opening {lambda N : Nat} (key : Key lambda 1 N)
    (hidden : Fin 1 → Fin N) (Topen : Nat) :
    openCommitment key hidden Topen =
      .ok { path := List.replicate (Topen * lambda) false
            hiddenCommitments := fun e => key.commitments e (hidden e) } := by
  have hj : 0 < Spec.SeedTree.leafAddress (0 : Fin 1) (hidden 0) :=
    (SeedTree.leafAddress_bounds 0 (hidden 0)).1
  simp only [openCommitment, openingQueue, List.ofFn_succ, List.ofFn_zero,
    List.mergeSort_singleton]
  rw [openLoop_singleton key.tree Topen _ hj]
  rfl

end SDitH.Proofs.BAVC
