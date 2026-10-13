import SDitH.Proofs.BAVCOpening
import Mathlib.Data.Nat.Bitwise

namespace SDitH.Proofs.BAVC

open Spec.BAVC

/-- Every queued address belongs to the allocated tree and Head is defined. -/
def ValidQueue (L : Nat) (queue : List Nat) : Prop :=
  queue ≠ [] ∧ ∀ j ∈ queue, 0 < j ∧ j < 2 * L

/-- A value or the explicit source abort; no undefined-operation error. -/
def SourceOutcome {α : Type*} : Except OpeningError α → Prop
  | .ok _ => True
  | .error err => err = .boundExceeded

theorem parent_queue_valid {L j : Nat} {queue : List Nat}
    (hj : 1 < j) (hbound : j < 2 * L)
    (hq : ∀ k ∈ queue, 0 < k ∧ k < 2 * L) :
    ValidQueue L (queue ++ [j / 2]) := by
  constructor
  · simp
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hq k hk
    · have he : k = j / 2 := List.mem_singleton.mp hk
      subst k
      constructor <;> omega

theorem sibling_in_bounds {L j : Nat} (hj : 1 < j) (hbound : j < 2 * L) :
    0 < j ^^^ 1 ∧ j ^^^ 1 < 2 * L := by
  by_cases he : Even j
  · rw [Nat.xor_one_of_even he]
    have hm := Nat.even_iff.mp he
    constructor <;> omega
  · rw [Nat.xor_one_of_odd (Nat.not_even_iff_odd.mp he)]
    constructor <;> omega

/-- All legal states remain inside allocated addresses. The printed sibling
guard is untouched; this establishes memory/queue safety, not reveal correctness. -/
theorem openLoop_source_outcome {lambda tau N : Nat} (tree : Tree lambda tau N)
    (Topen : Nat) (queue : List Nat) (path : List (Seed lambda))
    (hq : ValidQueue (tau * N) queue) : SourceOutcome (openLoop tree Topen queue path) := by
  induction queue, path using openLoop.induct tree Topen with
  | case1 path => exact False.elim (hq.1 rfl)
  | case2 rest path => rw [openLoop.eq_def]; simp [SourceOutcome]
  | case3 j path hne hgt hlen => simp at hlen
  | case4 j path hne hgt tail sibling hlen ih =>
    have hj := hq.2 j (by simp)
    have ht : ∀ k ∈ tail, 0 < k ∧ k < 2 * (tau * N) := by
      intro k hk
      exact hq.2 k (by simp [hk])
    dsimp only [sibling] at *
    rw [openLoop.eq_def]
    simp only [if_neg hne, if_pos hgt, if_pos hlen]
    exact ih (parent_queue_valid hgt hj.2 ht)
  | case5 j path hne hgt k tail sibling hks hcap hs hlen ih =>
    have hj := hq.2 j (by simp)
    have ht : ∀ x ∈ k :: tail, 0 < x ∧ x < 2 * (tau * N) := by
      intro x hx
      exact hq.2 x (by simp [hx])
    dsimp only [sibling] at *
    rw [openLoop.eq_def]
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_pos hcap]
    rw [dif_pos hs]
    exact ih (parent_queue_valid hgt hj.2 ht)
  | case6 j path hne hgt k tail sibling hks hcap hs hlen =>
    have hj := hq.2 j (by simp)
    exact False.elim (hs (sibling_in_bounds hgt hj.2))
  | case7 j path hne hgt k tail sibling hks hcap hlen =>
    dsimp only [sibling] at *
    rw [openLoop.eq_def]
    simp only [if_neg hne, if_pos hgt, if_pos hlen, if_neg hks, if_neg hcap]
    rfl
  | case8 j rest path hne hgt hlen ih =>
    have hj := hq.2 j (by simp)
    have ht : ∀ k ∈ rest, 0 < k ∧ k < 2 * (tau * N) := by
      intro k hk
      exact hq.2 k (by simp [hk])
    rw [openLoop.eq_def]
    simp only [if_neg hne, if_pos hgt, if_neg hlen]
    exact ih (parent_queue_valid hgt hj.2 ht)
  | case9 j rest path hne hgt =>
    have hj := (hq.2 j (by simp)).1
    omega

theorem openingQueue_valid {tau N : Nat} (hidden : Fin tau → Fin N) (ht : 0 < tau) :
    ValidQueue (tau * N) (openingQueue hidden) := by
  constructor
  · intro he
    have hl := congrArg List.length he
    simp [openingQueue] at hl
    omega
  · intro j hj
    simp only [openingQueue, List.mem_mergeSort, List.mem_ofFn] at hj
    obtain ⟨e, rfl⟩ := hj
    exact SeedTree.leafAddress_bounds e (hidden e)

/-- On every legal hidden-index vector, Algorithm 8 either returns an opening
or its explicit capacity abort. All added undefined-operation tags are excluded. -/
theorem openCommitment_source_outcome {lambda tau N : Nat} (key : Key lambda tau N)
    (hidden : Fin tau → Fin N) (Topen : Nat) (ht : 0 < tau) :
    SourceOutcome (openCommitment key hidden Topen) := by
  have h := openLoop_source_outcome key.tree Topen (openingQueue hidden) []
    (openingQueue_valid hidden ht)
  unfold openCommitment
  cases he : openLoop key.tree Topen (openingQueue hidden) [] with
  | error err => simpa [he] using h
  | ok blocks => simp [SourceOutcome]

end SDitH.Proofs.BAVC
