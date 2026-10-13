import SDitH.Spec.BAVCReconstruction
import SDitH.Proofs.BAVCOpening
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

namespace SDitH.Proofs.BAVC

open Spec.BAVC

theorem sibling_formula (j : Nat) :
    j ^^^ 1 = if j % 2 = 0 then j + 1 else j - 1 := by
  split
  · exact Nat.xor_one_of_even (Nat.even_iff.mpr ‹j % 2 = 0›)
  · apply Nat.xor_one_of_odd
    apply Nat.odd_iff.mpr
    omega

/-- A legal hidden-index vector for Table 4's Category-I short instance. -/
def categoryIHidden : Fin 11 → Fin 2048 := fun e => if e.val = 10 then 1 else 0

theorem categoryI_queue :
    openingQueue categoryIHidden =
      [22549, 22537, 22536, 22535, 22534, 22533, 22532, 22531, 22530, 22529, 22528] := by
  unfold openingQueue
  rw [List.mergeSort_eq_insertionSort]
  decide

/-- The complete list of sibling seeds actually appended by the literal loop.
Every address is proved inside the allocated source tree. -/
def categoryIPath (tree : Tree 128 11 2048) : List (Seed 128) :=
  [tree ⟨22548, by decide⟩, tree ⟨11275, by decide⟩,
   tree ⟨11269, by decide⟩, tree ⟨5636, by decide⟩,
   tree ⟨5635, by decide⟩, tree ⟨2819, by decide⟩]

/-- Equation rewriting and kernel-checked arithmetic cover all 35 loop
iterations; tree values are arbitrary. No external evaluation is trusted. -/
theorem categoryI_open_loop (tree : Tree 128 11 2048) :
    openLoop tree 109 (openingQueue categoryIHidden) [] = .ok (categoryIPath tree) := by
  rw [categoryI_queue]
  unfold categoryIPath
  repeat (rw [openLoop.eq_def]; norm_num [sibling_formula])

def categoryIOpening (key : Key 128 11 2048) : Opening 128 11 :=
  { path := (categoryIPath key.tree).flatMap List.ofFn ++ List.replicate ((109 - 6) * 128) false
    hiddenCommitments := fun e => key.commitments e (categoryIHidden e) }

theorem categoryI_open_succeeds (key : Key 128 11 2048) :
    openCommitment key categoryIHidden 109 = .ok (categoryIOpening key) := by
  unfold openCommitment
  rw [categoryI_open_loop]
  have hlen : ((categoryIPath key.tree).flatMap List.ofFn).length = 6 * 128 := by
    rw [blocks_bit_length]
    rfl
  change (Except.ok
    ({ path := (categoryIPath key.tree).flatMap List.ofFn ++
        List.replicate (109 * 128 - ((categoryIPath key.tree).flatMap List.ofFn).length) false
       hiddenCommitments := fun e => key.commitments e (categoryIHidden e) } : Opening 128 11) :
        Except OpeningError (Opening 128 11)) = .ok (categoryIOpening key)
  rw [hlen]
  rfl

/-- A full successful Algorithm-8 opening reaches explicit rejection in the
first Algorithm-9 iteration. This uses submitted tau, N, lambda, and Topen and
does not depend on cipher or hash outputs. It does not execute a signature. -/
theorem categoryI_opening_rejected (key : Key 128 11 2048) :
    openCommitment key categoryIHidden 109 = .ok (categoryIOpening key) ∧
      firstReconstructionAction categoryIHidden (categoryIOpening key) 109 = some .reject := by
  refine ⟨categoryI_open_succeeds key, ?_⟩
  have hlen := openCommitment_path_length key categoryIHidden 109 (by decide)
    (categoryIOpening key) (categoryI_open_succeeds key)
  simp only [firstReconstructionAction, categoryI_queue]
  simp only [show ¬ (22549 : Nat) = 1 by decide, ↓reduceIte, hlen]
  decide

end SDitH.Proofs.BAVC
