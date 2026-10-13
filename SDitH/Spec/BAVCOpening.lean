import SDitH.Spec.BAVC
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Algorithm 8, printed p. 23. The queue test is deliberately the printed
post-dequeue `length ≥ 2`. No conventional tree-opening algorithm is substituted.
Errors distinguish explicit source rejection from undefined source operations.
-/

namespace SDitH.Spec.BAVC

inductive OpeningError where
  /-- The explicit bottom return on line 15. -/
  | boundExceeded
  /-- The source supplies no value for Head on an empty queue. -/
  | undefinedEmptyQueue
  /-- Zero is not a node of the source's tree. -/
  | undefinedZeroNode
  /-- A requested sibling lies outside the allocated key. -/
  | undefinedTreeRead
  deriving DecidableEq, Repr

/-- Lines 3–4. Each execution contributes its designated leaf, then the queue is
sorted in decreasing order. Distinct executions give distinct leaf addresses. -/
def openingQueue {tau N : Nat} (hidden : Fin tau → Fin N) : List Nat :=
  (List.ofFn fun e => SeedTree.leafAddress e (hidden e)).mergeSort (fun a b => b ≤ a)

/-- Lines 5–16. A path is stored as a list of lambda-bit blocks, so its exact
bit length is `path.length * lambda`. The termination measure is the sum of
queued addresses, not an arbitrary fuel cutoff. -/
def openLoop {lambda tau N : Nat} (tree : Tree lambda tau N) (Topen : Nat) :
    (queue : List Nat) → (path : List (Seed lambda)) →
      Except OpeningError (List (Seed lambda))
  | [], _ => .error .undefinedEmptyQueue
  | j :: rest, path =>
    if j = 1 then .ok path
    else if 1 < j then
      if 2 ≤ rest.length then
        match rest with
        | [] => .error .undefinedEmptyQueue
        | k :: tail =>
          let sibling := j ^^^ 1
          if k = sibling then
            openLoop tree Topen (tail ++ [j / 2]) path
          else if path.length * lambda < Topen * lambda then
            if hs : 0 < sibling ∧ sibling < 2 * (tau * N) then
              openLoop tree Topen ((k :: tail) ++ [j / 2]) (path ++ [tree ⟨sibling, hs⟩])
            else .error .undefinedTreeRead
          else .error .boundExceeded
      else openLoop tree Topen (rest ++ [j / 2]) path
    else .error .undefinedZeroNode
termination_by queue _ => queue.sum
decreasing_by
  all_goals simp_wf
  all_goals omega

structure Opening (lambda tau : Nat) where
  path : List Bool
  hiddenCommitments : Fin tau → Digest lambda

/-- Lines 17–20. Padding appends zero bits, and commitments remain in execution
order. Its target length is proved for every successful run with lambda > 0. -/
def openCommitment {lambda tau N : Nat} (key : Key lambda tau N)
    (hidden : Fin tau → Fin N) (Topen : Nat) : Except OpeningError (Opening lambda tau) := do
  let blocks ← openLoop key.tree Topen (openingQueue hidden) []
  let bits := blocks.flatMap List.ofFn
  return { path := bits ++ List.replicate (Topen * lambda - bits.length) false
           hiddenCommitments := fun e => key.commitments e (hidden e) }

end SDitH.Spec.BAVC
