import SDitH.Spec.BAVCOpening
import SDitH.Spec.CommitmentChecks

/-! Algorithm 9's full staged body, printed p. 24, beginning with a typed opening.
The first-action interface is retained for the earlier discrepancy proofs.
Queue prefill keeps the printed post-dequeue guard and path-length comparison.
Expansion retains distinct tree/nodes names with an explicit missing binding;
leaf/row loops and both hashes follow in order. Undefined operations are separate
from the two explicit source rejection branches. This is not a source repair.
-/

namespace SDitH.Spec.BAVC

/-- `none` means there is no first sibling-comparison branch; `some reject`
is the explicit bottom return from the source's first loop iteration. -/
def firstReconstructionAction {lambda tau N : Nat} (hidden : Fin tau → Fin N)
    (opening : Opening lambda tau) (Topen : Nat) : Option SiblingAction :=
  match openingQueue hidden with
  | j :: k :: tail =>
    if j = 1 then none
    else some (reconstructSiblingAction (1 + tail.length) j k opening.path.length Topen lambda)
  | _ => none

inductive ReconstructionError where
  /-- Explicit line-15 bottom return. -/
  | boundRejected
  /-- Explicit line-18 bottom return. -/
  | paddingRejected
  | undefinedEmptyQueue
  | undefinedZeroNode
  | undefinedTreeWrite
  | undefinedPathRead
  /-- The source has not defined the array named nodes. -/
  | undefinedNodesArray
  /-- A declared partial array still lacks the seed being read. -/
  | undefinedNodeRead
  deriving DecidableEq, Repr

abbrev PartialTree (lambda tau N : Nat) := NodeAddress tau N → Option (Seed lambda)

structure Prefilled (lambda tau N : Nat) where
  tree : PartialTree lambda tau N
  remaining : List Bool

/-- A successful extraction requires lambda available bits. Short input is
not zero-padded or filled with a default value. -/
def pathSeed {lambda : Nat} (path : List Bool) (enough : lambda ≤ path.length) : Seed lambda :=
  fun i => path[i.val]'(i.isLt.trans_le enough)

/-- Algorithm 9 lines 6–16, with the actual printed guards. Termination follows
the decreasing sum of queue addresses and does not depend on an arbitrary fuel. -/
def prefillLoop {lambda tau N : Nat} (Topen : Nat) :
    (queue : List Nat) → (path : List Bool) → PartialTree lambda tau N →
      Except ReconstructionError (Prefilled lambda tau N)
  | [], _, _ => .error .undefinedEmptyQueue
  | j :: rest, path, tree =>
    if j = 1 then .ok ⟨tree, path⟩
    else if 1 < j then
      if 2 ≤ rest.length then
        match rest with
        | [] => .error .undefinedEmptyQueue
        | k :: tail =>
          let sibling := j ^^^ 1
          if k = sibling then
            prefillLoop Topen (tail ++ [j / 2]) path tree
          else if path.length < Topen * lambda then
            if hs : 0 < sibling ∧ sibling < 2 * (tau * N) then
              if hp : lambda ≤ path.length then
                prefillLoop Topen ((k :: tail) ++ [j / 2]) (path.drop lambda)
                  (Function.update tree ⟨sibling, hs⟩ (some (pathSeed path hp)))
              else .error .undefinedPathRead
            else .error .undefinedTreeWrite
          else .error .boundRejected
      else prefillLoop Topen (rest ++ [j / 2]) path tree
    else .error .undefinedZeroNode
termination_by queue _ _ => queue.sum
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Lines 1–18. `any id` is the nonzero-bit test of the remaining bitstring;
the explicit nonempty guard is kept as printed. -/
def prefill {lambda tau N : Nat} (hidden : Fin tau → Fin N)
    (opening : Opening lambda tau) (Topen : Nat) : Except ReconstructionError (PartialTree lambda tau N) := do
  let filled ← prefillLoop Topen (openingQueue hidden) opening.path (fun _ => none)
  if 0 < filled.remaining.length ∧ filled.remaining.any id = true then
    .error .paddingRejected
  else .ok filled.tree

def internalNode {tau N : Nat} (i : Fin (tau * N - 1)) : NodeAddress tau N :=
  ⟨i.val + 1, by have hi := i.isLt; constructor <;> omega⟩

def internalLeft {tau N : Nat} (i : Fin (tau * N - 1)) : NodeAddress tau N :=
  ⟨2 * (i.val + 1), by have hi := i.isLt; constructor <;> omega⟩

def internalRight {tau N : Nat} (i : Fin (tau * N - 1)) : NodeAddress tau N :=
  ⟨2 * (i.val + 1) + 1, by have hi := i.isLt; constructor <;> omega⟩

/-- A variable binding for `nodes`, distinct from the locally initialized
`tree`. None is an undeclared array; some memory may still contain empty cells.
No alias or copying rule between the two source names is invented. -/
abbrev NodesBinding (lambda tau N : Nat) := Option (PartialTree lambda tau N)

def readNode {lambda tau N : Nat} (nodes : NodesBinding lambda tau N) (i : NodeAddress tau N) :
    Except ReconstructionError (Seed lambda) :=
  match nodes with
  | none => .error .undefinedNodesArray
  | some values =>
    match values i with
    | none => .error .undefinedNodeRead
    | some seed => .ok seed

/-- Lines 20–21 test tree[i], then read and update nodes. The tested `tree`
is unchanged when `nodes` is updated; identifying them would be a correction.
The salt/index argument order follows the existing ExpandSeed interface. -/
def expandPartialStep {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (tree : PartialTree lambda tau N) (nodes : NodesBinding lambda tau N)
    (i : Fin (tau * N - 1)) : Except ReconstructionError (NodesBinding lambda tau N) :=
  match tree (internalNode i) with
  | none => .ok nodes
  | some _ =>
    match nodes with
    | none => .error .undefinedNodesArray
    | some values =>
      match values (internalNode i) with
      | none => .error .undefinedNodeRead
      | some seed =>
        let children := p.expandSeed salt (i.val + 1) seed
        .ok (some (Function.update (Function.update values (internalLeft i) (some children.1))
          (internalRight i) (some children.2)))

/-- The increasing-index expansion loop, with safe parent and child addresses
derived from the printed 1..tau*N-1 range. -/
def expandPartialThrough {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (tree : PartialTree lambda tau N) (initial : NodesBinding lambda tau N) :
    (count : Nat) → count ≤ tau * N - 1 → Except ReconstructionError (NodesBinding lambda tau N)
  | 0, _ => .ok initial
  | count + 1, hc => do
    let nodes ← expandPartialThrough p salt tree initial count (by omega)
    expandPartialStep p salt tree nodes ⟨count, by omega⟩

structure ReconstructedLeaf (lambda : Nat) where
  seed : Option (Seed lambda)
  commitment : Digest lambda

/-- Lines 24–29 at one leaf. The hidden digest is already a typed component
of the opening, in execution order. Revealed seeds must actually be present. -/
def reconstructLeaf {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau)
    (nodes : NodesBinding lambda tau N) (e : Fin tau) (i : Fin N) :
    Except ReconstructionError (ReconstructedLeaf lambda) :=
  if i = hidden e then .ok ⟨none, opening.hiddenCommitments e⟩
  else do
    let seed ← readNode nodes (leafNode e i)
    .ok ⟨some seed, p.commitSeed salt seed (SeedTree.leafOffset e i)⟩

/-- The increasing leaf loop for one execution. The output length is part of
the type; no default commitment is used to fill uninitialized entries. -/
def reconstructRowThrough {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau)
    (nodes : NodesBinding lambda tau N) (e : Fin tau) :
    (count : Nat) → count ≤ N → Except ReconstructionError (Vector (ReconstructedLeaf lambda) count)
  | 0, _ => .ok #v[]
  | count + 1, hc => do
    let row ← reconstructRowThrough p salt hidden opening nodes e count (by omega)
    let value ← reconstructLeaf p salt hidden opening nodes e ⟨count, by omega⟩
    .ok (row.push value)

def reconstructRowsThrough {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N) :
    (count : Nat) → count ≤ tau →
      Except ReconstructionError (Vector (Vector (ReconstructedLeaf lambda) N) count)
  | 0, _ => .ok #v[]
  | count + 1, hc => do
    let rows ← reconstructRowsThrough p salt hidden opening nodes count (by omega)
    let row ← reconstructRowThrough p salt hidden opening nodes ⟨count, by omega⟩ N le_rfl
    .ok (rows.push row)

structure Reconstructed (lambda tau N : Nat) where
  hcom : Digest lambda
  seeds : Fin tau → Fin N → Option (Seed lambda)

/-- The two levels of Hashbavc, retaining the salt and the increasing array
order of Algorithms 7/9. No hash collision claim is embedded in this definition. -/
def reconstructionHashes {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (rows : Vector (Vector (ReconstructedLeaf lambda) N) tau) : Reconstructed lambda tau N :=
  let rowHashes := fun e : Fin tau => hashBavc p (serializeArray fun i : Fin N => (rows[e][i]).commitment)
  { hcom := hashBavc p (List.ofFn salt ++ serializeArray rowHashes)
    seeds := fun e i => (rows[e][i]).seed }

/-- Full staged Algorithm-9 body with an explicit external binding for the
undeclared nodes array. This argument is not an assertion that the PDF supplies
such a binding, nor a correctness contract. `reconstruct` below leaves it absent. -/
def reconstructWithNodes {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (initialNodes : NodesBinding lambda tau N) : Except ReconstructionError (Reconstructed lambda tau N) := do
  let tree ← prefill hidden opening Topen
  let nodes ← expandPartialThrough p salt tree initialNodes (tau * N - 1) le_rfl
  let rows ← reconstructRowsThrough p salt hidden opening nodes tau le_rfl
  .ok (reconstructionHashes p salt rows)

/-- No declaration of nodes occurs in Algorithm 9. Absent-array faults are
undefined source reads, separate from the explicit bottom returns. -/
def reconstruct {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) :
    Except ReconstructionError (Reconstructed lambda tau N) :=
  reconstructWithNodes p salt hidden opening Topen none

end SDitH.Spec.BAVC
