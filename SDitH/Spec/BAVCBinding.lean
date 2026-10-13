import SDitH.Spec.BAVCReconstruction

/-! Explicit collision finding for the two Hashbavc layers of Algorithms 7/9.
The finder compares actual serialized bit strings, including their domain byte.
It is a deterministic computation, not a collision-resistance assumption.
The proof module connects it to successfully reconstructed revealed seeds. -/

namespace SDitH.Spec.BAVCBinding

open BAVC

abbrev Commitments (lambda tau N : Nat) := Fin tau → Fin N → Digest lambda
abbrev QueryPair := List Bool × List Bool

def HashCollision {Output : Type*} (hash : List Bool → Output) (pair : QueryPair) : Prop :=
  pair.1 ≠ pair.2 ∧ hash pair.1 = hash pair.2

def IsHashCollision {lambda : Nat} (p : Primitives lambda) (pair : QueryPair) : Prop :=
  HashCollision p.hash pair

def rowQuery {lambda tau N : Nat} (commits : Commitments lambda tau N) (e : Fin tau) : List Bool :=
  byteBits 1 ++ serializeArray (commits e)

def outerQuery {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (commits : Commitments lambda tau N) : List Bool :=
  byteBits 1 ++ (List.ofFn salt ++ serializeArray (fun e => p.hash (rowQuery commits e)))

/-- Calls in the specified order: each row hash, then the salt-bound outer hash. -/
def hashQueries {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (commits : Commitments lambda tau N) : List (List Bool) :=
  List.ofFn (rowQuery commits) ++ [outerQuery p salt commits]

def rootHash {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (commits : Commitments lambda tau N) : Digest lambda :=
  p.hash (outerQuery p salt commits)

def rowCommitments {lambda tau N : Nat}
    (rows : Vector (Vector (ReconstructedLeaf lambda) N) tau) : Commitments lambda tau N :=
  fun e i => (rows[e][i]).commitment

/-- If outer inputs differ, return them. Otherwise scan executions in order
for the first differing row input. Equal roots make a returned pair a collision;
the algorithm does not itself assume that roots agree or hashes are injective. -/
def findHashCollision {lambda tau N : Nat} (p : Primitives lambda)
    (leftSalt rightSalt : Seed lambda) (left right : Commitments lambda tau N) : Option QueryPair :=
  if outerQuery p leftSalt left = outerQuery p rightSalt right then
    ((List.finRange tau).find? (fun e => decide (rowQuery left e ≠ rowQuery right e))).map
      (fun e => (rowQuery left e, rowQuery right e))
  else some (outerQuery p leftSalt left, outerQuery p rightSalt right)

def IsSeedCollision {lambda : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (index : Nat) (left right : Seed lambda) : Prop :=
  left ≠ right ∧ p.commitSeed salt left index = p.commitSeed salt right index

/-- Instrument the exact staged reconstruction, retaining its internal rows.
No missing binding is supplied and no source guard or error is changed. -/
def reconstructionRows {lambda tau N : Nat} (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (initial : NodesBinding lambda tau N) :
    Except ReconstructionError (Vector (Vector (ReconstructedLeaf lambda) N) tau) := do
  let tree ← prefill hidden opening Topen
  let nodes ← expandPartialThrough p salt tree initial (tau * N - 1) le_rfl
  reconstructRowsThrough p salt hidden opening nodes tau le_rfl

/-- Run both actual reconstructions and compare their computed hash inputs.
A missing row computation remains an error. A none result only says these two
executions have no differing Hashbavc input; it says nothing about seed binding. -/
def findReconstructionCollision {lambda tau N : Nat} (p : Primitives lambda)
    (leftSalt rightSalt : Seed lambda) (leftHidden rightHidden : Fin tau → Fin N)
    (leftOpening rightOpening : Opening lambda tau) (Topen : Nat)
    (leftNodes rightNodes : NodesBinding lambda tau N) : Except ReconstructionError (Option QueryPair) := do
  let left ← reconstructionRows p leftSalt leftHidden leftOpening Topen leftNodes
  let right ← reconstructionRows p rightSalt rightHidden rightOpening Topen rightNodes
  .ok (findHashCollision p leftSalt rightSalt (rowCommitments left) (rowCommitments right))

end SDitH.Spec.BAVCBinding
