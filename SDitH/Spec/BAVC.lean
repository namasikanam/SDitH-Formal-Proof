import SDitH.Spec.SeedTree
import SDitH.Spec.DomainSeparation

/-! Algorithm 7, printed p. 22, at its stated primitive-call boundary.
The hash receives the actual ordered bit string, including the domain byte.
`Primitives` contains functions, not correctness or security propositions.
Concrete Enc*/SHAKE implementations and their correspondence are separate work.
-/

namespace SDitH.Spec.BAVC

open DomainSeparation

abbrev Seed (lambda : Nat) := Bits lambda
abbrev Digest (lambda : Nat) := Bits (2 * lambda)
abbrev NodeAddress (tau N : Nat) := {i : Nat // 0 < i ∧ i < 2 * (tau * N)}
abbrev Tree (lambda tau N : Nat) := NodeAddress tau N → Seed lambda

/-- The three primitive calls in Algorithm 7. Argument orders are made explicit.
No collision resistance, pseudorandomness, or tree correctness is postulated. -/
structure Primitives (lambda : Nat) where
  expandSeed : Bits lambda → Nat → Seed lambda → Seed lambda × Seed lambda
  commitSeed : Bits lambda → Seed lambda → Nat → Digest lambda
  hash : List Bool → Digest lambda

def byteBits (b : Byte) : List Bool :=
  List.ofFn (fun j : Fin 8 => b.val.testBit j.val)

def hashBavc {lambda : Nat} (p : Primitives lambda) (payload : List Bool) :
    Digest lambda :=
  p.hash (byteBits 1 ++ payload)

/-- Array concatenation in increasing index order. -/
def serializeArray {n bits : Nat} (v : Fin n → Bits bits) : List Bool :=
  (List.ofFn v).flatMap List.ofFn

def leafNode {tau N : Nat} (e : Fin tau) (i : Fin N) : NodeAddress tau N :=
  ⟨SeedTree.leafAddress e i, by
    have hi := i.isLt
    have he := e.isLt
    have hm := Nat.mul_le_mul_left tau hi
    rw [Nat.mul_succ, Nat.mul_comm tau i.val] at hm
    dsimp [SeedTree.leafAddress, SeedTree.leafOffset]
    constructor <;> omega⟩

structure Key (lambda tau N : Nat) where
  tree : Tree lambda tau N
  commitments : Fin tau → Fin N → Digest lambda

structure CommitResult (lambda tau N : Nat) where
  seeds : Fin tau → Fin N → Seed lambda
  hcom : Digest lambda
  key : Key lambda tau N

/-- Lines 4–11. Both levels of hashing and the salt position are explicit. -/
def commitFromTree {lambda tau N : Nat} (p : Primitives lambda) (salt : Bits lambda)
    (tree : Tree lambda tau N) : CommitResult lambda tau N :=
  let seeds := fun e i => tree (leafNode e i)
  let commits := fun e i => p.commitSeed salt (seeds e i) (SeedTree.leafOffset e i)
  let rowHashes := fun e => hashBavc p (serializeArray (commits e))
  { seeds := seeds
    hcom := hashBavc p (List.ofFn salt ++ serializeArray rowHashes)
    key := ⟨tree, commits⟩ }

/-- Lines 1–3. The initial total-memory value is a choice outside the printed
allocated array; the independent proof shows it cannot affect this result. -/
def buildTree {lambda tau N : Nat} (p : Primitives lambda) (salt root : Bits lambda)
    (initial : Nat → Seed lambda) : Tree lambda tau N :=
  fun a => SeedTree.run (p.expandSeed salt) root initial (tau * N - 1) a.val

/-- Algorithm 7 for positive tau and N. The exact range condition for its
mathematical tree characterization is proved, not imposed on the primitives. -/
def commit {lambda tau N : Nat} (p : Primitives lambda) (salt root : Bits lambda) :
    CommitResult lambda tau N :=
  commitFromTree p salt (buildTree p salt root (fun _ => root))

end SDitH.Spec.BAVC
