import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.OfFn

/-!
Algorithm 7's heap-indexed seed tree, printed p. 22.

`expand i seed` is the ExpandSeed call with the salt already fixed. No
pseudorandomness, injectivity, or cryptographic security property is assumed.
The imperative loop and its recursively characterized tree are both defined;
their equality on the allocated nodes is proved in a separate module.
-/

namespace SDitH.Spec.SeedTree

variable {Seed : Type*}

/-- Mathematical tree indexed by positive integers. Address zero is unused by
the source and is assigned the root only to totalize this auxiliary function. -/
def node (expand : Nat → Seed → Seed × Seed) (root : Seed) (address : Nat) : Seed :=
  if address ≤ 1 then root
  else
    let children := expand (address / 2) (node expand root (address / 2))
    if address % 2 = 0 then children.1 else children.2
termination_by address
decreasing_by omega

/-- Algorithm 7 line 3: update both children after reading their parent. -/
def expandStep (expand : Nat → Seed → Seed × Seed) (tree : Nat → Seed) (i : Nat) :
    Nat → Seed :=
  let children := expand i (tree i)
  Function.update (Function.update tree (2 * i) children.1) (2 * i + 1) children.2

/-- The actual increasing-index loop in Algorithm 7 lines 1–3. `initial` gives
unspecified memory contents outside initialized cells. The proof shows that
every allocated output node is independent of these arbitrary initial values. -/
def run (expand : Nat → Seed → Seed × Seed) (root : Seed) (initial : Nat → Seed) :
    Nat → (Nat → Seed)
  | 0 => Function.update initial 1 root
  | steps + 1 => expandStep expand (run expand root initial steps) (steps + 1)

/-- The interleaved leaf offset from Algorithm 7 line 6. -/
def leafOffset {tau N : Nat} (execution : Fin tau) (index : Fin N) : Nat :=
  index.val * tau + execution.val

def leafAddress {tau N : Nat} (execution : Fin tau) (index : Fin N) : Nat :=
  tau * N + leafOffset execution index

end SDitH.Spec.SeedTree
