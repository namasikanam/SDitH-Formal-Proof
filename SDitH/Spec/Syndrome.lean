import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! The SD relation and regular vectors from §§2.2 and 5.1.
These use a fully expanded matrix. Seed expansion and serialization remain separate.
-/

namespace SDitH.Spec

open scoped BigOperators

variable {F : Type*} [Field F]

structure SDInstance (F : Type*) (n k : Nat) where
  H : Matrix (Fin (n - k)) (Fin n) F
  y : Fin (n - k) → F

noncomputable def hammingWeight {n : Nat} (x : Fin n → F) : Nat := by
  classical
  exact (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- Standard syndrome decoding asks for an exact weight-`w` solution. -/
def SDSolution {n k : Nat} (inst : SDInstance F n k) (w : Nat) (x : Fin n → F) : Prop :=
  inst.H.mulVec x = inst.y ∧ hammingWeight x = w

/-- One-hot vector; §2.2 and Algorithm 1. -/
noncomputable def elementary {I : Type*} (position : I) : I → F := by
  classical
  exact fun j => if j = position then 1 else 0

/-- Binary regularity: exactly one 1 per chunk. A product index explicitly
separates chunk and coordinate and avoids imposing the inconsistent Table 3
tensor dimension equation as an assumption. -/
def BinaryRegular {w m : Nat} (x : Fin w → Fin m → ZMod 2) : Prop :=
  ∀ i, ∃ p : Fin m, x i = elementary p

/-- The larger-field variant of §6.1 permits nonzero scaling per chunk. -/
def Regular {w m : Nat} (x : Fin w → Fin m → F) : Prop :=
  ∀ i, ∃ (p : Fin m) (a : F), a ≠ 0 ∧ x i = fun j => a * elementary p j

/-- The tensor factor on printed pp. 8 and 34: the omitted coordinate is last,
and is reconstructed as one minus the sum of the stored coordinates. -/
def completeSelector {r : Nat} (bits : Fin r → F) : Fin (r + 1) → F :=
  Fin.lastCases (1 - ∑ k, bits k) bits

/-- A tensor product indexed by tuples of coordinates, as in §2.2.
This definition does not claim a particular flattening order. -/
def tensor {J : Type*} [Fintype J] {I : J → Type*}
    (vectors : (j : J) → I j → F) (coordinate : (j : J) → I j) : F :=
  ∏ j, vectors j (coordinate j)

end SDitH.Spec
