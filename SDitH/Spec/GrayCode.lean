import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Gray encoding and the prefix-fold formulas (4)–(5), printed pp. 25–26.
Rows are indexed most-significant-first, matching the displayed bin_kappa tuple.
The prefix identity is algebraic; the operation-count claim is a separate boundary.
-/

namespace SDitH.Spec.GrayCode

open scoped BigOperators

def grayWord (i : Nat) : Nat := i ^^^ (i / 2)

def binaryRow {kappa : Nat} (i : Fin (2 ^ kappa)) : Fin kappa → Bool :=
  fun j => i.val.testBit (kappa - 1 - j.val)

def grayRow {kappa : Nat} (i : Fin (2 ^ kappa)) : Fin kappa → Bool :=
  fun j => (grayWord i.val).testBit (kappa - 1 - j.val)

/-- The actual F2-valued row used in the folding equations. -/
def grayFieldRow {kappa : Nat} (i : Fin (2 ^ kappa)) : Fin kappa → ZMod 2 :=
  fun j => if grayRow i j then 1 else 0

/-- Explicit finite-array extension, implementing the stated phi(N)=0 boundary.
The values beyond N are auxiliary and are never read by differenceFold. -/
def extendZero {K : Type*} [Zero K] {N : Nat} (v : Fin N → K) (i : Nat) : K :=
  if h : i < N then v ⟨i, h⟩ else 0

/-- Accumulator before processing index n; equation (4) uses n=j+1. -/
def prefixAcc {K : Type*} [AddMonoid K] (random : Nat → K) : Nat → K
  | 0 => 0
  | n + 1 => prefixAcc random n + random n

/-- Equation (5). To use the source's last transition, phi(N) must be set to 0,
as expressly required on printed p. 25; grayWord(N) is not silently identified
with that boundary value. -/
def differenceFold {K : Type*} [Ring K] (random phi : Nat → K) (N : Nat) : K :=
  ∑ j ∈ Finset.range N, prefixAcc random (j + 1) * (phi j - phi (j + 1))

end SDitH.Spec.GrayCode
