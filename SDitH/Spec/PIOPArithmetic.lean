import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Arithmetic shared by the prover and verifier in §3.2.6, printed pp. 32–37.

The displayed mux recurrence is used here with typed indices. `widths` lists the
numbers of stored selector coordinates, so each arity is `width + 1`. This
specifies the arithmetic, not byte parsing, challenge expansion, or the undefined
index on Algorithm 17 line 4. Its relationship to the last-coordinate-omitting
tensor encoding must be established separately (see the source discrepancy log).

The polynomial and field versions are both actual computations in this module;
their agreement will be proved, not taken as an interface assumption.
-/

namespace SDitH.Spec.PIOPArithmetic

universe u

open Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The mux gate on printed p. 34, with the first input as the default. -/
def mux {r : Nat} (bits : Fin r → R) (values : Fin (r + 1) → R) : R :=
  values 0 + ∑ k, bits k * (values k.succ - values 0)

/-- Algorithms 15 and 16, where the actual arity is `r+1`.
The last stored coordinate participates only in the first sum, exactly as printed. -/
def unitaryCheck (ξ : R) {r : Nat} (bits : Fin r → R) : R :=
  (∑ k, ξ ^ k.val * bits k) *
    (∑ k : Fin (r - 1), ξ ^ (r * k.val) * bits (k.castLE (Nat.sub_le r 1))) -
    ∑ k : Fin (r - 1), ξ ^ ((r + 1) * k.val) * bits (k.castLE (Nat.sub_le r 1))

/-- Algorithm 13/14 line 7, using the printed exponent `d-2-i`.
The randomness vector is already parsed by row and bit. -/
def formatMask {d lambda : Nat} (ξ z : R) (randomness : Fin (d - 1) → Fin lambda → R) : R :=
  ∑ i, (∑ j, ξ ^ j.val * randomness i j) * z ^ (d - 2 - i.val)

/-- Number of leaves of the displayed mux recurrence, with arity `r+1` at each layer. -/
def leafCount : List Nat → Nat
  | [] => 1
  | r :: rest => (r + 1) * leafCount rest

/-- The selectors of successive mux layers, before flattening/serialization. -/
def Selectors (R : Type u) : List Nat → Type u
  | [] => PUnit
  | r :: rest => (Fin r → R) × Selectors R rest

/-- The degree-at-most-one input condition for each witness polynomial. -/
def LinearSelectors : (widths : List Nat) → Selectors R[X] widths → Prop
  | [], _ => True
  | _ :: rest, selectors =>
      (∀ k, (selectors.1 k).natDegree ≤ 1) ∧ LinearSelectors rest selectors.2

/-- Apply a scalar map to every stored selector coordinate. -/
def mapSelectors {S : Type*} (f : R → S) :
    (widths : List Nat) → Selectors R widths → Selectors S widths
  | [], _ => PUnit.unit
  | _ :: rest, selectors =>
      (fun k => f (selectors.1 k), mapSelectors f rest selectors.2)

/-- Number of stored witness coordinates in one chunk. -/
def selectorCount : List Nat → Nat
  | [] => 0
  | r :: rest => r + selectorCount rest

/-- Algorithm 13/14 lines 3–6 within a single chunk: take each layer's stored
coordinates consecutively. No default or unchecked out-of-bounds read is used. -/
def parseSelectors : (widths : List Nat) → (Fin (selectorCount widths) → R) →
    Selectors R widths
  | [], _ => PUnit.unit
  | r :: rest, flat =>
      (fun k => flat (Fin.castAdd (selectorCount rest) k),
        parseSelectors rest (fun k => flat (Fin.natAdd r k)))

/-- Linear address `arity * row + column` used by the mux-tree recurrence. -/
def blockIndex {a m : Nat} (row : Fin m) (col : Fin a) : Fin (a * m) :=
  ⟨a * row.val + col.val, by
    calc
      a * row.val + col.val < a * row.val + a := Nat.add_lt_add_left col.isLt _
      _ = a * (row.val + 1) := by simp [Nat.mul_add]
      _ ≤ a * m := Nat.mul_le_mul_left a row.isLt⟩

/-- Algorithm 13/14 lines 1–6, including the outer chunk loop.
`selectorCount * w` is the same length as the source's `w * selectorCount`. -/
def formatWitness {w : Nat} (widths : List Nat)
    (flat : Fin (selectorCount widths * w) → R) : Fin w → Selectors R widths :=
  fun i => parseSelectors widths (fun k => flat (blockIndex i k))

/-- The index `i*lambda+j` in Algorithm 13/14 line 7. -/
def formatRandomness {d lambda : Nat} (flat : Fin (lambda * (d - 1)) → R) :
    Fin (d - 1) → Fin lambda → R :=
  fun i j => flat (blockIndex i j)

/-- Collapse the first layer of adjacent leaves, then continue toward the root.
The first supplied arity is the least significant coordinate in the leaf address,
matching the arithmetic indexing `μj * h + k` in the displayed recurrence. -/
def muxTree : (widths : List Nat) → Selectors R widths → (Fin (leafCount widths) → R) → R
  | [], _, leaves => leaves ⟨0, by decide⟩
  | _ :: rest, selectors, leaves =>
      muxTree rest selectors.2 (fun row => mux selectors.1 (fun col => leaves (blockIndex row col)))

/-- The packed unitary-constraint sum in Algorithms 19/20 line 7.
`layer` is zero based, so its exponent is the printed `32*(j-1)` for one-based j. -/
def unitaryLayers (ξ : R) : (widths : List Nat) → Selectors R widths → Nat → R
  | [], _, _ => 0
  | _ :: rest, selectors, layer =>
      ξ ^ (32 * layer) * unitaryCheck ξ selectors.1 +
        unitaryLayers ξ rest selectors.2 (layer + 1)

/-- Arithmetic body of Algorithms 19 and 20, after parsing and challenge expansion.
The batched syndrome is subtracted as in line 4 of those algorithms (although it
is absent from an intervening prose equation). -/
def runArithmetic {w : Nat} (widths : List Nat) (ξ z mask syndrome : R)
    (gamma : Fin w → R) (selectors : Fin w → Selectors R widths)
    (columns : Fin w → Fin (leafCount widths) → R) : R :=
  mask * z - syndrome +
    ∑ i, (muxTree widths (selectors i) (columns i) +
      gamma i * unitaryLayers ξ widths (selectors i) 0)

/-- Prover arithmetic with the true polynomial input arrays. Public field
constants are embedded by `C`; the masking polynomial is computed, not supplied
through a correctness contract. -/
noncomputable def proverArithmetic {w lambda : Nat} (widths : List Nat) (ξ syndrome : R)
    (gamma : Fin w → R) (selectors : Fin w → Selectors R[X] widths)
    (randomness : Fin (widths.length - 1) → Fin lambda → R[X])
    (columns : Fin w → Fin (leafCount widths) → R) : R[X] :=
  runArithmetic widths (C ξ) X (formatMask (C ξ) X randomness) (C syndrome)
    (fun i => C (gamma i)) selectors (fun i j => C (columns i j))

/-- Verifier arithmetic on the received/evaluated arrays. -/
def verifierArithmetic {w lambda : Nat} (widths : List Nat) (ξ Δ syndrome : R)
    (gamma : Fin w → R) (selectors : Fin w → Selectors R widths)
    (randomness : Fin (widths.length - 1) → Fin lambda → R)
    (columns : Fin w → Fin (leafCount widths) → R) : R :=
  runArithmetic widths ξ Δ (formatMask ξ Δ randomness) syndrome gamma selectors columns

/-- Prover arithmetic with the flat input arrays of Algorithms 13 and 19. -/
noncomputable def proverArithmeticFlat {w lambda : Nat} (widths : List Nat) (ξ syndrome : R)
    (gamma : Fin w → R) (witness : Fin (selectorCount widths * w) → R[X])
    (randomness : Fin (lambda * (widths.length - 1)) → R[X])
    (columns : Fin w → Fin (leafCount widths) → R) : R[X] :=
  proverArithmetic widths ξ syndrome gamma (formatWitness widths witness)
    (formatRandomness randomness) columns

/-- Verifier arithmetic with the flat evaluation arrays of Algorithms 14 and 20. -/
def verifierArithmeticFlat {w lambda : Nat} (widths : List Nat) (ξ Δ syndrome : R)
    (gamma : Fin w → R) (witness : Fin (selectorCount widths * w) → R)
    (randomness : Fin (lambda * (widths.length - 1)) → R)
    (columns : Fin w → Fin (leafCount widths) → R) : R :=
  verifierArithmetic widths ξ Δ syndrome gamma (formatWitness widths witness)
    (formatRandomness randomness) columns

end SDitH.Spec.PIOPArithmetic
