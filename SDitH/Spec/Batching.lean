import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Matrix.Mul

/-!
Equation (7), equation (9), and Algorithm 21, printed pp. 34 and 37.

`K` is the syndrome field and `F` its extension. In the main variant `K = ZMod 2`.
These generic formulas assume no injectivity. Their concrete specialization in
the exact Table-2 quotient rings is proved in `Proofs/ConcreteEncodings.lean`;
field irreducibility and byte-representation integration remain separate.
-/

namespace SDitH.Spec.Batching

open scoped BigOperators

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

/-- Number of length-lambda blocks, including a final partially padded block.
The intended uses require `0 < lambda`; this natural-number formula is total. -/
def blockCount (r lambda : Nat) : Nat := (r + lambda - 1) / lambda

/-- One block of the embedding Φ, as an actual linear map. Out-of-range
coordinates of the final block contribute zero, exactly as in equation (7). -/
def packBlockLinear {r lambda : Nat} (ξ : F) (block : Fin (blockCount r lambda)) :
    (Fin r → K) →ₗ[K] F :=
  ∑ j : Fin lambda,
    if h : block.val * lambda + j.val < r then
      (LinearMap.proj (R := K) (φ := fun _ : Fin r => K)
        ⟨block.val * lambda + j.val, h⟩).smulRight (ξ ^ j.val)
    else 0

/-- The block-wise map Φ in equation (7). -/
def packVector {r lambda : Nat} (ξ : F) (v : Fin r → K) :
    Fin (blockCount r lambda) → F :=
  fun block => packBlockLinear ξ block v

/-- The scalar `γᵀ Φ(v)` in equations (8)–(9). Its linearity follows from its
construction, rather than an assumed property of an opaque batching routine. -/
def batchLinearMap {r lambda : Nat} (ξ : F) (gamma : Fin (blockCount r lambda) → F) :
    (Fin r → K) →ₗ[K] F :=
  ∑ block, gamma block • packBlockLinear ξ block

/-- Algorithm 21's explicitly printed orientation `[I | H′]`.
The prose elsewhere also uses `[H′ | I]`; that conflict is not identified away. -/
def systematicLeft {r k : Nat} (H' : Matrix (Fin r) (Fin k) K) :
    Matrix (Fin r) (Fin (r + k)) K :=
  fun row => Fin.addCases (fun col => if row = col then 1 else 0) (H' row)

/-- Algorithm 21, given its already-expanded batching challenge and the field
representation used in equation (7). The result contains every batched matrix
column and the batched syndrome. -/
def batchLinearEquations {r k lambda : Nat} (ξ : F)
    (gamma : Fin (blockCount r lambda) → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K) :
    (Fin (r + k) → F) × F :=
  (fun col => batchLinearMap ξ gamma (fun row => systematicLeft H' row col),
    batchLinearMap ξ gamma y)

end SDitH.Spec.Batching
