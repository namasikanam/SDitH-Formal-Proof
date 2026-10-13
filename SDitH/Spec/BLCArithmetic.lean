import SDitH.Spec.Batching
import SDitH.Spec.GrayCode
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.OfFn

/-!
The BLC arithmetic of printed pp. 25–30. Algorithm 10's folding loop, correction,
`[I | M]` consistency orientation, and line construction are explicit. The opening
equations are those displayed on pp. 27–29; they do not silently fix Algorithm
12's `reval`/`rshare`, undefined `phi_mu`, or raw-index/Gray challenge issues.

The input random table consists of already expanded PRG field elements. No
distribution or correctness property of the PRG, BAVC, or hash is assumed here.
-/

namespace SDitH.Spec.BLC

open scoped BigOperators

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

structure Folded (K : Type*) (ell kappa : Nat) where
  acc : Fin ell → K
  base : Fin ell → Fin kappa → K

def foldStep {N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin N → Fin ell → K) (state : Folded K ell kappa) (i : Fin N) :
    Folded K ell kappa :=
  { acc := fun c => state.acc c + random i c
    base := fun c j => state.base c j + random i c * phi i j }

/-- Algorithm 10 lines 3–9, initialized to zero and folded in increasing order. -/
def foldExecution {N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin N → Fin ell → K) : Folded K ell kappa :=
  (List.ofFn id).foldl (foldStep phi random) ⟨0, 0⟩

/-- The prefix-fold optimization from equations (4)–(5), with the boundary row
explicitly zero. Its equality to foldExecution is proved for every input array. -/
def optimizedFoldExecution {N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin N → Fin ell → K) : Folded K ell kappa :=
  { acc := fun c => GrayCode.prefixAcc (GrayCode.extendZero (fun i => random i c)) N
    base := fun c j => GrayCode.differenceFold
      (GrayCode.extendZero (fun i => random i c)) (GrayCode.extendZero (fun i => phi i j)) N }

def foldExecutions {tau N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) : Fin tau → Folded K ell kappa :=
  fun e => foldExecution phi (random e)

/-- Algorithm 10 line 12. NeZero tau records the source's positive execution count. -/
def commonAcc {tau N ell kappa : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) : Fin ell → K :=
  (foldExecutions phi random 0).acc

/-- Algorithm 10 line 11, extended by zero at execution 0. Only positive
execution indices are transmitted; zero-extension is proved in the proof module. -/
def correction {tau N ell kappa : Nat} [NeZero tau] (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (e : Fin tau) : Fin ell → K :=
  commonAcc phi random - (foldExecutions phi random e).acc

/-- A row of the concatenation V = [rbase[0], ..., rbase[tau-1]], line 13. -/
def baseRow {tau N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (c : Fin ell) :
    Fin tau → Fin kappa → K :=
  fun e j => (foldExecutions phi random e).base c j

/-- The displayed psi map, with coordinate e*kappa+j in the row concatenation.
This is a constructed linear map; injectivity/power-basis independence is not
an assumption in its type. -/
def psi {tau kappa : Nat} (xi : F) : (Fin tau → Fin kappa → K) →ₗ[K] F :=
  ∑ e : Fin tau, ∑ j : Fin kappa,
    ((LinearMap.proj (R := K) (φ := fun _ : Fin kappa => K) j).comp
      (LinearMap.proj (R := K) (φ := fun _ : Fin tau => Fin kappa → K) e)).smulRight
        (xi ^ (e.val * kappa + j.val))

def challengeRow {tau N kappa : Nat} (phi : Fin N → Fin kappa → K)
    (hidden : Fin tau → Fin N) : Fin tau → Fin kappa → K :=
  fun e j => phi (hidden e) j

/-- The displayed opening sum and auxiliary correction on printed p. 27.
This function uses the actual phi values, not the unresolved raw-index encoding. -/
def correctedOpening {tau N ell kappa : Nat} [NeZero tau]
    (phi : Fin N → Fin kappa → K) (random : Fin tau → Fin N → Fin ell → K)
    (hidden : Fin tau → Fin N) (c : Fin ell) : Fin tau → Fin kappa → K :=
  fun e j =>
    (∑ i ∈ Finset.univ.erase (hidden e), random e i c * (phi (hidden e) j - phi i j)) +
      correction phi random e c * phi (hidden e) j

/-- Algorithms 10/12 explicitly use [I | M]. Rows are consistency coordinates,
followed by payload coordinates, matching their line-construction slicing. -/
def consistencyCheck {s payload : Nat} (M : Matrix (Fin s) (Fin payload) K)
    (u : Fin (s + payload) → K) : Fin s → K :=
  (Batching.systematicLeft M).mulVec u

def consistencyColumns {s payload tau kappa : Nat} (M : Matrix (Fin s) (Fin payload) K)
    (V : Fin (s + payload) → Fin tau → Fin kappa → K) : Fin s → Fin tau → Fin kappa → K :=
  fun a e j => ∑ c, Batching.systematicLeft M a c * V c e j

def recoverConsistencyBase {s payload tau kappa : Nat}
    (M : Matrix (Fin s) (Fin payload) K) (plain : Fin s → K)
    (Q : Fin (s + payload) → Fin tau → Fin kappa → K)
    (delta : Fin tau → Fin kappa → K) : Fin s → Fin tau → Fin kappa → K :=
  fun a e j => consistencyColumns M Q a e j - plain a * delta e j

/-- Algorithm 10 lines 22–23. The caller selects the witness or randomness
constant; the slope is the psi-encoded corresponding row of V. -/
noncomputable def buildLine (constant : K) (slope : F) : Polynomial F :=
  Polynomial.C (algebraMap K F constant) + Polynomial.C slope * Polynomial.X

/-- Algorithm 12 lines 24–25 / displayed reciprocal equations, where delta is
the nonzero merged challenge before inversion, and correction is zero for rnd. -/
def reciprocalEvaluation [Inv F] (delta : F) (corr : K) (mergedOpening : F) : F :=
  algebraMap K F corr + delta⁻¹ * mergedOpening

/-- The consistency-mask coordinates precede witness and randomness, as in
Algorithm 10 lines 18–19. All slices carry their actual array bounds. -/
def witnessIndex {s wit rnd : Nat} (j : Fin wit) : Fin (s + (wit + rnd)) :=
  Fin.natAdd s (Fin.castAdd rnd j)

def randomnessIndex {s wit rnd : Nat} (j : Fin rnd) : Fin (s + (wit + rnd)) :=
  Fin.natAdd s (Fin.natAdd wit j)

structure CommitArithmeticResult (K F : Type*) [CommRing F]
    (tau kappa s wit rnd : Nat) where
  witnessLines : Fin wit → Polynomial F
  randomnessLines : Fin rnd → Polynomial F
  auxiliary : Fin tau → Fin (s + (wit + rnd)) → K
  plainCheck : Fin s → K
  baseCheck : Fin s → Fin tau → Fin kappa → K
  witnessCorrection : Fin wit → K

/-- Algorithm 10's complete arithmetic after the PRG and consistency challenge
are expanded. Hash calls, transcript serialization, and those expansions are
not claimed by this function. s=lambda+B and rnd=(d-1)*lambda in the source. -/
noncomputable def commitArithmetic {tau N kappa s wit rnd : Nat} [NeZero tau]
    (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K)
    (M : Matrix (Fin s) (Fin (wit + rnd)) K) (witness : Fin wit → K) :
    CommitArithmeticResult K F tau kappa s wit rnd :=
  let u := commonAcc phi random
  let V := baseRow phi random
  { witnessLines := fun j => buildLine (witness j) (psi xi (V (witnessIndex j)))
    randomnessLines := fun j =>
      buildLine (u (randomnessIndex j)) (psi xi (V (randomnessIndex j)))
    auxiliary := correction phi random
    plainCheck := consistencyCheck M u
    baseCheck := consistencyColumns M V
    witnessCorrection := fun j => witness j - u (witnessIndex j) }

end SDitH.Spec.BLC
