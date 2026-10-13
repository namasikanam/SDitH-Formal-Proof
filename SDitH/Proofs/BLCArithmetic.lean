import SDitH.Spec.BLCArithmetic
import SDitH.Proofs.GrayCode
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

namespace SDitH.Proofs.BLC

open Spec.BLC
open scoped BigOperators

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

theorem foldl_acc {N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin N → Fin ell → K) (indices : List (Fin N))
    (initial : Folded K ell kappa) (c : Fin ell) :
    (indices.foldl (foldStep phi random) initial).acc c =
      initial.acc c + (indices.map (fun i => random i c)).sum := by
  induction indices generalizing initial with
  | nil => simp
  | cons i tail ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, foldStep]
    ring

theorem foldl_base {N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin N → Fin ell → K) (indices : List (Fin N))
    (initial : Folded K ell kappa) (c : Fin ell) (j : Fin kappa) :
    (indices.foldl (foldStep phi random) initial).base c j =
      initial.base c j + (indices.map (fun i => random i c * phi i j)).sum := by
  induction indices generalizing initial with
  | nil => simp
  | cons i tail ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, foldStep]
    ring

theorem fold_acc_formula {N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin N → Fin ell → K) (c : Fin ell) :
    (foldExecution phi random).acc c = ∑ i, random i c := by
  simp [foldExecution, foldl_acc, List.map_ofFn, List.sum_ofFn]

theorem fold_base_formula {N ell kappa : Nat} (phi : Fin N → Fin kappa → K)
    (random : Fin N → Fin ell → K) (c : Fin ell) (j : Fin kappa) :
    (foldExecution phi random).base c j = ∑ i, random i c * phi i j := by
  simp [foldExecution, foldl_base, List.map_ofFn, List.sum_ofFn]

omit [CommRing K] in
theorem folded_ext {ell kappa : Nat} {a b : Folded K ell kappa}
    (ha : a.acc = b.acc) (hb : a.base = b.base) : a = b := by
  cases a
  cases b
  simp_all

/-- The optimized and direct source folds agree, including the initialization,
all N inputs, every output coordinate, and the explicit zero boundary. -/
theorem optimizedFoldExecution_eq {N ell kappa : Nat}
    (phi : Fin N → Fin kappa → K) (random : Fin N → Fin ell → K) :
    optimizedFoldExecution phi random = foldExecution phi random := by
  apply folded_ext
  · funext c
    simp only [optimizedFoldExecution]
    rw [GrayCode.prefixAcc_formula, fold_acc_formula, ← Fin.sum_univ_eq_sum_range]
    simp [Spec.GrayCode.extendZero]
  · funext c j
    simp only [optimizedFoldExecution]
    rw [GrayCode.differenceFold_eq_direct _ _ N (by simp [Spec.GrayCode.extendZero]),
      fold_base_formula, ← Fin.sum_univ_eq_sum_range]
    simp [Spec.GrayCode.extendZero]

theorem correction_zero {tau N ell kappa : Nat} [NeZero tau]
    (phi : Fin N → Fin kappa → K) (random : Fin tau → Fin N → Fin ell → K) :
    correction phi random 0 = 0 := by
  simp [correction, commonAcc]

theorem psi_formula {tau kappa : Nat} (xi : F) (v : Fin tau → Fin kappa → K) :
    psi xi v = ∑ e, ∑ j, algebraMap K F (v e j) * xi ^ (e.val * kappa + j.val) := by
  simp [psi, LinearMap.sum_apply, LinearMap.smulRight_apply, Algebra.smul_def]

/-- The linearity needed for VOLE merging is proved from the explicit psi map. -/
theorem psi_common_line {tau kappa : Nat} (xi : F) (u : K)
    (delta V : Fin tau → Fin kappa → K) :
    psi xi (fun e j => u * delta e j + V e j) =
      algebraMap K F u * psi xi delta + psi xi V := by
  change psi xi (u • delta + V) = _
  rw [map_add, map_smul, Algebra.smul_def]

/-- Corrected evaluation equals u*phi(hidden)+base in characteristic two.
The omitted summand is proved zero; no BAVC reconstruction contract is assumed. -/
theorem correctedOpening_formula [CharP K 2] {tau N ell kappa : Nat} [NeZero tau]
    (phi : Fin N → Fin kappa → K) (random : Fin tau → Fin N → Fin ell → K)
    (hidden : Fin tau → Fin N) (c : Fin ell) (e : Fin tau) (j : Fin kappa) :
    correctedOpening phi random hidden c e j =
      commonAcc phi random c * challengeRow phi hidden e j + baseRow phi random c e j := by
  have hs : (∑ i ∈ Finset.univ.erase (hidden e),
      random e i c * (phi (hidden e) j - phi i j)) =
      ∑ i, random e i c * (phi (hidden e) j - phi i j) := by simp
  simp only [correctedOpening, hs, correction, Pi.sub_apply, challengeRow, baseRow,
    foldExecutions, fold_acc_formula, fold_base_formula]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [CharTwo.sub_eq_add]
  have hneg (a : K) : -a = a := CharTwo.neg_eq a
  simp only [sub_eq_add_neg, hneg]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- The complete merged opening identity for the displayed phi-based challenge. -/
theorem mergedOpening_formula [CharP K 2] {tau N ell kappa : Nat} [NeZero tau]
    (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (hidden : Fin tau → Fin N) (c : Fin ell) :
    psi xi (correctedOpening phi random hidden c) =
      algebraMap K F (commonAcc phi random c) * psi xi (challengeRow phi hidden) +
        psi xi (baseRow phi random c) := by
  have he : correctedOpening phi random hidden c =
      fun e j => commonAcc phi random c * challengeRow phi hidden e j + baseRow phi random c e j := by
    funext e j
    exact correctedOpening_formula phi random hidden c e j
  rw [he, psi_common_line]

/-- Consistency-check base recovery for each execution/bit column. This uses
the actual [I | M] matrix, and does not claim consistency-check soundness. -/
theorem recoverConsistencyBase_eq {s payload tau kappa : Nat}
    (M : Matrix (Fin s) (Fin payload) K) (u : Fin (s + payload) → K)
    (V : Fin (s + payload) → Fin tau → Fin kappa → K)
    (delta : Fin tau → Fin kappa → K) :
    recoverConsistencyBase M (consistencyCheck M u)
      (fun c e j => u c * delta e j + V c e j) delta = consistencyColumns M V := by
  funext a e j
  simp only [recoverConsistencyBase, consistencyColumns, consistencyCheck,
    Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
  ring

/-- The consistency fields produced by Algorithm 10's arithmetic are recovered
from the displayed corrected openings, with the same blockwise phi challenge. -/
theorem commitArithmetic_consistency [CharP K 2]
    {tau N kappa s wit rnd : Nat} [NeZero tau]
    (xi : F) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K)
    (M : Matrix (Fin s) (Fin (wit + rnd)) K) (witness : Fin wit → K)
    (hidden : Fin tau → Fin N) :
    recoverConsistencyBase M (commitArithmetic xi phi random M witness).plainCheck
      (correctedOpening phi random hidden) (challengeRow phi hidden) =
      (commitArithmetic xi phi random M witness).baseCheck := by
  have he : correctedOpening phi random hidden =
      fun c e j => commonAcc phi random c * challengeRow phi hidden e j + baseRow phi random c e j := by
    funext c e j
    exact correctedOpening_formula phi random hidden c e j
  rw [he]
  exact recoverConsistencyBase_eq M (commonAcc phi random) (baseRow phi random)
    (challengeRow phi hidden)

section FieldEvaluation

variable {E : Type*} [Field E] [Algebra K E]

theorem buildLine_zero (constant : K) (slope : E) :
    (buildLine constant slope).eval 0 = algebraMap K E constant := by
  simp [buildLine]

/-- Reciprocal conversion of one merged coordinate, with an arbitrary explicit
constant correction. Only nonzero delta is required for inversion. -/
theorem reciprocalEvaluation_buildLine (u corr : K) (slope delta : E) (hd : delta ≠ 0) :
    reciprocalEvaluation delta corr (algebraMap K E u * delta + slope) =
      (buildLine (u + corr) slope).eval delta⁻¹ := by
  simp only [reciprocalEvaluation, buildLine, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, map_add]
  field_simp
  ring

/-- Prover witness lines and the displayed recomputation equations agree at the
inverse phi-based challenge. This does not replace the source's raw-index
challenge with phi: connecting that challenge is still a correspondence issue. -/
theorem witness_evaluation [CharP K 2] {tau N ell kappa : Nat} [NeZero tau]
    (xi : E) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (hidden : Fin tau → Fin N)
    (wit : Fin ell → K) (c : Fin ell)
    (hd : psi xi (challengeRow phi hidden) ≠ 0) :
    reciprocalEvaluation (psi xi (challengeRow phi hidden))
      (wit c - commonAcc phi random c) (psi xi (correctedOpening phi random hidden c)) =
      (buildLine (wit c) (psi xi (baseRow phi random c))).eval
        (psi xi (challengeRow phi hidden))⁻¹ := by
  rw [mergedOpening_formula]
  have he := reciprocalEvaluation_buildLine (commonAcc phi random c)
    (wit c - commonAcc phi random c) (psi xi (baseRow phi random c))
    (psi xi (challengeRow phi hidden)) hd
  simpa using he

theorem randomness_evaluation [CharP K 2] {tau N ell kappa : Nat} [NeZero tau]
    (xi : E) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin ell → K) (hidden : Fin tau → Fin N) (c : Fin ell)
    (hd : psi xi (challengeRow phi hidden) ≠ 0) :
    reciprocalEvaluation (psi xi (challengeRow phi hidden)) (0 : K)
      (psi xi (correctedOpening phi random hidden c)) =
      (buildLine (commonAcc phi random c) (psi xi (baseRow phi random c))).eval
        (psi xi (challengeRow phi hidden))⁻¹ := by
  rw [mergedOpening_formula]
  simpa using reciprocalEvaluation_buildLine (commonAcc phi random c) 0
    (psi xi (baseRow phi random c)) (psi xi (challengeRow phi hidden)) hd

/-- Integrated line agreement, including the source's mask/witness/randomness
slices and the actually computed witness correction. This is the algebraic BLC
body, conditional on a nonzero phi-based challenge and the displayed openings. -/
theorem commitArithmetic_evaluations [CharP K 2]
    {tau N kappa s wit rnd : Nat} [NeZero tau]
    (xi : E) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K)
    (M : Matrix (Fin s) (Fin (wit + rnd)) K) (witness : Fin wit → K)
    (hidden : Fin tau → Fin N) (hd : psi xi (challengeRow phi hidden) ≠ 0) :
    (∀ j : Fin wit,
      reciprocalEvaluation (psi xi (challengeRow phi hidden))
        ((commitArithmetic xi phi random M witness).witnessCorrection j)
        (psi xi (correctedOpening phi random hidden (witnessIndex j))) =
      ((commitArithmetic xi phi random M witness).witnessLines j).eval
        (psi xi (challengeRow phi hidden))⁻¹) ∧
    (∀ j : Fin rnd,
      reciprocalEvaluation (psi xi (challengeRow phi hidden)) (0 : K)
        (psi xi (correctedOpening phi random hidden (randomnessIndex j))) =
      ((commitArithmetic xi phi random M witness).randomnessLines j).eval
        (psi xi (challengeRow phi hidden))⁻¹) := by
  constructor
  · intro j
    rw [mergedOpening_formula]
    have he := reciprocalEvaluation_buildLine (commonAcc phi random (witnessIndex j))
      (witness j - commonAcc phi random (witnessIndex j))
      (psi xi (baseRow phi random (witnessIndex j))) (psi xi (challengeRow phi hidden)) hd
    simpa [commitArithmetic] using he
  · intro j
    exact randomness_evaluation xi phi random hidden (randomnessIndex j) hd

theorem commitArithmetic_witness_at_zero {tau N kappa s wit rnd : Nat} [NeZero tau]
    (xi : E) (phi : Fin N → Fin kappa → K)
    (random : Fin tau → Fin N → Fin (s + (wit + rnd)) → K)
    (M : Matrix (Fin s) (Fin (wit + rnd)) K) (witness : Fin wit → K) (j : Fin wit) :
    ((commitArithmetic xi phi random M witness).witnessLines j).eval 0 =
      algebraMap K E (witness j) := by
  exact buildLine_zero _ _

end FieldEvaluation

end SDitH.Proofs.BLC
