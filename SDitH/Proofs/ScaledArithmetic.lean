import SDitH.Spec.ScaledArithmetic
import SDitH.Proofs.ScaledWitness
import SDitH.Proofs.Batching

namespace SDitH.Proofs.ScaledArithmetic

open Polynomial Spec.PIOPArithmetic Spec.Batching Spec.PIOPComposition
open Spec.ScaledWitness Spec.ScaledArithmetic
open scoped BigOperators

theorem rawVector_coordinate {F : Type*} [Field F] {w m : Nat}
    (positions : Fin w → Fin m) (amplitudes : Fin w → F) (i : Fin w) (j : Fin m) :
    rawVector positions amplitudes (finProdFinEquiv (i, j)) =
      amplitudes i * Spec.elementary (positions i) j := by
  simp [rawVector]

theorem vector_eq_rawVector {F : Type*} [Field F] {w m : Nat} (wit : Witness F w m) :
    vector wit = rawVector wit.positions (fun i => (wit.amplitudes i).val) := rfl

/-- Nonzero values are precisely the missing regularity condition; they are
not obtained by giving every raw candidate the type of an honest witness. -/
theorem raw_regular_iff {F : Type*} [Field F] {w m : Nat}
    (positions : Fin w → Fin m) (amplitudes : Fin w → F) :
    Spec.SDReduction.regularFlat (rawVector positions amplitudes) ↔
      ∀ i, amplitudes i ≠ 0 := by
  constructor
  · intro h i hz
    obtain ⟨j, a, ha, hx⟩ := h i
    have he := congrFun hx j
    dsimp only at he
    rw [rawVector_coordinate, hz] at he
    simp [Spec.elementary] at he
    exact ha he.symm
  · intro ha
    exact ScaledWitness.vector_regular ⟨positions, fun i => ⟨amplitudes i, ha i⟩⟩

theorem rawVector_zero {F : Type*} [Field F] {w m : Nat}
    (positions : Fin w → Fin m) : rawVector positions (fun _ => (0 : F)) = 0 := by
  funext j
  simp [rawVector]

theorem zero_amplitudes_not_regular {F : Type*} [Field F] {w m : Nat}
    (hw : 0 < w) (positions : Fin w → Fin m) :
    ¬ Spec.SDReduction.regularFlat (rawVector positions (fun _ => (0 : F))) := by
  intro h
  exact (raw_regular_iff positions (fun _ => (0 : F))).mp h ⟨0, hw⟩ rfl

theorem map_runArithmetic {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {w : Nat} (widths : List Nat)
    (xi z mask syndrome : R) (gamma amplitudes : Fin w → R)
    (selectors : Fin w → Selectors R widths)
    (columns : Fin w → Fin (leafCount widths) → R) :
    f (Spec.ScaledArithmetic.runArithmetic widths xi z mask syndrome gamma amplitudes
      selectors columns) =
    Spec.ScaledArithmetic.runArithmetic widths (f xi) (f z) (f mask) (f syndrome)
      (fun i => f (gamma i)) (fun i => f (amplitudes i))
      (fun i => mapSelectors f widths (selectors i)) (fun i j => f (columns i j)) := by
  simp [Spec.ScaledArithmetic.runArithmetic, scaledMux, map_sum,
    PIOPArithmetic.map_muxTree, PIOPArithmetic.map_unitaryLayers]

/-- Evaluation commutes with the actual flat position/randomness parsers,
the scaled mux trees and every retained unitary check. -/
theorem verifier_evaluates_prover {R : Type*} [CommRing R] {w lambda degree : Nat}
    (widths : List Nat) (xi delta syndrome : R) (gamma : Fin w → R)
    (positions : Fin (selectorCount widths * w) → R[X]) (amplitudes : Fin w → R[X])
    (randomness : Fin (lambda * (degree - 1)) → R[X])
    (columns : Fin w → Fin (leafCount widths) → R) :
    (Spec.ScaledArithmetic.proverArithmetic widths xi syndrome gamma positions amplitudes
      randomness columns).eval delta =
    Spec.ScaledArithmetic.verifierArithmetic widths xi delta syndrome gamma
      (fun i => (positions i).eval delta) (fun i => (amplitudes i).eval delta)
      (fun i => (randomness i).eval delta) columns := by
  unfold Spec.ScaledArithmetic.proverArithmetic Spec.ScaledArithmetic.verifierArithmetic
  change (evalRingHom delta) _ = _
  rw [map_runArithmetic]
  simp only [PIOPArithmetic.map_formatMask, coe_evalRingHom, eval_C, eval_X,
    PIOPArithmetic.map_formatWitness]
  rfl

theorem verifierRun_evaluates_proverRun {K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F]
    {r k w lambda packingWidth degree : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi delta : F)
    (gamma : Fin (blockCount r packingWidth) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (randomness : Fin (lambda * (degree - 1)) → F[X]) :
    (Spec.ScaledArithmetic.proverRun widths hsize xi gamma gammaPrime H' y positions
      amplitudes randomness).eval delta =
    Spec.ScaledArithmetic.verifierRun widths hsize xi delta gamma gammaPrime H' y
      (fun i => (positions i).eval delta) (fun i => (amplitudes i).eval delta)
      (fun i => (randomness i).eval delta) :=
  verifier_evaluates_prover widths xi delta _ gammaPrime positions amplitudes randomness _

/-- The extra amplitude line raises the mux degree by one. Mask degree is
kept independent of the number of selector layers. -/
theorem proverArithmetic_degree {F : Type*} [Field F] {w lambda degree : Nat}
    (widths : List Nat) (hd : 2 ≤ degree) (hlength : widths.length + 1 ≤ degree)
    (xi syndrome : F) (gamma : Fin w → F)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (randomness : Fin (lambda * (degree - 1)) → F[X])
    (columns : Fin w → Fin (leafCount widths) → F)
    (hp : ∀ i, (positions i).natDegree ≤ 1) (ha : ∀ i, (amplitudes i).natDegree ≤ 1)
    (hr : ∀ i, (randomness i).natDegree ≤ 1) :
    (Spec.ScaledArithmetic.proverArithmetic widths xi syndrome gamma positions amplitudes
      randomness columns).natDegree ≤ degree := by
  unfold Spec.ScaledArithmetic.proverArithmetic Spec.ScaledArithmetic.runArithmetic
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · have hm := PIOPDegree.formatMask_degree hd xi (formatRandomness randomness)
        (fun i j => hr (blockIndex i j))
      have hx : (X : F[X]).natDegree ≤ 1 := by simp
      exact (Polynomial.natDegree_mul_le_of_le hm hx).trans (by omega)
    · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (ScaledWitness.scaledMux_degree (amplitudes i) widths
        (formatWitness widths positions i) (columns i) (ha i)
        (PIOPDegree.formatWitness_linear widths positions hp i)).trans hlength
    · have hu := (PIOPDegree.unitaryLayers_degree xi widths
        (formatWitness widths positions i) 0
        (PIOPDegree.formatWitness_linear widths positions hp i)).trans hd
      have hc : (C (gamma i)).natDegree ≤ 0 := by simp
      simpa using Polynomial.natDegree_mul_le_of_le hc hu

theorem proverRun_degree {K F : Type*} [CommRing K] [Field F] [Algebra K F]
    {r k w lambda packingWidth degree : Nat} (widths : List Nat)
    (hd : 2 ≤ degree) (hlength : widths.length + 1 ≤ degree)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r packingWidth) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (randomness : Fin (lambda * (degree - 1)) → F[X])
    (hp : ∀ i, (positions i).natDegree ≤ 1) (ha : ∀ i, (amplitudes i).natDegree ≤ 1)
    (hr : ∀ i, (randomness i).natDegree ≤ 1) :
    (Spec.ScaledArithmetic.proverRun widths hsize xi gamma gammaPrime H' y positions
      amplitudes randomness).natDegree ≤ degree :=
  proverArithmetic_degree widths hd hlength xi _ gammaPrime positions amplitudes randomness
    _ hp ha hr

/-- The retained Algorithm-21 batching commutes with scaled mux selection.
No identification of the conflicting position encodings is assumed. -/
theorem batch_scaled_residual {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
    {r k w packingWidth : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r packingWidth) → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positions : Fin (selectorCount widths * w) → K) (amplitudes : Fin w → K) :
    batchLinearMap xi gamma (scaledResidual widths hsize H' y positions amplitudes) =
      -(batchLinearEquations xi gamma H' y).2 + ∑ i,
        scaledMux (algebraMap K F (amplitudes i)) widths
          (mapSelectors (algebraMap K F) widths (formatWitness widths positions i))
          (chunkColumns widths hsize (batchLinearEquations xi gamma H' y).1 i) := by
  have he : scaledResidual widths hsize H' y positions amplitudes =
      -y + ∑ i, (fun row => scaledMux (amplitudes i) widths (formatWitness widths positions i)
        (chunkColumns widths hsize (systematicLeft H' row) i)) := by
    funext row
    simp [scaledResidual, Finset.sum_apply]
  rw [he, map_add, map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact ScaledWitness.batch_scaledMux (batchLinearMap xi gamma) (amplitudes i) widths
    (formatWitness widths positions i)
    (fun col row => chunkColumns widths hsize (systematicLeft H' row) i col)

theorem unitaryLayers_zero_selectors {R : Type*} [CommRing R]
    (xi : R) (widths : List Nat) (layer : Nat) :
    unitaryLayers xi widths (parseSelectors widths (fun _ => 0)) layer = 0 := by
  induction widths generalizing layer with
  | nil => rfl
  | cons r rest ih => simp [parseSelectors, unitaryLayers, unitaryCheck, ih]

theorem run_zero_eq_affine {R : Type*} [CommRing R] {w : Nat} (widths : List Nat)
    (xi mask syndrome : R) (gamma amplitudes : Fin w → R)
    (selectors : Fin w → Selectors R widths)
    (columns : Fin w → Fin (leafCount widths) → R) :
    Spec.ScaledArithmetic.runArithmetic widths xi 0 mask syndrome gamma amplitudes
      selectors columns =
      (-syndrome + ∑ i, scaledMux (amplitudes i) widths (selectors i) (columns i)) +
        Spec.UniformChallenges.linearBatch
          (fun i => unitaryLayers xi widths (selectors i) 0) gamma := by
  simp [Spec.ScaledArithmetic.runArithmetic, Spec.UniformChallenges.linearBatch,
    Finset.sum_add_distrib, add_assoc]

/-- The constant term is the actual batch of the scaled residual plus the
actual unitary batch. Constants of both position and amplitude lines are
related explicitly to their base-field values. -/
theorem constant_eq_batches {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
    {r k w lambda packingWidth degree : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r packingWidth) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positionValues : Fin (selectorCount widths * w) → K) (amplitudeValues : Fin w → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (hp : ∀ i, (positions i).eval 0 = algebraMap K F (positionValues i))
    (ha : ∀ i, (amplitudes i).eval 0 = algebraMap K F (amplitudeValues i))
    (randomness : Fin (lambda * (degree - 1)) → F[X]) :
    (Spec.ScaledArithmetic.proverRun widths hsize xi gamma gammaPrime H' y positions
      amplitudes randomness).eval 0 =
      batchLinearMap xi gamma (scaledResidual widths hsize H' y positionValues amplitudeValues) +
        Spec.UniformChallenges.linearBatch (fun i => unitaryLayers xi widths
          (mapSelectors (algebraMap K F) widths (formatWitness widths positionValues i)) 0)
          gammaPrime := by
  rw [verifierRun_evaluates_proverRun]
  simp_rw [hp, ha]
  unfold Spec.ScaledArithmetic.verifierRun Spec.ScaledArithmetic.verifierArithmetic
  rw [← PIOPArithmetic.map_formatWitness, run_zero_eq_affine, batch_scaled_residual]

/-- All-zero raw values, selectors and masks satisfy the described arithmetic
for zero syndrome, independently of the matrix. This is an arithmetic boundary,
not a claim about an unspecified complete F256 signature verifier. -/
theorem proverArithmetic_zero {R : Type*} [CommRing R] {w lambda degree : Nat}
    (widths : List Nat) (xi : R) (gamma : Fin w → R)
    (columns : Fin w → Fin (leafCount widths) → R) :
    Spec.ScaledArithmetic.proverArithmetic (lambda := lambda) (degree := degree) widths xi 0
      gamma (fun _ => 0) (fun _ => 0) (fun _ => 0) columns = 0 := by
  simp [Spec.ScaledArithmetic.proverArithmetic, Spec.ScaledArithmetic.runArithmetic,
    scaledMux, formatWitness, unitaryLayers_zero_selectors, formatRandomness, formatMask]

theorem proverRun_zero {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
    {r k w lambda packingWidth degree : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r packingWidth) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) :
    Spec.ScaledArithmetic.proverRun (lambda := lambda) (degree := degree) widths hsize xi
      gamma gammaPrime H' 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) = 0 := by
  unfold Spec.ScaledArithmetic.proverRun
  simp only [batchLinearEquations, map_zero]
  exact proverArithmetic_zero widths xi gammaPrime _

end SDitH.Proofs.ScaledArithmetic
