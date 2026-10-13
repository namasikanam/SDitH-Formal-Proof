import SDitH.Spec.ScaledWitness
import SDitH.Spec.PIOPComposition
import SDitH.Spec.DetailedPIOPChallenges
import SDitH.Spec.SDReduction

/-! The arithmetic modification outlined in §6.1, printed p. 45: multiply
each chunk's mux output by its witness value and retain the other arithmetic.
This is not a complete F256 protocol. The amplitude array is separate from
the binary position array, with no invented bit codec or nonzero constraint.
Mask degree and syndrome packing width are explicit and distinct parameters.
In particular, the binary packing width is not silently reused for F256.
The inherited first-default mux convention remains unchanged.
-/

namespace SDitH.Spec.ScaledArithmetic

open Polynomial PIOPArithmetic Batching PIOPComposition ScaledWitness
open scoped BigOperators

/-- A raw candidate permits zero amplitudes. Nonzeroness is a predicate to
check, not a type-level premise imposed on an adversarial witness. -/
noncomputable def rawVector {F : Type*} [Field F] {w m : Nat}
    (positions : Fin w → Fin m) (amplitudes : Fin w → F) : Fin (w * m) → F :=
  fun j => amplitudes (finProdFinEquiv.symm j).1 *
    elementary (positions (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

def runArithmetic {R : Type*} [CommRing R] {w : Nat} (widths : List Nat)
    (xi z mask syndrome : R) (gamma amplitudes : Fin w → R)
    (selectors : Fin w → Selectors R widths)
    (columns : Fin w → Fin (leafCount widths) → R) : R :=
  mask * z - syndrome + ∑ i,
    (scaledMux (amplitudes i) widths (selectors i) (columns i) +
      gamma i * unitaryLayers xi widths (selectors i) 0)

/-- Position parsing and the mask are the actual earlier routines. No
conversion of the extra amplitude bits into these scalar lines is presumed. -/
noncomputable def proverArithmetic {R : Type*} [CommRing R] {w lambda degree : Nat}
    (widths : List Nat) (xi syndrome : R) (gamma : Fin w → R)
    (positions : Fin (selectorCount widths * w) → R[X]) (amplitudes : Fin w → R[X])
    (randomness : Fin (lambda * (degree - 1)) → R[X])
    (columns : Fin w → Fin (leafCount widths) → R) : R[X] :=
  runArithmetic widths (C xi) X
    (formatMask (d := degree) (C xi) X (formatRandomness randomness)) (C syndrome)
    (fun i => C (gamma i)) amplitudes (formatWitness widths positions) (fun i j => C (columns i j))

def verifierArithmetic {R : Type*} [CommRing R] {w lambda degree : Nat}
    (widths : List Nat) (xi delta syndrome : R) (gamma : Fin w → R)
    (positions : Fin (selectorCount widths * w) → R) (amplitudes : Fin w → R)
    (randomness : Fin (lambda * (degree - 1)) → R)
    (columns : Fin w → Fin (leafCount widths) → R) : R :=
  runArithmetic widths xi delta (formatMask (d := degree) xi delta (formatRandomness randomness))
    syndrome gamma amplitudes (formatWitness widths positions) columns

/-- The residual computed by scaled mux selection, without identifying the
literal mux with the source's conflicting omitted-last coordinate encoding. -/
def scaledResidual {K : Type*} [CommRing K] {r k w : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positions : Fin (selectorCount widths * w) → K) (amplitudes : Fin w → K) : Fin r → K :=
  fun row => -y row + ∑ i, scaledMux (amplitudes i) widths (formatWitness widths positions i)
    (chunkColumns widths hsize (systematicLeft H' row) i)

/-- Post-challenge composition, at explicit base-field algebra and packing
boundaries. The source gives no F256 packing basis or scalar/bit parser. -/
noncomputable def proverRun {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
    {r k w lambda packingWidth degree : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r packingWidth) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (randomness : Fin (lambda * (degree - 1)) → F[X]) : F[X] :=
  let output := batchLinearEquations xi gamma H' y
  proverArithmetic widths xi output.2 gammaPrime positions amplitudes randomness
    (chunkColumns widths hsize output.1)

def verifierRun {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
    {r k w lambda packingWidth degree : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi delta : F)
    (gamma : Fin (blockCount r packingWidth) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positions : Fin (selectorCount widths * w) → F) (amplitudes : Fin w → F)
    (randomness : Fin (lambda * (degree - 1)) → F) : F :=
  let output := batchLinearEquations xi gamma H' y
  verifierArithmetic widths xi delta output.2 gammaPrime positions amplitudes randomness
    (chunkColumns widths hsize output.1)

/-- The arithmetic constant-term experiment with fresh independent uniform
batching challenges. Arrays are fixed before sampling. This is a sampling
model, not an assertion about concrete XOF output or a full F256 protocol. -/
noncomputable def constantExperiment {K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] [Fintype F] [Nontrivial F]
    {r k w lambda packingWidth degree : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (randomness : Fin (lambda * (degree - 1)) → F[X]) : PMF Bool :=
  (PMF.uniformOfFintype (Fin (blockCount r packingWidth) → F)).bind fun gamma =>
    UniformChallenges.eventOutcome (PMF.uniformOfFintype (Fin w → F)) fun gammaPrime =>
      (proverRun widths hsize xi gamma gammaPrime H' y positions amplitudes randomness).eval 0 = 0

/-- Delimited consistent-evaluation comparison for the outlined arithmetic.
The response may depend on both batching challenges, but is chosen before
the fresh evaluation sample. This does not specify the omitted F256 commitment,
scalar parser, coefficient hash, grinding, or signature-security game. -/
noncomputable def comparisonExperiment {K F : Type*}
    [CommRing K] [Field F] [Algebra K F] [Fintype F]
    {r k w lambda packingWidth degree : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (positions : Fin (selectorCount widths * w) → F[X]) (amplitudes : Fin w → F[X])
    (randomness : Fin (lambda * (degree - 1)) → F[X])
    (response : DetailedPIOPChallenges.Challenges F r w packingWidth → PMF F[X])
    (sample : Finset F) (hne : sample.Nonempty) : PMF Bool :=
  (DetailedPIOPChallenges.batchingChallenges F r w packingWidth).bind fun challenges =>
    (response challenges).bind fun answer =>
      UniformChallenges.eventOutcome (PMF.uniformOfFinset sample hne) fun delta =>
        answer.eval 0 = 0 ∧ answer.eval delta =
          verifierRun widths hsize xi delta challenges.1 challenges.2 H' y
            (fun i => (positions i).eval delta) (fun i => (amplitudes i).eval delta)
            (fun i => (randomness i).eval delta)

end SDitH.Spec.ScaledArithmetic
