import SDitH.Spec.PIOPArithmetic
import SDitH.Spec.Batching
import SDitH.Spec.UniformChallenges

/-! Algorithms 19/20 after challenge expansion, including Algorithm 21 and
the actual flat witness/randomness formatting routines. The required matrix
column/chunk-size equality is an explicit typing premise; it is false for
Table 3 and must not be supplied by an assumption about the submitted rows.

The optional PMF experiment below samples fresh independent uniform challenge
vectors. It does not identify that model with ExpandBatchingChallenge's XOF.
-/

namespace SDitH.Spec.PIOPComposition

open PIOPArithmetic Batching UniformChallenges Polynomial
open scoped BigOperators

noncomputable section

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

/-- Increasing chunks and increasing columns within a chunk, as in the
interval h[i*m .. (i+1)*m-1] passed to the mux routine. -/
def chunkColumns {r k w : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (columns : Fin (r + k) → F) :
    Fin w → Fin (leafCount widths) → F :=
  fun i j => columns (Fin.cast hsize (blockIndex i j))

/-- The syndrome residual actually selected by the printed mux recurrence.
This definition does not identify that recurrence with the submission's
conflicting omitted-last-coordinate witness interpretation. -/
def muxSyndromeResidual {r k w : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (bits : Fin (selectorCount widths * w) → K) : Fin r → K :=
  fun row => -y row + ∑ i, muxTree widths (formatWitness widths bits i)
    (chunkColumns widths hsize (systematicLeft H' row) i)

/-- Entire post-challenge Algorithm 19 computation, including Algorithm 21.
The transcript/hash inputs remain at the challenge-expansion boundary. -/
def proverRun {r k w lambda : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F[X])
    (randomness : Fin (lambda * (widths.length - 1)) → F[X]) : F[X] :=
  let output := batchLinearEquations xi gamma H' y
  proverArithmeticFlat widths xi output.2 gammaPrime witness randomness
    (chunkColumns widths hsize output.1)

/-- Entire post-challenge Algorithm 20 computation, using the same literal
systematic matrix orientation and chunk indexing as proverRun. -/
def verifierRun {r k w lambda : Nat} (widths : List Nat)
    (hsize : leafCount widths * w = r + k) (xi delta : F)
    (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F)
    (randomness : Fin (lambda * (widths.length - 1)) → F) : F :=
  let output := batchLinearEquations xi gamma H' y
  verifierArithmeticFlat widths xi delta output.2 gammaPrime witness randomness
    (chunkColumns widths hsize output.1)

/-- A literal post-challenge constant-term experiment. Both polynomial arrays
are fixed before sampling, gamma is drawn first, then gamma-prime independently.
Acceptance here means only that the computed constant term is zero. -/
def constantExperiment [Fintype F] [Nontrivial F] {r k w lambda : Nat}
    (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F[X])
    (randomness : Fin (lambda * (widths.length - 1)) → F[X]) : PMF Bool :=
  (PMF.uniformOfFintype (Fin (blockCount r lambda) → F)).bind fun gamma =>
    eventOutcome (PMF.uniformOfFintype (Fin w → F)) fun gammaPrime =>
      (proverRun widths hsize xi gamma gammaPrime H' y witness randomness).eval 0 = 0

end
end SDitH.Spec.PIOPComposition
