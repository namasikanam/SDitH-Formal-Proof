import SDitH.Spec.BLCSeedLines
import SDitH.Spec.UniformChallenges

/-! The consistency mask [I | M] applied to a fixed vector, and the explicit
uniform-matrix experiment for its kernel. The uniform law is a defined
sampler over all binary matrices; it is not a claim about the concrete XOF
expansion of Algorithm 10/12, whose correspondence is a separate obligation. -/

namespace SDitH.Spec.ConsistencyMatrix

open scoped ENNReal

variable {K : Type*} [CommRing K] {s payload : Nat}

/-- [I | M] applied to a vector of length s+payload. -/
def masked (M : Matrix (Fin s) (Fin payload) K) (d : Fin (s + payload) → K) (a : Fin s) : K :=
  ∑ c, Batching.systematicLeft M a c * d c

def top (d : Fin (s + payload) → K) : Fin s → K := fun a => d (Fin.castAdd payload a)

def bottom (d : Fin (s + payload) → K) : Fin payload → K := fun b => d (Fin.natAdd s b)

/-- Probability, over a uniformly sampled mask, that a fixed vector is annihilated. -/
noncomputable def kernelProbability [Fintype K] (d : Fin (s + payload) → K) : ℝ≥0∞ :=
  UniformChallenges.probability (fun M : Matrix (Fin s) (Fin payload) K => ∀ a, masked M d a = 0)

/-- Probability, over a uniformly sampled mask, that two fixed vectors have
the same masked image, as the two-challenge identity requires of two
executions' slopes against one plain check. -/
noncomputable def equalMaskProbability [Fintype K] (x y : Fin (s + payload) → K) : ℝ≥0∞ :=
  UniformChallenges.probability (fun M : Matrix (Fin s) (Fin payload) K => ∀ a, masked M x a = masked M y a)

end SDitH.Spec.ConsistencyMatrix
