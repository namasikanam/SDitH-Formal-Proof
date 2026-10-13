import Mathlib.Probability.Distributions.Uniform
import Mathlib.LinearAlgebra.Pi

/-! The uniform verifier-challenge model in §2.1, printed pp. 3–4, and the
linear batching discussion on printed p. 34. These are explicit sampling
definitions, not assumptions that concrete hash/XOF outputs have this law.
Event parameters are fixed before the sample described by each definition.
-/

namespace SDitH.Spec.UniformChallenges

open scoped BigOperators ENNReal

noncomputable section

def probability {A : Type*} [Fintype A] [Nonempty A] (event : A → Prop) : ℝ≥0∞ :=
  (PMF.uniformOfFintype A).toOuterMeasure {a | event a}

def subsetProbability {A : Type*} (sample : Finset A) (hne : sample.Nonempty)
    (event : A → Prop) : ℝ≥0∞ :=
  (PMF.uniformOfFinset sample hne).toOuterMeasure {a | event a}

/-- Record whether a sampled value satisfies an event. -/
def eventOutcome {A : Type*} (p : PMF A) (event : A → Prop) : PMF Bool :=
  p.map (fun a => @decide (event a) (Classical.propDecidable _))

/-- The coefficient dot product in equation (3) and in γᵀ Φ(v). -/
def linearBatch {I F : Type*} [Fintype I] [CommRing F] (values gamma : I → F) : F :=
  ∑ i, gamma i * values i

end
end SDitH.Spec.UniformChallenges
