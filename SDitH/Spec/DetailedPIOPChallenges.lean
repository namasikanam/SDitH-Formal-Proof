import SDitH.Spec.PIOPComposition

/-! A delimited algebraic comparison experiment for the detailed PIOP of
Algorithms 19/20. Consistent evaluations of the committed polynomials are
supplied by construction. The response polynomial is chosen after the two
batching vectors and before a fresh evaluation point. This does not model
commitment extraction, the coefficient hash check or a full signature game.
Unlike introductory equation (2), Algorithm 20 evaluates the polynomial without
an additional multiplication by delta. The two experiments are kept separate. -/

namespace SDitH.Spec.DetailedPIOPChallenges

open PIOPArithmetic PIOPComposition Batching UniformChallenges Polynomial

noncomputable section

abbrev Challenges (F : Type*) (r w lambda : Nat) :=
  (Fin (blockCount r lambda) → F) × (Fin w → F)

def batchingChallenges (F : Type*) [Fintype F] [Nonempty F] (r w lambda : Nat) :
    PMF (Challenges F r w lambda) :=
  (PMF.uniformOfFintype (Fin (blockCount r lambda) → F)).bind fun gamma =>
    (PMF.uniformOfFintype (Fin w → F)).map fun gammaPrime => (gamma, gammaPrime)

def comparisonExperiment {K F : Type*} [CommRing K] [Field F] [Algebra K F] [Fintype F]
    {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (H' : Matrix (Fin r) (Fin k) K) (y : Fin r → K)
    (witness : Fin (selectorCount widths * w) → F[X])
    (randomness : Fin (lambda * (widths.length - 1)) → F[X])
    (response : Challenges F r w lambda → PMF F[X])
    (sample : Finset F) (hne : sample.Nonempty) : PMF Bool :=
  (batchingChallenges F r w lambda).bind fun challenges =>
    (response challenges).bind fun answer =>
      eventOutcome (PMF.uniformOfFinset sample hne) fun delta =>
        answer.eval 0 = 0 ∧ answer.eval delta =
          verifierRun widths hsize xi delta challenges.1 challenges.2 H' y
            (fun j => (witness j).eval delta) (fun j => (randomness j).eval delta)

end
end SDitH.Spec.DetailedPIOPChallenges
