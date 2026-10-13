import SDitH.Spec.PIOP
import SDitH.Spec.UniformChallenges

/-! Sampling experiments for the literal introductory PIOP. The extra factor
in equation (2) is preserved. The residual below is derived from that equation;
it is not substituted for the different residual printed in its soundness text.
Committed lines and their openings are fixed algebraic data in these experiments.
Commitment binding, adaptive transcript generation and Fiat–Shamir are separate.
-/

namespace SDitH.Spec.PIOPChallenges

open Polynomial PIOP
open scoped ENNReal

variable {F : Type*} [CommRing F] {n m : Nat}

noncomputable def literalResidual (f : Fin m → MvPolynomial (Fin n) F)
    (gamma : Fin m → F) (P : Fin n → F[X]) (P₀ answer : F[X]) : F[X] :=
  answer * X - proverPolynomial f gamma P P₀

noncomputable def sampledLiteralAcceptance (f : Fin m → MvPolynomial (Fin n) F)
    (gamma : Fin m → F) (P : Fin n → F[X]) (P₀ answer : F[X])
    (sample : Finset F) (hne : sample.Nonempty) : ℝ≥0∞ :=
  UniformChallenges.subsetProbability sample hne (fun delta =>
    literalVerifier f gamma answer delta (P₀.eval delta) (fun i => (P i).eval delta))

/-- The two fresh uniform verifier challenges, with a response allowed to
depend on gamma but fixed before delta. Openings are the consistent evaluations
of the fixed committed polynomials. No commitment-security conclusion is built
into this algebraic experiment. -/
noncomputable def literalExperiment [Fintype F] [Nontrivial F]
    (f : Fin m → MvPolynomial (Fin n) F) (P : Fin n → F[X]) (P₀ : F[X])
    (response : (Fin m → F) → F[X]) (sample : Finset F) (hne : sample.Nonempty) : PMF Bool :=
  (PMF.uniformOfFintype (Fin m → F)).bind fun gamma =>
    UniformChallenges.eventOutcome (PMF.uniformOfFinset sample hne) (fun delta =>
      literalVerifier f gamma (response gamma) delta (P₀.eval delta) (fun i => (P i).eval delta))

/-- The same schedule with a randomized response after gamma. -/
noncomputable def randomizedLiteralExperiment [Fintype F] [Nontrivial F]
    (f : Fin m → MvPolynomial (Fin n) F) (P : Fin n → F[X]) (P₀ : F[X])
    (response : (Fin m → F) → PMF F[X]) (sample : Finset F) (hne : sample.Nonempty) : PMF Bool :=
  (PMF.uniformOfFintype (Fin m → F)).bind fun gamma =>
    (response gamma).bind fun answer =>
      UniformChallenges.eventOutcome (PMF.uniformOfFinset sample hne) (fun delta =>
        literalVerifier f gamma answer delta (P₀.eval delta) (fun i => (P i).eval delta))

end SDitH.Spec.PIOPChallenges
