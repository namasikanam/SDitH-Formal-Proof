import SDitH.Spec.Parameters
import SDitH.Spec.RegularSupport
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! §4.1, printed p. 38: literal dimension formulas and density accounting.
Integer dimensions retain negative or excessive results instead of silently
clamping an ill-formed dimension. The RSD formula contains the printed minus
log(theta) and floor. Neither is corrected here. The density is candidate count
divided by the number of binary syndromes; it is not a success probability for
a planted key distribution or a cryptographic hardness statement. -/

namespace SDitH.Spec.ParameterSelection

noncomputable section

def binaryDensity (candidates codimension : Nat) : ℝ :=
  (candidates : ℝ) / (2 : ℝ) ^ codimension

def rsdDensity (w m codimension : Nat) : ℝ :=
  binaryDensity (m ^ w) codimension

def sdDensity (n w codimension : Nat) : ℝ :=
  binaryDensity (Nat.choose n w) codimension

/-- The displayed k_rsd^max, including its literal signs and floor. -/
def sourceRSDMaxDimension (n w : Nat) (theta : ℝ) : ℤ :=
  (n : ℤ) - ⌊(w : ℝ) * Real.logb 2 ((n : ℝ) / w) - Real.logb 2 theta⌋

/-- The displayed k_sd. -/
def sourceSDDimension (n w : Nat) : ℤ :=
  (n : ℤ) - ⌊Real.logb 2 (Nat.choose n w : ℝ)⌋

/-- Arithmetic threshold derived from the density target, not a replacement
for either source formula. The proof of its characterization is separate. -/
def requiredCodimension (candidates : Nat) (theta : ℝ) : Nat :=
  ⌈Real.logb 2 (candidates : ℝ) + Real.logb 2 theta⌉₊

/-- Average fiber size over all binary syndromes for a fixed candidate-to-
syndrome map. No randomness or regularity of that map is presumed. -/
def averageSolutionCount {A : Type*} (candidates : Finset A) (r : Nat)
    (syndrome : A → (Fin r → Fin 2)) : ℝ := by
  classical
  exact (∑ y : Fin r → Fin 2,
    ((candidates.filter (fun x => syndrome x = y)).card : ℝ)) /
      Fintype.card (Fin r → Fin 2)

/-- Greatest byte-aligned dimension below a supplied valid upper bound,
provided its rounded codimension fits in n. No SD lower bound is presumed. -/
def byteAlignedDimension (n maxDimension : Nat) : Nat :=
  n - ceil8 (n - maxDimension)

end
end SDitH.Spec.ParameterSelection
