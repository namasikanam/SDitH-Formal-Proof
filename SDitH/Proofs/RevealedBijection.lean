import SDitH.Proofs.HiddenShareTranslation
import SDitH.Proofs.IntegerSamplingProbability

/-! The revealed triple as an affine bijection of the hidden party's vector.
The witness correction is a constant minus the vector's witness
coordinates, the randomness constants are its randomness coordinates plus
a constant, and the plain consistency check is its check coordinates plus
the mask image of its payload coordinates plus a constant; the map from
the vector to the triple is therefore a bijection (the payload is read off
the first two components and the check coordinates from the third), so a
uniform vector yields a uniform triple whatever the constants, in
particular whatever the witness. -/

namespace SDitH.Proofs.RevealedBijection

open Spec.BLC
open scoped BigOperators Classical

noncomputable section

variable {K : Type*} [CommRing K] {s wit rnd : Nat}

/-- The plain consistency check reads the check coordinates plus the mask
image of the payload coordinates. -/
theorem consistencyCheck_eq (M : Matrix (Fin s) (Fin (wit + rnd)) K) (r : Fin (s + (wit + rnd)) → K) (a : Fin s) :
    consistencyCheck M r a = r (Fin.castAdd (wit + rnd) a) + ∑ c, M a c * r (Fin.natAdd s c) := by
  unfold consistencyCheck Spec.Batching.systematicLeft
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
  simp [Finset.sum_ite_eq]

/-- The revealed triple of a hidden vector, with the other parties' contributions
as constants. -/
def revealedMap (M : Matrix (Fin s) (Fin (wit + rnd)) K) (A : Fin wit → K) (B : Fin rnd → K) (Cc : Fin s → K)
    (r : Fin (s + (wit + rnd)) → K) : (Fin wit → K) × (Fin rnd → K) × (Fin s → K) :=
  (fun j => A j - r (witnessIndex j), fun j => r (randomnessIndex j) + B j, fun a => consistencyCheck M r a + Cc a)

/-- The payload coordinates recovered from the first two components. -/
def payloadOf (A : Fin wit → K) (B : Fin rnd → K) (x : Fin wit → K) (y : Fin rnd → K) : Fin (wit + rnd) → K :=
  Fin.addCases (fun j => A j - x j) (fun j => y j - B j)

/-- The inverse of the revealed map. -/
def revealedInv (M : Matrix (Fin s) (Fin (wit + rnd)) K) (A : Fin wit → K) (B : Fin rnd → K) (Cc : Fin s → K)
    (t : (Fin wit → K) × (Fin rnd → K) × (Fin s → K)) : Fin (s + (wit + rnd)) → K :=
  Fin.addCases (fun a => t.2.2 a - Cc a - ∑ c, M a c * payloadOf A B t.1 t.2.1 c) (payloadOf A B t.1 t.2.1)

theorem payloadOf_revealed (M : Matrix (Fin s) (Fin (wit + rnd)) K) (A : Fin wit → K) (B : Fin rnd → K) (Cc : Fin s → K)
    (r : Fin (s + (wit + rnd)) → K) (c : Fin (wit + rnd)) :
    payloadOf A B (revealedMap M A B Cc r).1 (revealedMap M A B Cc r).2.1 c = r (Fin.natAdd s c) := by
  unfold payloadOf revealedMap
  refine Fin.addCases (fun j => ?_) (fun j => ?_) c
  · simp [witnessIndex]
  · simp [randomnessIndex]

/-- The revealed map is a bijection of the hidden vector. -/
def revealedEquiv (M : Matrix (Fin s) (Fin (wit + rnd)) K) (A : Fin wit → K) (B : Fin rnd → K) (Cc : Fin s → K) :
    (Fin (s + (wit + rnd)) → K) ≃ (Fin wit → K) × (Fin rnd → K) × (Fin s → K) where
  toFun := revealedMap M A B Cc
  invFun := revealedInv M A B Cc
  left_inv := by
    intro r
    funext i
    unfold revealedInv
    refine Fin.addCases (fun a => ?_) (fun c => ?_) i
    · simp only [Fin.addCases_left]
      simp only [payloadOf_revealed]
      show (consistencyCheck M r a + Cc a) - Cc a - ∑ c, M a c * r (Fin.natAdd s c) = r (Fin.castAdd (wit + rnd) a)
      rw [consistencyCheck_eq]
      ring
    · simp only [Fin.addCases_right]
      exact payloadOf_revealed M A B Cc r c
  right_inv := by
    intro t
    obtain ⟨x, y, z⟩ := t
    have hpay : ∀ c, revealedInv M A B Cc (x, y, z) (Fin.natAdd s c) = payloadOf A B x y c := by
      intro c
      simp [revealedInv]
    have hcheck : ∀ a, revealedInv M A B Cc (x, y, z) (Fin.castAdd (wit + rnd) a) =
        z a - Cc a - ∑ c, M a c * payloadOf A B x y c := by
      intro a
      simp [revealedInv]
    unfold revealedMap
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext j
      show A j - revealedInv M A B Cc (x, y, z) (witnessIndex j) = x j
      rw [witnessIndex, hpay]
      simp [payloadOf]
    · funext j
      show revealedInv M A B Cc (x, y, z) (randomnessIndex j) + B j = y j
      rw [randomnessIndex, hpay]
      simp [payloadOf]
    · funext a
      show consistencyCheck M (revealedInv M A B Cc (x, y, z)) a + Cc a = z a
      rw [consistencyCheck_eq, hcheck]
      simp only [hpay]
      ring

/-- A uniform hidden vector reveals a uniform triple, whatever the constants
(in particular whatever the witness). -/
theorem revealed_uniform [Fintype K] [Nonempty K] (M : Matrix (Fin s) (Fin (wit + rnd)) K) (A : Fin wit → K)
    (B : Fin rnd → K) (Cc : Fin s → K) :
    (PMF.uniformOfFintype (Fin (s + (wit + rnd)) → K)).map (revealedMap M A B Cc) =
      PMF.uniformOfFintype ((Fin wit → K) × (Fin rnd → K) × (Fin s → K)) :=
  IntegerSamplingProbability.map_uniform_equiv (revealedEquiv M A B Cc)

theorem revealed_independent [Fintype K] [Nonempty K] (M : Matrix (Fin s) (Fin (wit + rnd)) K) (A A' : Fin wit → K)
    (B B' : Fin rnd → K) (Cc Cc' : Fin s → K) :
    (PMF.uniformOfFintype (Fin (s + (wit + rnd)) → K)).map (revealedMap M A B Cc) =
      (PMF.uniformOfFintype (Fin (s + (wit + rnd)) → K)).map (revealedMap M A' B' Cc') := by
  rw [revealed_uniform, revealed_uniform]

end
end SDitH.Proofs.RevealedBijection
