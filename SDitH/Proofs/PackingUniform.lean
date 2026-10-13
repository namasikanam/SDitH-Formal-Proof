import SDitH.Proofs.FieldIrreducibility
import SDitH.Proofs.IntegerSamplingProbability

/-! Uniformity of packed layer constants and the one-time pad. The
coefficient encoding of a full width of bits in the submitted power basis
is injective, and the quotient ring has exactly as many elements as bit
vectors, so it is a bijection: uniform bits pack to a uniform ring element.
Adding an independent uniform element to any value (a one-time pad) is
uniform, and a uniform pad on one coordinate of a product makes that
coordinate uniform and independent of the rest. These are the
probabilistic inputs of the honest-verifier zero-knowledge argument. -/

namespace SDitH.Proofs.PackingUniform

open Spec.FieldRepresentation FieldIrreducibility
open scoped BigOperators ENNReal Classical

noncomputable section

/-- The full-width coefficient encoding is a bijection. -/
theorem encodeCoefficients_bijective (category : Category) :
    Function.Bijective (encodeCoefficients category (n := width category)) := by
  have hinj := FieldRepresentation.encodeCoefficients_injective category (n := width category) le_rfl
  have hcard : Fintype.card (Fin (width category) → ZMod 2) = Fintype.card (QuotientRing category) := by
    rw [quotient_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩

/-- The packing bijection as an equivalence. -/
def packEquiv (category : Category) : (Fin (width category) → ZMod 2) ≃ QuotientRing category :=
  Equiv.ofBijective _ (encodeCoefficients_bijective category)

/-- Uniform bits pack to a uniform ring element. -/
theorem pack_uniform (category : Category) :
    (PMF.uniformOfFintype (Fin (width category) → ZMod 2)).map (encodeCoefficients category) =
      PMF.uniformOfFintype (QuotientRing category) :=
  IntegerSamplingProbability.map_uniform_equiv (packEquiv category)

section Pad

variable {G : Type*} [AddCommGroup G] [Fintype G] [Nonempty G]

/-- A uniform pad added to any fixed value is uniform. -/
theorem pad_uniform (c : G) :
    (PMF.uniformOfFintype G).map (fun g => g + c) = PMF.uniformOfFintype G :=
  IntegerSamplingProbability.map_uniform_equiv (Equiv.addRight c)

/-- A uniform pad added to a value drawn from any distribution is uniform. -/
theorem pad_bind_uniform {A : Type*} (p : PMF A) (f : A → G) :
    (p.bind fun a => (PMF.uniformOfFintype G).map (fun g => g + f a)) = PMF.uniformOfFintype G := by
  have h : (fun a => (PMF.uniformOfFintype G).map (fun g => g + f a)) = fun _ => PMF.uniformOfFintype G := by
    funext a
    exact pad_uniform (f a)
  rw [h, PMF.bind_const]

/-- A uniform pad on a coordinate makes the padded pair the pair of the
original distribution and an independent uniform element. -/
theorem pad_pair_uniform {A : Type*} (p : PMF A) (f : A → G) :
    (p.bind fun a => (PMF.uniformOfFintype G).map (fun g => (a, g + f a))) =
      p.bind fun a => (PMF.uniformOfFintype G).map (fun g => (a, g)) := by
  congr 1
  funext a
  have h := pad_uniform (f a)
  calc (PMF.uniformOfFintype G).map (fun g => (a, g + f a))
      = ((PMF.uniformOfFintype G).map (fun g => g + f a)).map (fun g => (a, g)) := by
        rw [PMF.map_comp]
        rfl
    _ = _ := by rw [h]

end Pad

end
end SDitH.Proofs.PackingUniform
