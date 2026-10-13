import SDitH.Proofs.PIOPMaskCoeff
import SDitH.Proofs.PackingUniform
import SDitH.Spec.CoefficientCompression

/-! The pads on the hashed coefficients. The hashed coefficient tuple of the
prover polynomial is the zero-randomness tuple plus the mask coefficients;
for randomness lines, the mask coefficient at position k is the packed
constant of layer d-2-k (plus a slope term), and a layer's packed constant
of bits is the coefficient encoding in the submitted power basis when the
field is the submitted quotient ring with its generator, so uniform layer
bits give a uniform pad. -/

namespace SDitH.Proofs.HashedPads

open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Spec.CoefficientCompression Spec.FieldRepresentation
open Polynomial
open scoped BigOperators Classical

noncomputable section

section FieldPart

variable {K F : Type*} [CommRing K] [Field F] [Algebra K F]

/-- The hashed tuple is the zero-randomness tuple padded by the mask
coefficients. -/
theorem hashed_eq_padded {r k w lambda higherCount : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k)
    (xi : F) (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F) (H' : Matrix (Fin r) (Fin k) K)
    (y : Fin r → K) (witness : Fin (selectorCount widths * w) → F[X])
    (randomness : Fin (lambda * (widths.length - 1)) → F[X]) (j : Fin (higherCount + 1)) :
    hashedCoefficients higherCount (proverRun widths hsize xi gamma gammaPrime H' y witness randomness) j =
      hashedCoefficients higherCount (proverRun widths hsize xi gamma gammaPrime H' y witness 0) j +
        (formatMask (C xi) X (formatRandomness randomness)).coeff j.val := by
  unfold hashedCoefficients
  exact PIOPMaskCoeff.proverRun_coeff_succ widths hsize xi gamma gammaPrime H' y witness randomness j.val

end FieldPart

variable {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]

/-- A layer's packed constant of base-ring bits. -/
def packedConst {lambda : Nat} (xi : F) (bits : Fin lambda → K) : F :=
  ∑ j, xi ^ j.val * algebraMap K F (bits j)

/-- The mask coefficient of randomness lines whose constants are algebra
images of bits: the packed constant of layer d-2-k plus the slope term. -/
theorem formatMask_coeff_bits {d lambda : Nat} (xi : F) (bits : Fin (d - 1) → Fin lambda → K)
    (b : Fin (d - 1) → Fin lambda → F) (k : Nat) :
    (formatMask (C xi) X (fun i j => C (algebraMap K F (bits i j)) + C (b i j) * X)).coeff k =
      (∑ i : Fin (d - 1), if i.val = d - 2 - k ∧ k + 2 ≤ d then packedConst xi (bits i) else 0) +
      (∑ i : Fin (d - 1), if i.val = d - 1 - k ∧ 1 ≤ k ∧ k + 1 ≤ d then ∑ j, xi ^ j.val * b i j else 0) :=
  PIOPMaskCoeff.formatMask_coeff_lines xi (fun i j => algebraMap K F (bits i j)) b k

/-- In the submitted quotient ring with its generator, the packed constant of a
full width of bits is the coefficient encoding. -/
theorem packedConst_eq_encode (category : Category) (bits : Fin (width category) → ZMod 2) :
    packedConst (generator category) bits = encodeCoefficients category bits := by
  unfold packedConst encodeCoefficients
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Uniform layer bits give a uniform packed constant. -/
theorem packedConst_uniform (category : Category) :
    (PMF.uniformOfFintype (Fin (width category) → ZMod 2)).map (packedConst (generator category)) =
      PMF.uniformOfFintype (QuotientRing category) := by
  calc (PMF.uniformOfFintype (Fin (width category) → ZMod 2)).map (packedConst (generator category))
      = (PMF.uniformOfFintype (Fin (width category) → ZMod 2)).map (encodeCoefficients category) := by
        congr 1
        funext bits
        exact packedConst_eq_encode category bits
    _ = _ := PackingUniform.pack_uniform category

/-- A uniform packed constant pads any value to a uniform value. -/
theorem packedConst_pad_uniform (category : Category) (c : QuotientRing category) :
    (PMF.uniformOfFintype (Fin (width category) → ZMod 2)).map (fun bits => c + packedConst (generator category) bits) =
      PMF.uniformOfFintype (QuotientRing category) := by
  have h : (fun bits : Fin (width category) → ZMod 2 => c + packedConst (generator category) bits) =
      (fun g => g + c) ∘ packedConst (generator category) := by
    funext bits
    simp [Function.comp, add_comm]
  rw [h, ← PMF.map_comp, packedConst_uniform]
  exact PackingUniform.pad_uniform c

end
end SDitH.Proofs.HashedPads
