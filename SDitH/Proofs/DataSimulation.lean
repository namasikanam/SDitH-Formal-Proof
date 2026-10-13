import SDitH.Proofs.PreparedHonestData

/-! The simulation step at the data level. The honest signer with the real
witness and the simulator with a fake witness run the same commitment
program on the same salt, root and seeds, so their revealed data (hashed
coefficients below the top, witness correction, plain check) are the
honest data map with the same other-party constants, mask and slope terms
and with the witness-dependent constants (the witness correction's
constant and the zero-randomness hashed coefficients) differing. Under the
PRG hypothesis and a uniform hidden seed, the two data distributions
coincide. The uniformity of the hidden leaf seed (an ideal-cipher step on
unqueried tree paths) is carried as an explicit hypothesis. -/

namespace SDitH.Proofs.DataSimulation

open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Spec.BLC Spec.BLCCommit Spec.FieldRepresentation
open Spec.DomainSeparation
open HonestViewUniform SignatureData TranscriptRevealed PRGHypothesis
open scoped BigOperators Classical

noncomputable section

variable (category : Category)
variable {r k w higherCount tau N kappa s : Nat} [NeZero tau] (widths : List Nat)
  (hsize : leafCount widths * w = r + k) (gamma : Fin (blockCount r (width category)) → QuotientRing category)
  (gammaPrime : Fin w → QuotientRing category) (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
  (phi : Fin N → Fin kappa → ZMod 2)
  (random : Fin tau → Fin N → Fin (s + (selectorCount widths * w + width category * (widths.length - 1))) → ZMod 2)
  (M : Matrix (Fin s) (Fin (selectorCount widths * w + width category * (widths.length - 1))) (ZMod 2))
  (h : Fin N) (hdeg : widths.length = higherCount + 1)

/-- The revealed data of a signer with a given witness, as a function of the
hidden party's vector. -/
def signerData (witness : Fin (selectorCount widths * w) → ZMod 2)
    (v : Fin (s + (selectorCount widths * w + width category * (widths.length - 1))) → ZMod 2) :
    (Fin (selectorCount widths * w) → ZMod 2) × (Fin (widths.length - 1) → QuotientRing category) × (Fin s → ZMod 2) :=
  honestData category M (constantsA random witness h) (othersPacked category widths random h) (constantsC random M h)
    (zeroRandomnessHashed category widths hsize gamma gammaPrime H' y phi random M witness hdeg)
    (slopeTerm category widths phi random (r := r) (k := k)) v

/-- The data of the real witness and of a fake witness share the other-party
constants, the mask and the slope terms; only the witness-dependent
constants differ. -/
theorem signerData_eq (witness fake : Fin (selectorCount widths * w) → ZMod 2) :
    signerData category widths hsize gamma gammaPrime H' y phi random M h hdeg witness =
        honestData category M (constantsA random witness h) (othersPacked category widths random h)
          (constantsC random M h)
          (zeroRandomnessHashed category widths hsize gamma gammaPrime H' y phi random M witness hdeg)
          (slopeTerm category widths phi random (r := r) (k := k)) ∧
      signerData category widths hsize gamma gammaPrime H' y phi random M h hdeg fake =
        honestData category M (constantsA random fake h) (othersPacked category widths random h)
          (constantsC random M h)
          (zeroRandomnessHashed category widths hsize gamma gammaPrime H' y phi random M fake hdeg)
          (slopeTerm category widths phi random (r := r) (k := k)) :=
  ⟨rfl, rfl⟩

/-- Under a uniform hidden vector, the real and fake signers' data have the
same distribution. -/
theorem signerData_uniform_vector (witness fake : Fin (selectorCount widths * w) → ZMod 2) :
    (PMF.uniformOfFintype (Fin (s + (selectorCount widths * w + width category * (widths.length - 1))) → ZMod 2)).map
        (signerData category widths hsize gamma gammaPrime H' y phi random M h hdeg witness) =
      (PMF.uniformOfFintype (Fin (s + (selectorCount widths * w + width category * (widths.length - 1))) → ZMod 2)).map
        (signerData category widths hsize gamma gammaPrime H' y phi random M h hdeg fake) := by
  unfold signerData
  exact honestData_independent category M _ _ _ _ _ _ _ _ _ _

/-- Under the PRG hypothesis and a uniform hidden seed, the real and fake
signers' data over the hidden seed have the same distribution. -/
theorem signerData_uniform_seed (p : Primitives (width category) tau kappa s (selectorCount widths * w)
      (width category * (widths.length - 1)))
    (salt : Bits (width category)) (count : Nat)
    (enough : s + (selectorCount widths * w + width category * (widths.length - 1)) ≤ 8 * count) (e : Fin tau)
    (hprg : PRGUniform p salt count enough e) (seeds : PMF (Bits (width category)))
    (hseed : seeds = PMF.uniformOfFintype (Bits (width category)))
    (witness fake : Fin (selectorCount widths * w) → ZMod 2) :
    seeds.map (fun seed => signerData category widths hsize gamma gammaPrime H' y phi random M h hdeg witness
        (prgVector p salt count enough e seed)) =
      seeds.map (fun seed => signerData category widths hsize gamma gammaPrime H' y phi random M h hdeg fake
        (prgVector p salt count enough e seed)) := by
  subst hseed
  unfold signerData
  exact honestData_independent_of_prg category p salt count enough e hprg M _ _ _ _ _ _ _ _ _ _

end
end SDitH.Proofs.DataSimulation
