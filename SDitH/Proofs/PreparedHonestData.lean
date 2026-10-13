import SDitH.Proofs.PreparedData

/-! The prepared signing state's revealed data as the honest data map of
the hidden seed's PRG vector. Composing the executed commitment's data
with the arithmetic link, the prepared state's hashed coefficients below
the top, witness correction and plain check are the honest data map, with
the other parties' constants, the zero-randomness coefficients and the
slope terms, applied to the PRG vector of the hidden party's seed at
execution zero. With the PRG hypothesis, this data is uniform over that
seed and independent of the witness. -/

namespace SDitH.Proofs.PreparedHonestData

open Spec.DomainSeparation Spec.SharedScheme Spec.SharedSigner Spec.SharedSigning Spec.HashCipherEvaluation
open Spec.CoefficientCompression Spec.PIOPComposition Spec.BLC Spec.BLCCommit Spec.FieldRepresentation
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open HonestViewUniform SignatureData TranscriptRevealed PRGHypothesis PreparedData
open scoped BigOperators Classical

noncomputable section

variable (category : Category)
variable {tau kappa s higherCount r k w wpow : Nat} [NeZero tau] {widths : List Nat}
variable (family : Spec.IdealCipher.Family (Bits (width category)) (Bits (width category)))
  (table : List Bool → Option (Out (width category) s (selectorCount widths * w) (width category * (widths.length - 1))))
  (ciphers : List (Spec.IdealCipher.Entry (Bits (width category)) (Bits (width category))))

/-- The prepared state's data is the honest data of the hidden seed's PRG
vector: hashed coefficients below the top, witness correction and plain
check. -/
theorem prepared_honestData
    (S : SigningSetting (QuotientRing category) (width category) tau kappa s r k w wpow higherCount widths)
    (hxi : S.signer.xi = generator category) (salt root : Bits (width category))
    (witness : Fin (selectorCount widths * w) → ZMod 2)
    (committed : Committed (QuotientRing category) (width category) tau kappa s (selectorCount widths * w)
      (width category * (widths.length - 1)))
    (h : Evaluates family table ciphers (commitProgram S.signer salt root witness) committed) (hid : Fin (2 ^ kappa)) :
    let random := randomTable S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough
    let challenge := S.expandBatching committed.result.lines
    let seedVector := prgVector S.signer.p salt S.signer.randomCount S.signer.enough 0 (committed.seeds 0 hid)
    ∃ (M : Matrix (Fin s) (Fin (selectorCount widths * w + width category * (widths.length - 1))) (ZMod 2)),
      let data := honestData category M (constantsA random witness hid) (othersPacked category widths random hid)
        (constantsC random M hid)
        (zeroRandomnessHashed category widths S.hsize challenge.1 challenge.2 S.H' S.y Spec.GrayCode.grayFieldRow random M
          witness S.hdegree)
        (slopeTerm category widths Spec.GrayCode.grayFieldRow random (r := r) (k := k)) seedVector
      (∀ j : Fin (widths.length - 1), (stateOf S salt committed).1.2 ⟨j.val, by have := j.isLt; have := S.hdegree; omega⟩ = data.2.1 j) ∧
      committed.result.auxiliary.witnessCorrection = data.1 ∧
      committed.result.auxiliary.plain = data.2.2 := by
  intro random challenge seedVector
  obtain ⟨M, hwc, hplain, _, _, hhashed⟩ :=
    prepared_eq_honestData category family table ciphers S hxi salt root witness committed h
  refine ⟨M, ?_, ?_, ?_⟩
  · intro j
    rw [hhashed]
    exact hashed_eq_honestData category widths S.hsize challenge.1 challenge.2 S.H' S.y Spec.GrayCode.grayFieldRow random M
      witness hid S.hdegree j
  · rw [hwc]
    exact (aux_eq_honestData category widths S.hsize challenge.1 challenge.2 S.H' S.y Spec.GrayCode.grayFieldRow random M
      witness hid S.hdegree).1
  · rw [hplain]
    exact (aux_eq_honestData category widths S.hsize challenge.1 challenge.2 S.H' S.y Spec.GrayCode.grayFieldRow random M
      witness hid S.hdegree).2

end
end SDitH.Proofs.PreparedHonestData
