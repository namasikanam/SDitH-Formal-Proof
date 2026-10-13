import SDitH.Proofs.SignatureData
import SDitH.Proofs.SharedSigning

/-! The prepared signing state's data as the honest data of the hidden
seed. An executed commitment over the submitted field with its generator
has the committed arithmetic's lines, auxiliary data and seeds, so the
prepared state's hashed coefficients below the top, witness correction
and plain check are the honest data map applied to the PRG vector of the
hidden party's seed at execution zero. This lifts the arithmetic link to
the executed signer. -/

namespace SDitH.Proofs.PreparedData

open Spec.DomainSeparation Spec.SharedScheme Spec.SharedSigner Spec.SharedSigning Spec.HashCipherEvaluation
open Spec.CoefficientCompression Spec.PIOPComposition Spec.BLC Spec.BLCCommit Spec.FieldRepresentation
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open HonestViewUniform SignatureData TranscriptRevealed PRGHypothesis
open scoped BigOperators Classical

noncomputable section

variable (category : Category)
variable {lambda tau kappa s higherCount r k w wpow : Nat} [NeZero tau] {widths : List Nat}
variable (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
  (table : List Bool → Option (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
  (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))

/-- The hidden party's vector at execution zero of an executed commitment: the
random table's row, which is the PRG vector of its seed. -/
theorem hidden_vector_eq (S : SignerSetting (QuotientRing category) lambda tau kappa s (selectorCount widths * w)
      (lambda * (widths.length - 1))) (salt : Bits lambda) (committed : Committed (QuotientRing category) lambda tau kappa s
      (selectorCount widths * w) (lambda * (widths.length - 1))) (hid : Fin (2 ^ kappa)) :
    randomTable S.p salt committed.seeds S.randomCount S.enough 0 hid =
      prgVector S.p salt S.randomCount S.enough 0 (committed.seeds 0 hid) := rfl

/-- The prepared state's hashed coefficients below the top and auxiliary
components of an executed commitment over the submitted field. -/
theorem prepared_eq_honestData
    (S : SigningSetting (QuotientRing category) lambda tau kappa s r k w wpow higherCount widths)
    (hxi : S.signer.xi = generator category) (salt root : Bits lambda)
    (witness : Fin (selectorCount widths * w) → ZMod 2)
    (committed : Committed (QuotientRing category) lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (h : Evaluates family table ciphers (commitProgram S.signer salt root witness) committed) :
    let random := randomTable S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough
    let challenge := S.expandBatching committed.result.lines
    ∃ (M : Matrix (Fin s) (Fin (selectorCount widths * w + lambda * (widths.length - 1))) (ZMod 2)),
      committed.result.auxiliary.witnessCorrection =
          (commitArithmetic (generator category) Spec.GrayCode.grayFieldRow random M witness).witnessCorrection ∧
      committed.result.auxiliary.plain =
          (commitArithmetic (generator category) Spec.GrayCode.grayFieldRow random M witness).plainCheck ∧
      committed.result.witness = (commitArithmetic (generator category) Spec.GrayCode.grayFieldRow random M witness).witnessLines ∧
      committed.result.randomness =
          (commitArithmetic (generator category) Spec.GrayCode.grayFieldRow random M witness).randomnessLines ∧
      (stateOf S salt committed).1.2 = hashedCoefficients higherCount (proverRun widths S.hsize (generator category)
          challenge.1 challenge.2 S.H' S.y
          (commitArithmetic (generator category) Spec.GrayCode.grayFieldRow random M witness).witnessLines
          (commitArithmetic (generator category) Spec.GrayCode.grayFieldRow random M witness).randomnessLines) := by
  intro random challenge
  obtain ⟨hseeds, _, _, _, _, _, _, _, hwit, hrand, haux, _⟩ :=
    SharedSigner.commit_evaluates family table ciphers S.signer salt root witness committed h
  rw [hxi] at hwit hrand haux
  have hrandom : random = randomTable S.signer.p salt
      (Spec.BAVC.commit (SharedSigner.inducedPrimitives (tau := tau) (kappa := kappa) family table S.signer.layout
        S.signer.variant) salt root).seeds S.signer.randomCount S.signer.enough := by
    simp only [random, hseeds]
  refine ⟨committed.mask, ?_, ?_, ?_, ?_, ?_⟩
  · rw [haux, hrandom]
  · rw [haux, hrandom]
  · rw [hwit, hrandom]
  · rw [hrand, hrandom]
  · show hashedCoefficients higherCount (proverRun widths S.hsize S.signer.xi challenge.1 challenge.2 S.H' S.y
        committed.result.witness committed.result.randomness) = _
    rw [hxi, hwit, hrand, hrandom]

end
end SDitH.Proofs.PreparedData
