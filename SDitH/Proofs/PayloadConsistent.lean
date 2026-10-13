import SDitH.Proofs.PayloadBridge
import SDitH.Proofs.ConstantTermZero
import SDitH.Proofs.SimulatedWith
import SDitH.Proofs.CoefficientCompression

/-! Payload consistency of the honest signer. Under the candidate encoding
(the psi map of the Gray challenge row) and at least one higher
coefficient, for a solution witness the honest signer's hashed coefficient
tuple of an executed commitment equals the simulator's recomputed tuple at
every hidden vector with nonzero encoding: the verifier's recomputed value
is the prover polynomial's evaluation at the inverse challenge (the
bridge), the prover polynomial has the bounded degree and a vanishing
constant term, so the restored tuple is the hashed one. -/

namespace SDitH.Proofs.PayloadConsistent

open Spec.BAVC Spec.DomainSeparation Spec.SharedSigner Spec.SharedSigning Spec.CandidateSimulator Spec.BLC
open Spec.BLCSeedFold Spec.BLCSeedLines Spec.BLCCommit Spec.PIOPComposition Spec.CoefficientCompression
open Spec.HashCipherEvaluation Spec.SlopeConsistencyGame Polynomial
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open SimulatedWith PayloadBridge ConstantTermZero PIOPComposition CoefficientCompression
open scoped Classical

noncomputable section

section Degree

variable {K F : Type*} [CommRing K] [Field F] [Algebra K F]

/-- A line has degree at most one. -/
theorem buildLine_natDegree_le (constant : K) (slope : F) : (buildLine constant slope).natDegree ≤ 1 := by
  unfold buildLine
  exact (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))

end Degree

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- Payload consistency under the candidate encoding and at least one
higher coefficient. -/
theorem payload_consistent
    (hencode : S.encode = fun hidden => psi S.signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hhigher : 1 ≤ higherCount) : PayloadConsistent S := by
  intro salt root witness hsol family table ciphers committed heval hidden hne
  obtain ⟨hseeds, _, _, _, _, _, _, _, hwit, hrand, haux, _⟩ :=
    SharedSigner.commit_evaluates family table ciphers S.signer salt root witness committed heval
  have hpsi : psi S.signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden) ≠ 0 := by
    simpa [hencode] using hne
  have hdelta : (S.encode hidden)⁻¹ ≠ 0 := inv_ne_zero hne
  have hw : ∀ j, (committed.result.witness j).natDegree ≤ 1 := by
    intro j
    rw [hwit]
    exact buildLine_natDegree_le _ _
  have hr : ∀ j, (committed.result.randomness j).natDegree ≤ 1 := by
    intro j
    rw [hrand]
    exact buildLine_natDegree_le _ _
  have hd : 2 ≤ widths.length := by
    rw [S.hdegree]
    omega
  simp only [stateOf, simulatedCoefficients]
  set challenge := S.expandBatching committed.result.lines with hchallenge
  set p := proverRun widths S.hsize S.signer.xi challenge.1 challenge.2 S.H' S.y committed.result.witness
    committed.result.randomness with hp
  have hdeg : p.natDegree ≤ higherCount + 1 := by
    rw [← S.hdegree]
    exact prover_degree widths S.hsize hd S.signer.xi challenge.1 challenge.2 S.H' S.y committed.result.witness
      committed.result.randomness hw hr
  have hc0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    refine prover_eval_zero widths S.hsize S.signer.xi challenge.1 challenge.2 S.H' S.y witness hsol.1 hsol.2
      committed.result.witness (fun j => ?_) committed.result.randomness
    rw [hwit]
    exact BLC.commitArithmetic_witness_at_zero _ _ _ _ _ j
  have haux' : committed.result.auxiliary.corrections = positiveCorrections (correction Spec.GrayCode.grayFieldRow
      (randomTable S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough)) := by
    rw [haux, hseeds]
  have hwc : committed.result.auxiliary.witnessCorrection =
      (commitArithmetic S.signer.xi Spec.GrayCode.grayFieldRow
        (randomTable S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough) committed.mask witness).witnessCorrection := by
    rw [haux, hseeds]
  have hW : (fun j => (committed.result.witness j).eval (S.encode hidden)⁻¹) = fun j =>
      algebraMap (ZMod 2) F (committed.result.auxiliary.witnessCorrection j) + (S.encode hidden)⁻¹ *
        psi S.signer.xi (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough
          committed.result.auxiliary hidden (witnessIndex j)) := by
    funext j
    rw [hwit, hwc, hseeds]
    simp only [hencode]
    exact witnessLine_eval S.signer.xi S.signer.p salt _ S.signer.randomCount S.signer.enough committed.mask witness
      committed.result.auxiliary (by rw [← hseeds]; exact haux') hidden hpsi j
  have hR : (fun j => (committed.result.randomness j).eval (S.encode hidden)⁻¹) = fun j =>
      (S.encode hidden)⁻¹ * psi S.signer.xi (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount
        S.signer.enough committed.result.auxiliary hidden (randomnessIndex j)) := by
    funext j
    rw [hrand, hseeds]
    simp only [hencode]
    exact randomnessLine_eval S.signer.xi S.signer.p salt _ S.signer.randomCount S.signer.enough committed.mask witness
      committed.result.auxiliary (by rw [← hseeds]; exact haux') hidden hpsi j
  have hvalue : verifierRun widths S.hsize S.signer.xi (S.encode hidden)⁻¹ challenge.1 challenge.2 S.H' S.y
      (fun j => algebraMap (ZMod 2) F (committed.result.auxiliary.witnessCorrection j) + (S.encode hidden)⁻¹ *
        psi S.signer.xi (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough
          committed.result.auxiliary hidden (witnessIndex j)))
      (fun j => (S.encode hidden)⁻¹ * psi S.signer.xi (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount
        S.signer.enough committed.result.auxiliary hidden (randomnessIndex j))) = p.eval (S.encode hidden)⁻¹ := by
    rw [hp, verifier_evaluates_prover, hW, hR]
  rw [hvalue]
  exact ((restored_eq_hashed_iff higherCount p hdeg _ hdelta).mpr hc0).symm

end
end SDitH.Proofs.PayloadConsistent
