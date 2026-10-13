import SDitH.Spec.CandidateSimulator
import SDitH.Proofs.CandidateCompleteness
import SDitH.Proofs.CandidateSchemeChain

/-! Completeness of a committed transcript with its recomputed values: the
candidate verification of an executed commitment (with any witness, in
particular the simulator's fake one) opened at hidden indices evaluates on
the signer's world to the inverted challenge, the affine share values of
the committed seeds and the committed lines digest, so the verification
input recomputed from it hashes the committed lines digest and exactly the
simulator's coefficient tuple. This is the deterministic half of the
simulator's programming step. -/

namespace SDitH.Proofs.SimulatedCompleteness

open Spec.DomainSeparation Spec.SharedScheme Spec.SharedSigner Spec.SharedSigning Spec.CandidateScheme
open Spec.CandidateVerifier Spec.CandidateBAVC Spec.CandidateSimulator Spec.HashCipherEvaluation Spec.HashCipherProgram
open Spec.BLCSeedLines Spec.CoefficientCompression Spec.PIOPComposition
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open scoped Classical
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
variable (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
  (table : List Bool → Option (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
  (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))

/-- The candidate verification of an executed commitment evaluates to the
inverted challenge, the affine share values on the committed seeds and the
committed lines digest. -/
theorem committed_verifies (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hlayout : V.layout = S.signer.layout) (hvariant : V.variant = S.signer.variant)
    (hencoding : V.encoding = S.signer.encoding)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes S.encode S.signer.randomCount S.signer.enough)
    (htail : S.signer.linesTail = verifierLinesTail S.signer.encoding)
    (salt root : Bits lambda) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (committed : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (h : Evaluates family table ciphers (commitProgram S.signer salt root witness) committed)
    (piop : Spec.BAVC.Digest lambda) (ctr : Spec.BLCRetry.Counter) :
    let hidden := V.expand piop ctr
    let aux := committed.result.auxiliary
    Evaluates family table ciphers
      (Spec.CandidateScheme.verifyProgram V salt aux piop (ctr, openKey committed.result.key hidden))
      (Except.ok ⟨(S.encode hidden)⁻¹,
        fun j => algebraMap (ZMod 2) F (aux.witnessCorrection j) + (S.encode hidden)⁻¹ * Spec.BLC.psi S.signer.xi
          (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough aux hidden (Spec.BLC.witnessIndex j)),
        fun j => (S.encode hidden)⁻¹ * Spec.BLC.psi S.signer.xi
          (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough aux hidden
            (Spec.BLC.randomnessIndex j)),
        committed.result.lines⟩) := by
  intro hidden aux
  obtain ⟨delta, wv, rv, hev⟩ := CandidateCompleteness.honest_verifies family table ciphers S.signer V S.signer.xi S.encode
    hlayout hvariant hencoding hmid htail salt root witness committed h piop ctr
  obtain ⟨hseeds, hkey, _⟩ := SharedSigner.commit_evaluates family table ciphers S.signer salt root witness committed h
  obtain ⟨recon, pa, pl, value, hrecon, _, hmidv, _, hrecovered⟩ :=
    CandidateSchemeChain.verify_evaluates family table ciphers V salt aux piop (ctr, openKey committed.result.key hidden) _ hev
  obtain ⟨hrseeds, _⟩ := CandidateBAVC.reconstruct_evaluates family table ciphers V.layout V.variant salt _ _ recon hrecon
  have hagree : ∀ e i, i ≠ hidden e → recon.seeds e i = some (committed.seeds e i) := by
    intro e i hi
    rw [hrseeds]
    simp only [openKey, hi, ↓reduceIte, hkey, hseeds]
    rfl
  rw [hmid] at hmidv
  obtain ⟨_, _, hdelta, hwit, hrand, _⟩ := CandidateVerifier.candidateMiddle_evaluates S.signer.xi S.signer.p V.nodes S.encode
    S.signer.randomCount S.signer.enough salt aux hidden recon pa.1 committed.seeds hagree family table ciphers value hmidv
  have hval : (⟨delta, wv, rv, committed.result.lines⟩ : Spec.SignatureComposition.Recomputed F lambda _ _) =
      ⟨(S.encode hidden)⁻¹,
        fun j => algebraMap (ZMod 2) F (aux.witnessCorrection j) + (S.encode hidden)⁻¹ * Spec.BLC.psi S.signer.xi
          (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough aux hidden (Spec.BLC.witnessIndex j)),
        fun j => (S.encode hidden)⁻¹ * Spec.BLC.psi S.signer.xi
          (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough aux hidden
            (Spec.BLC.randomnessIndex j)),
        committed.result.lines⟩ := by
    have h1 : delta = value.1 := congrArg Spec.SignatureComposition.Recomputed.delta hrecovered
    have h2 : wv = value.2.1 := congrArg Spec.SignatureComposition.Recomputed.witness hrecovered
    have h3 : rv = value.2.2.1 := congrArg Spec.SignatureComposition.Recomputed.randomness hrecovered
    rw [h1, h2, h3, hdelta]
    congr 1 <;> funext j
    · exact hwit j
    · exact hrand j
  rw [← hval]
  exact hev

/-- The verification input recomputed from an executed commitment opened at
hidden indices hashes the committed lines digest and the simulator's
coefficient tuple. -/
theorem committed_input (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hlayout : V.layout = S.signer.layout) (hvariant : V.variant = S.signer.variant)
    (hencoding : V.encoding = S.signer.encoding)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes S.encode S.signer.randomCount S.signer.enough)
    (htail : S.signer.linesTail = verifierLinesTail S.signer.encoding)
    (salt root : Bits lambda) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (committed : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (h : Evaluates family table ciphers (commitProgram S.signer salt root witness) committed)
    (piop : Spec.BAVC.Digest lambda) (ctr : Spec.BLCRetry.Counter) (publicKey message : List Bool) :
    let hidden := V.expand piop ctr
    let aux := committed.result.auxiliary
    ∃ recovered, Evaluates family table ciphers
      (Spec.CandidateScheme.verifyProgram V salt aux piop (ctr, openKey committed.result.key hidden)) (Except.ok recovered) ∧
      let input := Spec.SignatureComposition.verificationInput widths S.hdegree S.hsize S.signer.xi S.expandBatching S.H' S.y
        publicKey message ⟨salt, piop, aux, (ctr, ⟨[], fun e => (openKey committed.result.key hidden).hiddenCommitments e⟩),
          (stateOf S salt committed).2.higher⟩ recovered
      input.lines = committed.result.lines ∧ input.coefficients = simulatedCoefficients S salt committed hidden := by
  intro hidden aux
  refine ⟨_, committed_verifies family table ciphers S V hlayout hvariant hencoding hmid htail salt root witness committed h
    piop ctr, ?_⟩
  exact ⟨rfl, rfl⟩

end
end SDitH.Proofs.SimulatedCompleteness
