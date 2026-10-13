import SDitH.Spec.CandidateBAVC
import SDitH.Spec.SharedSigning

/-! The shared-model scheme over the candidate BAVC target. The verifier
runs the candidate reconstruction in place of the literal one, then the
same Hashaux query, middle and Hashlines query. The signer's commitment
phase is unchanged; its opening phase runs Algorithm 11's retry with the
candidate opening of the committed key, whose only retry conditions are
the grinding test and a nonzero merged challenge. The abstract game's
components are assembled as before, with the candidate opening in the
signature body. -/

namespace SDitH.Spec.CandidateScheme

open BAVC DomainSeparation HashCipherProgram SharedScheme SharedSigning CandidateBAVC AbstractSignature
open PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
noncomputable section

variable {lambda tau kappa s wit rnd higherCount : Nat}

/-- Algorithm 4's verification over the candidate reconstruction. -/
def verifyProgram {F : Type*} (V : VerifierSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (aux : BLCCommit.Auxiliary tau s wit rnd) (piop : Digest lambda)
    (decomposition : BLCRetry.Counter × CandidateBAVC.Opening lambda tau (2 ^ kappa)) :
    Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Except (Sum ReconstructionError BLCRecompute.Error) (SignatureComposition.Recomputed F lambda wit rnd)) :=
  HashCipherProgram.bind (CandidateBAVC.reconstruct V.layout V.variant salt (V.expand piop decomposition.1) decomposition.2)
    fun result =>
    match result with
    | Except.error cause => Program.done (Except.error (Sum.inl cause))
    | Except.ok reconstruction =>
        Program.hash (BLCHashChain.auxQuery reconstruction.hcom (BLCHashChain.sourceTail V.encoding aux.corrections))
          fun auxiliary => HashCipherProgram.bind
            (V.middle salt aux (V.expand piop decomposition.1) reconstruction auxiliary.1) fun middle =>
            match middle with
            | Except.error cause => Program.done (Except.error (Sum.inr cause))
            | Except.ok value =>
                Program.hash (BLCHashChain.linesQuery auxiliary.1 (V.encoding.vector aux.plain ++ V.encoding.base value.2.2.2))
                  fun lines => Program.done (Except.ok ⟨value.1, value.2.1, value.2.2.1, lines.1⟩)

abbrev Body (F : Type*) (lambda tau kappa s wit rnd higherCount : Nat) :=
  Bits lambda × BLCCommit.Auxiliary tau s wit rnd × (BLCRetry.Counter × CandidateBAVC.Opening lambda tau (2 ^ kappa)) ×
    (Fin higherCount → F)

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {r k w wpow : Nat} {widths : List Nat}

/-- Algorithm 11's attempt with the candidate opening: the grinding test and
a nonzero merged challenge; the opening itself always succeeds. -/
def attempt [DecidableEq F] (key : Key lambda tau (2 ^ kappa))
    (expand : BLCRetry.Counter → BLCRetry.Challenge tau (2 ^ kappa) wpow) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (ctr : BLCRetry.Counter) : BLCRetry.Attempt (CandidateBAVC.Opening lambda tau (2 ^ kappa)) :=
  let challenge := expand ctr
  if BLCRetry.GrindingPassed challenge.grinding ∧ encode challenge.hidden ≠ 0 then
    .ready (openKey key challenge.hidden)
  else .retry

/-- Algorithm 3 lines 8–9 after HashPiop, with the candidate opening. -/
def openSigning [DecidableEq F] (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (state : SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
    (digest : Digest lambda) (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    PMF (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount) ×
      World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :=
  PMF.pure
    (match BLCRetry.observe (attempt state.key (S.expandEvaluation digest) S.encode) S.fuel 0 with
      | .returned counter opening => some (state.salt, state.auxiliary, (counter, opening), state.higher)
      | _ => none,
      world)

/-- Verification over the candidate reconstruction, on bodies that exist. -/
def prepareVerification (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) (budget : Nat)
    (publicKey message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    PMF (Option (Payload F lambda higherCount) × World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :=
  match signature.body with
  | none => PMF.pure (none, world)
  | some body =>
      (runProgram budget (verifyProgram V body.1 body.2.1 signature.piop body.2.2.1) world).map fun result =>
        (match result.1 with
          | Program.done (Except.ok recovered) =>
              let input := SignatureComposition.verificationInput widths S.hdegree S.hsize S.signer.xi S.expandBatching S.H'
                S.y publicKey message
                ⟨body.1, signature.piop, body.2.1, (body.2.2.1.1, ⟨[], fun e => body.2.2.1.2.hiddenCommitments e⟩), body.2.2.2⟩
                recovered
              some (input.lines, input.coefficients)
          | _ => none,
          result.2)

/-- The abstract game's components over the candidate target. -/
def components [NeZero tau] [DecidableEq F] (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2)) :
    Components (List Bool) (Fin (selectorCount widths * w) → ZMod 2) (List Bool) (Payload F lambda higherCount)
      (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))
      (SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)
      (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) where
  keygen := keygen publicKey sampleWitness
  prepareSigning := SharedSigning.prepareSigning S
  openSigning := openSigning S
  prepareVerification := prepareVerification S V verifyBudget
  publicOracle := publicOracle

end
end SDitH.Spec.CandidateScheme
