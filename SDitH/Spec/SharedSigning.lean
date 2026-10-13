import SDitH.Spec.SharedSigner
import SDitH.Spec.SharedScheme

/-! The abstract signature game's signing services in the shared model:
Algorithm 3 lines 1–6 as uniform salt and root, the executed commitment
program and the PIOP prover, returning the HashPiop payload and the
signer's state; lines 8–9 after HashPiop as Algorithm 11's observed retry
on the returned digest and the parsed body. An observation that does not
return (pending or undefined) yields no body, so such a signature never
verifies; this is a recorded modelling choice, not a source rule. Key
generation is parametrized by the witness sampler at a fixed instance and
public key, with a uniform cipher family and empty tables. The verifier is
the executed `SharedScheme.verifyProgram` on bodies that exist. -/

namespace SDitH.Spec.SharedSigning

open BAVC DomainSeparation HashCipherProgram SharedScheme SharedSigner AbstractSignature
open PIOPArithmetic (selectorCount)
open Batching (blockCount)
open CoefficientCompression (hashedCoefficients transmittedCoefficients)
open PIOPComposition (proverRun)
open Spec.SlopeConsistencyGame (Out)
noncomputable section

variable {lambda tau kappa s wit rnd higherCount : Nat}

/-- Everything of Algorithm 3 before HashPiop except its digest. -/
structure SignedState (F : Type*) [CommRing F] (lambda tau kappa s wit rnd higherCount : Nat) where
  polynomial : Polynomial F
  salt : Bits lambda
  auxiliary : BLCCommit.Auxiliary tau s wit rnd
  key : Key lambda tau (2 ^ kappa)
  higher : Fin higherCount → F

abbrev Payload (F : Type*) (lambda higherCount : Nat) := Digest lambda × (Fin (higherCount + 1) → F)

abbrev Body (F : Type*) (lambda tau s wit rnd higherCount : Nat) :=
  SignatureHashGame.SignatureBody F (BLCCommit.Auxiliary tau s wit rnd) lambda tau higherCount

/-- The signing parameters at a fixed PIOP shape `widths`; the witness and
randomness counts are the source's expressions in `widths`, `w` and lambda. -/
structure SigningSetting (F : Type*) (lambda tau kappa s r k w wpow higherCount : Nat) (widths : List Nat) where
  signer : SignerSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))
  hdegree : widths.length = higherCount + 1
  hsize : PIOPArithmetic.leafCount widths * w = r + k
  expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F)
  H' : Matrix (Fin r) (Fin k) (ZMod 2)
  y : Fin r → ZMod 2
  Topen : Nat
  /-- Algorithm 11's challenge expansion of the digest and counter: an
  explicit parameter, as the literal sampler reads the undefined B. -/
  expandEvaluation : Digest lambda → BLCRetry.Counter → BLCRetry.Challenge tau (2 ^ kappa) wpow
  encode : (Fin tau → Fin (2 ^ kappa)) → F
  /-- The finite observation length of Algorithm 11. -/
  fuel : Nat

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {r k w wpow : Nat} {widths : List Nat}

def defaultState : SignedState F lambda tau kappa s wit rnd higherCount :=
  ⟨0, fun _ => false, ⟨fun _ _ => 0, fun _ => 0, fun _ => 0⟩, ⟨fun _ => fun _ => false, fun _ _ => fun _ => false⟩, fun _ => 0⟩

/-- Algorithm 3 lines 6–7 and the coefficients of line 9 from an executed commitment. -/
def stateOf (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths) (salt : Bits lambda)
    (committed : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    Payload F lambda higherCount ×
      SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount :=
  let challenge := S.expandBatching committed.result.lines
  let p := proverRun widths S.hsize S.signer.xi challenge.1 challenge.2 S.H' S.y committed.result.witness
    committed.result.randomness
  ((committed.result.lines, hashedCoefficients higherCount p),
    ⟨p, salt, committed.result.auxiliary, committed.result.key, transmittedCoefficients higherCount p⟩)

/-- Algorithm 3 lines 1–6: uniform salt and root, the executed commitment
and the prover. The public key and message are consumed by HashPiop in
the abstract game. The second branch is unreachable within the budget. -/
def prepareSigning [NeZero tau] (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (_publicKey : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2) (_message : List Bool)
    (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    PMF (Payload F lambda higherCount ×
      SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount ×
      World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :=
  (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
    (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
      (runProgram (commitBudget tau kappa) (commitProgram S.signer salt root witness) world).map fun result =>
        match result.1 with
        | Program.done committed => ((stateOf S salt committed).1, (stateOf S salt committed).2, result.2)
        | _ => ((fun _ => false, fun _ => 0), defaultState, result.2)

/-- Algorithm 3 lines 8–9 after HashPiop: Algorithm 11 observed on the
digest, then the parsed body; no body when the observation does not return. -/
def openSigning [DecidableEq F] (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (state : SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
    (digest : Digest lambda) (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    PMF (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount) ×
      World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :=
  PMF.pure
    (match BLCRetry.openRandomEvaluation state.key S.Topen (S.expandEvaluation digest) S.encode S.fuel with
      | .returned counter opening => some (state.salt, state.auxiliary, (counter, opening), state.higher)
      | _ => none,
      world)

/-- Verification of a signature with a body is the executed verifier;
without a body it is rejection. -/
def prepareVerification (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) (budget : Nat)
    (publicKey message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    PMF (Option (Payload F lambda higherCount) × World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :=
  match signature.body with
  | none => PMF.pure (none, world)
  | some body => SharedScheme.prepareVerification V budget widths S.hdegree S.hsize S.signer.xi S.expandBatching S.H' S.y
      rfl rfl publicKey message ⟨signature.piop, body⟩ world

/-- A fixed instance and public key, a witness sampler, a uniform cipher
family and empty tables. -/
def keygen (publicKey : List Bool) (sampleWitness : PMF (Fin wit → ZMod 2)) :
    PMF (List Bool × (Fin wit → ZMod 2) × World lambda s wit rnd) :=
  sampleWitness.bind fun witness =>
    (PMF.uniformOfFintype (SharedSlopeGame.CipherFamily lambda)).map fun family =>
      (publicKey, witness, ⟨family, fun _ => none, [], [], []⟩)

/-- The abstract game's components in the shared model. -/
def components [NeZero tau] [DecidableEq F] (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2)) :
    Components (List Bool) (Fin (selectorCount widths * w) → ZMod 2) (List Bool) (Payload F lambda higherCount)
      (Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))
      (SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)
      (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) where
  keygen := keygen publicKey sampleWitness
  prepareSigning := prepareSigning S
  openSigning := openSigning S
  prepareVerification := prepareVerification S V verifyBudget
  publicOracle := publicOracle

end
end SDitH.Spec.SharedSigning
