import SDitH.Spec.CandidateScheme

/-! The named witness-free signing simulator for the candidate scheme. The
abstract scheme wrapper fixes the honest HashPiop query, so the simulator
is a direct scheme whose signing programs the hash table: it commits with
a uniformly random fake witness through the honest commitment program,
samples the HashPiop digest first, runs the candidate retry on it, and
hashes the coefficient tuple that the candidate verifier will recompute
from the simulated transcript (the restored tuple at the inverted
challenge, computed from the committed seeds); it then programs the
digest as the answer at the resulting hash input, or returns a bodiless
signature when that input is already present. The secret key is never
read. This is a candidate algorithm, not a correctness or simulation
claim; its distance from the honest signer is to be proved. -/

namespace SDitH.Spec.CandidateSimulator

open BAVC DomainSeparation HashCipherProgram SharedScheme SharedSigning CandidateBAVC AbstractSignature SignatureSecurity
open PIOPArithmetic (selectorCount)
open CoefficientCompression PIOPComposition BLCSeedLines
open scoped Classical
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]

/-- The coefficient tuple the candidate verifier recomputes from a committed
transcript opened at the hidden indices: the restored tuple at the inverted
challenge of the composed verifier on the affine share values. -/
def simulatedCoefficients (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths) (salt : Bits lambda)
    (committed : SharedSigner.Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hidden : Fin tau → Fin (2 ^ kappa)) : Fin (higherCount + 1) → F :=
  let delta := (S.encode hidden)⁻¹
  let challenge := S.expandBatching committed.result.lines
  let aux := committed.result.auxiliary
  let value := verifierRun widths S.hsize S.signer.xi delta challenge.1 challenge.2 S.H' S.y
    (fun j => algebraMap (ZMod 2) F (aux.witnessCorrection j) + delta * BLC.psi S.signer.xi
      (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough aux hidden (BLC.witnessIndex j)))
    (fun j => delta * BLC.psi S.signer.xi
      (shareMatrix S.signer.p salt committed.seeds S.signer.randomCount S.signer.enough aux hidden (BLC.randomnessIndex j)))
  restoredCoefficients delta value (stateOf S salt committed).2.higher

/-- The simulated signing: fake witness, honest commitment, digest first,
candidate retry, recomputed tuple, programmed answer. -/
def simulatedSign (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths) (publicKey message : List Bool)
    (world : SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    PMF (Signature (Digest lambda)
        (Option (CandidateScheme.Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :=
  (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
    (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
      (PMF.uniformOfFintype (Fin (selectorCount widths * w) → ZMod 2)).bind fun fake =>
        (PMF.uniformOfFintype (Digest lambda)).bind fun digest =>
          (runProgram (SharedSigner.commitBudget tau kappa) (SharedSigner.commitProgram S.signer salt root fake)
              world.other).map fun result =>
            match result.1 with
            | Program.done committed =>
              let state := (stateOf S salt committed).2
              match BLCRetry.observe (CandidateScheme.attempt state.key (S.expandEvaluation digest) S.encode) S.fuel 0 with
              | .returned ctr opening =>
                let hidden := (S.expandEvaluation digest ctr).hidden
                let input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) :=
                  ⟨publicKey, message, (committed.result.lines, simulatedCoefficients S salt committed hidden)⟩
                match world.hashTable input with
                | none => (⟨digest, some (salt, committed.result.auxiliary, (ctr, opening), state.higher)⟩,
                    ⟨Function.update world.hashTable input (some digest), result.2⟩)
                | some _ => (⟨digest, none⟩, ⟨world.hashTable, result.2⟩)
              | _ => (⟨digest, none⟩, ⟨world.hashTable, result.2⟩)
            | _ => (⟨digest, none⟩, ⟨world.hashTable, result.2⟩)

/-- The simulated scheme: the candidate scheme with the simulated signing,
which reads only the public half of the signing key. -/
def simulatedScheme (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2)) :
    Scheme (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
      (Signature (Digest lambda)
        (Option (CandidateScheme.Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)
      (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :=
  { scheme (CandidateScheme.components S V verifyBudget publicKey sampleWitness) with
    sign := fun secret message world => simulatedSign S secret.1 message world }

end
end SDitH.Spec.CandidateSimulator
