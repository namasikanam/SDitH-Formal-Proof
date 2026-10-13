import SDitH.Spec.AbstractSignature
import SDitH.Spec.SignatureHashGame
import SDitH.Spec.SharedSlopeExec
import SDitH.Spec.BLCReconstructionChain

/-! The abstract signature game's other-state instantiated by the shared
hash/cipher/mask world, with Algorithm 4's verification as an executed
oracle program: the complete ordered Algorithm-9 reconstruction, the
Hashaux/Hashlines chain, and an explicit verifier middle program for lines
9–21 of Algorithm 12. That middle program is a parameter: the literal lines
read undeclared names and line 21 is ill typed, so no definite verifier is
selected here. The honest signing services are likewise parameters, to be
supplied by a signer program in a later step. The adversary's public
oracle answers hash queries by the digest component, mask queries by the
matrix component and cipher queries by the block. -/

namespace SDitH.Spec.SharedScheme

open BAVC DomainSeparation AbstractSignature HashCipherProgram
open SignatureComposition (Recomputed)
open Spec.SlopeConsistencyGame (Out)
open scoped Classical
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The private other-state: hidden family, lazy table, both histories and the fresh-query log. -/
structure World (lambda s wit rnd : Nat) where
  family : SharedSlopeGame.CipherFamily lambda
  hashTable : List Bool → Option (Out lambda s wit rnd)
  hashHistory : List (List Bool × Out lambda s wit rnd)
  cipherHistory : SharedSlopeGame.History lambda
  trace : List (RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))

inductive Query (lambda : Nat) where
  | hash (input : List Bool)
  | mask (input : List Bool)
  | cipher (request : IdealCipher.Query (Bits lambda) (Bits lambda))

inductive Answer (lambda s wit rnd : Nat) where
  | digest (value : Digest lambda)
  | mask (value : SlopeConsistencyGame.Mask s wit rnd)
  | block (value : Bits lambda)

/-- Run a mixed program on the world with a given budget, returning the final
program state and the updated world. -/
def runProgram {A : Type*} (budget : Nat) (program : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (world : World lambda s wit rnd) :
    PMF (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A × World lambda s wit rnd) :=
  (HashCipherTrace.runFixed procedure world.family budget program world.hashTable world.hashHistory
    world.cipherHistory world.trace).map fun out =>
    (out.state, ⟨world.family, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩)

/-- One public query, answered by the matching component. -/
def publicOracle (query : Query lambda) (world : World lambda s wit rnd) :
    PMF (Answer lambda s wit rnd × World lambda s wit rnd) :=
  match query with
  | .hash input => (runProgram 1 (.hash input fun answer => .done answer.1) world).map fun result =>
      (.digest (match result.1 with | .done value => value | _ => fun _ => false), result.2)
  | .mask input => (runProgram 1 (.hash input fun answer => .done answer.2) world).map fun result =>
      (.mask (match result.1 with | .done value => value | _ => 0), result.2)
  | .cipher request => (runProgram 1 (.cipher request fun answer => .done answer) world).map fun result =>
      (.block (match result.1 with | .done value => value | _ => fun _ => false), result.2)

/-- The verifier's computation between Hashaux and Hashlines, lines 9–21 of
Algorithm 12, as an explicit parameter: given the reconstruction and the
auxiliary digest it returns delta, the recomputed witness/randomness values
and the base matrix, or an error. No definite implementation is selected. -/
abbrev VerifierMiddle (F : Type*) (lambda tau kappa s wit rnd : Nat) :=
  Bits lambda → BLCCommit.Auxiliary tau s wit rnd → (Fin tau → Fin (2 ^ kappa)) →
    Reconstructed lambda tau (2 ^ kappa) → Digest lambda →
    Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Except BLCRecompute.Error (F × (Fin wit → F) × (Fin rnd → F) × (Fin s → Fin tau → Fin kappa → ZMod 2)))

structure VerifierSetting (F : Type*) (lambda tau kappa s wit rnd : Nat) where
  layout : BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)
  variant : Grinding
  Topen : Nat
  encoding : ConcreteBLC.Serialization tau kappa s
  middle : VerifierMiddle F lambda tau kappa s wit rnd
  middleBudget : Nat
  /-- The hidden-index expansion of the transmitted digest and counter: an
  explicit parameter, since the literal sampler reads the undefined B. -/
  expand : Digest lambda → BLCRetry.Counter → Fin tau → Fin (2 ^ kappa)
  nodes : NodesBinding lambda tau (2 ^ kappa)

/-- A digest-answered program run on the product-valued oracle reads the
digest component of each answer. -/
def liftFirst {A : Type*} : Program (List Bool) (Digest lambda) (Bits lambda) (Bits lambda) A →
    Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A
  | Program.done value => Program.done value
  | Program.hash input next => Program.hash input fun answer => liftFirst (next answer.1)
  | Program.cipher request next => Program.cipher request fun answer => liftFirst (next answer)

/-- Reconstruction, then the Hashaux query, the supplied middle, and the
Hashlines query, returning Algorithm 4's recomputed record. The chain
queries are the exact strings of `BLCHashChain`. -/
def verifyProgram {F : Type*} (V : VerifierSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (aux : BLCCommit.Auxiliary tau s wit rnd) (piop : Digest lambda)
    (decomposition : BLCRetry.Counter × Opening lambda tau) :
    Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Except (Sum ReconstructionError BLCRecompute.Error) (Recomputed F lambda wit rnd)) :=
  HashCipherProgram.bind (liftFirst (BAVCReconstructionProgram.reconstruct V.layout V.variant salt
      (V.expand piop decomposition.1) decomposition.2 V.Topen V.nodes)) fun result =>
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

/-- Algorithm 4's final input from an executed verification: the restored
coefficient tuple uses the recomputed record and the transmitted higher
coefficients, exactly as in `SignatureComposition.verificationInput`. -/
def prepareVerification {F : Type*} [Field F] [Algebra (ZMod 2) F] {r k w higherCount : Nat}
    (V : VerifierSetting F lambda tau kappa s wit rnd) (budget : Nat)
    (widths : List Nat) (hdegree : widths.length = higherCount + 1)
    (hsize : PIOPArithmetic.leafCount widths * w = r + k) (xi : F)
    (expandBatching : Digest lambda → (Fin (Batching.blockCount r lambda) → F) × (Fin w → F))
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (hwit : PIOPArithmetic.selectorCount widths * w = wit) (hrnd : lambda * (widths.length - 1) = rnd)
    (publicKey message : List Bool)
    (signature : Signature (Digest lambda) (SignatureHashGame.SignatureBody F (BLCCommit.Auxiliary tau s wit rnd) lambda tau higherCount))
    (world : World lambda s wit rnd) :
    PMF (Option (Digest lambda × (Fin (higherCount + 1) → F)) × World lambda s wit rnd) :=
  (runProgram budget (verifyProgram V signature.body.1 signature.body.2.1 signature.piop signature.body.2.2.1) world).map
    fun result =>
      (match result.1 with
        | Program.done (Except.ok recovered) =>
            let input := SignatureComposition.verificationInput widths hdegree hsize xi expandBatching H' y publicKey message
              ((SignatureHashGame.signatureEquiv F (BLCCommit.Auxiliary tau s wit rnd) lambda tau higherCount) signature)
              (hwit ▸ hrnd ▸ recovered)
            some (input.lines, input.coefficients)
        | _ => none,
        result.2)

end
end SDitH.Spec.SharedScheme
