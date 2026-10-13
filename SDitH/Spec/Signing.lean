import SDitH.Spec.SignatureComposition
import SDitH.Spec.BLCCommit

/-! Algorithm 3 phases 1–3 with actual BLC commitment, detailed PIOP,
coefficient compression and retry/opening. Phase 0's decoded key, expanded H',
salt and root seed are supplied explicitly. Byte serialization, primitive
implementations and challenge expansion remain the documented function inputs;
no line-degree, witness-constant or successful-opening contract is an input.
-/

namespace SDitH.Spec.Signing

open DomainSeparation PIOPArithmetic SignatureComposition Batching

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

def commitmentRecord {lambda tau kappa s wit rnd : Nat}
    (result : BLCCommit.Result F lambda tau kappa s wit rnd) :
    Commitment F (BLCCommit.Auxiliary tau s wit rnd) lambda tau (2 ^ kappa) wit rnd :=
  ⟨result.witness, result.randomness, result.lines, result.key, result.auxiliary⟩

/-- Phases 1–2, including the real Algorithm-10 commitment. -/
def prepareFromSeeds {r k w lambda tau kappa B higherCount : Nat} [NeZero tau]
    (widths : List Nat) (hdegree : widths.length = higherCount + 1)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (primitives : BLCCommit.Primitives lambda tau kappa (lambda + B)
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F))
    (hashPiop : HashInput F lambda higherCount → Digest lambda)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (publicKey message : List Bool) (salt root : Bits lambda)
    (witness : Fin (selectorCount widths * w) → ZMod 2)
    (randomCount consistencyCount : Nat)
    (hrandom : lambda + B + (selectorCount widths * w + lambda * (widths.length - 1)) ≤ 8 * randomCount)
    (hconsistency : selectorCount widths * w + lambda * (widths.length - 1) ≤ 8 * consistencyCount) :
    Prepared F (BLCCommit.Auxiliary tau (lambda + B) (selectorCount widths * w)
      (lambda * (widths.length - 1))) lambda tau (2 ^ kappa) higherCount :=
  let committed := BLCCommit.commit xi primitives salt root witness randomCount consistencyCount hrandom hconsistency
  prepare widths hdegree hsize xi expandBatching hashPiop H' y publicKey message salt (commitmentRecord committed)

/-- Phases 1–3 after source initialization. `fuel` is only a finite observation
of Algorithm 11, preserving pending execution and unspecified overflow. -/
def signAfterInitialization [DecidableEq F]
    {r k w lambda tau kappa B wpow higherCount : Nat} [NeZero tau]
    (widths : List Nat) (hdegree : widths.length = higherCount + 1)
    (hsize : leafCount widths * w = r + k) (xi : F)
    (primitives : BLCCommit.Primitives lambda tau kappa (lambda + B)
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F))
    (hashPiop : HashInput F lambda higherCount → Digest lambda)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (publicKey message : List Bool) (salt root : Bits lambda)
    (witness : Fin (selectorCount widths * w) → ZMod 2)
    (randomCount consistencyCount : Nat)
    (hrandom : lambda + B + (selectorCount widths * w + lambda * (widths.length - 1)) ≤ 8 * randomCount)
    (hconsistency : selectorCount widths * w + lambda * (widths.length - 1) ≤ 8 * consistencyCount)
    (Topen : Nat)
    (expandEvaluation : Digest lambda → BLCRetry.Counter → BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat) :
    BLCRetry.Observation (Signature F (BLCCommit.Auxiliary tau (lambda + B) (selectorCount widths * w)
      (lambda * (widths.length - 1))) lambda tau higherCount) :=
  observeSigning (prepareFromSeeds widths hdegree hsize xi primitives expandBatching hashPiop H' y
    publicKey message salt root witness randomCount consistencyCount hrandom hconsistency)
    Topen expandEvaluation encode fuel

end
end SDitH.Spec.Signing
