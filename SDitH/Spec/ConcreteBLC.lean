import SDitH.Spec.BLCCommit
import SDitH.Spec.PRG

/-! Algorithm 10's primitive family using the actual Table-1 ciphers, SHAKE
and ciphertext byte stream. Structured binary-vector/matrix serialization is
still an explicit boundary; the source's top-level hash component order and
domain prefixes are fixed here.

The stream is a mathematical concatenation of cipher outputs. In Category III
it does not resolve Algorithm 6's inconsistent finite Parse assignment. Proofs
relating this family to successful finite PRG calls carry those obligations.
No cryptographic or serializer correctness contract is assumed.
-/

namespace SDitH.Spec.ConcreteBLC

open DomainSeparation FieldRepresentation

/-- Unspecified wire encodings, separate from hashes and cipher bodies.
`vector` is applied separately to each positive-index correction, in order.
`base` leaves the matrix's byte/bit layout explicitly supplied. -/
structure Serialization (tau kappa s : Nat) where
  vector : {n : Nat} → (Fin n → ZMod 2) → List Bool
  base : (Fin s → Fin tau → Fin kappa → ZMod 2) → List Bool

def auxPayload {category : Category} {tau kappa s wit rnd : Nat}
    (encoding : Serialization tau kappa s)
    (input : BLCCommit.AuxHashInput (width category) tau (s + (wit + rnd))) : List Bool :=
  List.ofFn input.commitment ++ (List.ofFn fun j => encoding.vector (input.corrections j)).flatten

def linesPayload {category : Category} {tau kappa s wit : Nat}
    (encoding : Serialization tau kappa s)
    (input : BLCCommit.LinesHashInput (width category) tau kappa s wit) : List Bool :=
  List.ofFn input.auxiliary ++ encoding.vector input.plain ++
    encoding.base input.base ++ encoding.vector input.witnessCorrection

/-- Zero outside the source's 8-bit execution-tweak input range is only a
total extension for the existing Nat-indexed interface. It is never used by
the submitted execution loops; the corresponding range proof is separate. -/
def executionStream (category : Category) (variant : Grinding)
    (seed salt : Bits (width category)) (execution : Nat) : Nat → Byte :=
  if h : execution < 256 then
    PRG.stream category seed (tweakSalt variant salt (PRG.shiftedTweak ⟨execution, h⟩) false)
  else fun _ => 0

def primitives (category : Category) (variant : Grinding) {tau kappa s wit rnd : Nat}
    (encoding : Serialization tau kappa s) : BLCCommit.Primitives (width category) tau kappa s wit rnd where
  grinding := variant
  encStar := CipherPrimitives.encStar category
  hash := SHAKE.hash category
  prg := executionStream category variant
  xof := HashPrimitives.digestXOF category
  hashAux := fun input => HashPrimitives.domainHash category 2 (auxPayload encoding input)
  hashLines := fun input => HashPrimitives.domainHash category 3 (linesPayload encoding input)

end SDitH.Spec.ConcreteBLC
