import SDitH.Spec.SignatureSecurity

/-! Abstract Algorithms 2–4 retaining the message-bound HashPiop call and its
position between PIOP preparation and opening. The payload contains commitment
and coefficients; the signature body contains the other transmitted fields.
Components are actual supplied computations, not correctness/security contracts.
Other hash/cipher operations use the Other state. This typed domain separation
requires a source/encoding correspondence proof; it is not asserted about bytes.
In particular this is not yet an instantiation of the incomplete literal scheme. -/

namespace SDitH.Spec.AbstractSignature

open SignatureSecurity
noncomputable section
open scoped Classical

structure HashInput (PublicKey Message Payload : Type*) where
  publicKey : PublicKey
  message : Message
  payload : Payload

structure Signature (Digest Body : Type*) where
  piop : Digest
  body : Body

structure Components (PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer : Type*) where
  keygen : PMF (PublicKey × SecretKey × Other)
  prepareSigning : PublicKey → SecretKey → Message → Other → PMF (Payload × CommitState × Other)
  openSigning : CommitState → Digest → Other → PMF (Body × Other)
  prepareVerification : PublicKey → Message → Signature Digest Body → Other → PMF (Option Payload × Other)
  publicOracle : Query → Other → PMF (Answer × Other)

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- As in the source secret key, the abstract signing key retains its public
key. HashPiop has one query per signing call, at the source's position. -/
def scheme
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer) :
    Scheme PublicKey (PublicKey × SecretKey) Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Other Query Answer where
  keygen := components.keygen.map fun generated =>
    (generated.1, (generated.1, generated.2.1), ⟨fun _ => none, generated.2.2⟩)
  sign := fun secret message world =>
    (components.prepareSigning secret.1 secret.2 message world.other).bind fun prepared =>
      (RandomOracle.query world.hashTable ⟨secret.1, message, prepared.1⟩).bind fun hashResult =>
        (components.openSigning prepared.2.1 hashResult.1 prepared.2.2).map fun opened =>
          (⟨hashResult.1, opened.1⟩, ⟨hashResult.2, opened.2⟩)
  prepareVerification := fun pk message signature world =>
    (components.prepareVerification pk message signature world.other).map fun result =>
      (result.1.map (fun payload => ⟨pk, message, payload⟩), ⟨world.hashTable, result.2⟩)
  signatureDigest := Signature.piop
  publicOracle := fun query world =>
    (components.publicOracle query world.other).map fun result =>
      (result.1, ⟨world.hashTable, result.2⟩)

/-- Every defined final-hash table entry arose from a public adversary query
or a signing call on the entry's message. This is a predicate to be proved
invariant, not a property built into the oracle/algorithm type. -/
def Accounted
    (table : HashInput PublicKey Message Payload → Option Digest)
    (trace : Trace Message (HashInput PublicKey Message Payload) Query) : Prop :=
  ∀ input answer, table input = some answer →
    input ∈ trace.hashRequests ∨ input.message ∈ trace.signingRequests

end
end SDitH.Spec.AbstractSignature
