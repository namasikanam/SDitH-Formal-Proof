import SDitH.Spec.RandomOracle

/-! The adaptive chosen-message experiment described in §5.3, printed p. 44,
with Algorithm 4's final random-oracle equality test explicit. These are abstract
service interfaces, not an instantiation of the source's incomplete algorithms.
They assert no correctness, hiding, soundness, extraction or simulation contract.
The adversary sees the public key and oracle answers, not the secret key, world
or signing-query log. Honest services may use shared oracle state. Establishing
their actual source implementation and allowed table updates remains a proof
obligation. The final table records all earlier evaluations, not just adversary
queries. No table-present event is called extraction or an RSD solution. -/

namespace SDitH.Spec.SignatureSecurity

noncomputable section
open scoped Classical ENNReal

structure World (HashInput Digest Other : Type*) where
  hashTable : HashInput → Option Digest
  other : Other

/-- Complete abstract services. The partial literal source is not silently
converted into such a service. `none` here is a completed verification rejection,
not an undefined operation or exhausted observation of the concrete code. -/
structure Scheme (PublicKey SecretKey Message Signature HashInput Digest Other Query Answer : Type*) where
  keygen : PMF (PublicKey × SecretKey × World HashInput Digest Other)
  sign : SecretKey → Message → World HashInput Digest Other →
    PMF (Signature × World HashInput Digest Other)
  prepareVerification : PublicKey → Message → Signature → World HashInput Digest Other →
    PMF (Option HashInput × World HashInput Digest Other)
  signatureDigest : Signature → Digest
  publicOracle : Query → World HashInput Digest Other → PMF (Answer × World HashInput Digest Other)

inductive Action (Message Signature HashInput Digest Query Answer State : Type*) where
  | finish (message : Message) (signature : Signature)
  | sign (message : Message) (next : Signature → State)
  | hash (input : HashInput) (next : Digest → State)
  | query (input : Query) (next : Answer → State)
  | abort

structure Adversary (PublicKey Message Signature HashInput Digest Query Answer State : Type*) where
  start : PublicKey → PMF State
  step : PublicKey → State → PMF (Action Message Signature HashInput Digest Query Answer State)

structure Trace (Message HashInput Query : Type*) where
  signingRequests : List Message := []
  hashRequests : List HashInput := []
  publicRequests : List Query := []

structure Attempt (Message Signature HashInput Digest Other Query : Type*) where
  message : Message
  signature : Signature
  input : HashInput
  target : Digest
  world : World HashInput Digest Other
  trace : Trace Message HashInput Query

inductive Terminal (Message Signature HashInput Digest Other Query : Type*) where
  | exhausted (trace : Trace Message HashInput Query)
  | aborted (trace : Trace Message HashInput Query)
  | rejected (trace : Trace Message HashInput Query)
  | attempt (value : Attempt Message Signature HashInput Digest Other Query)

structure Checked (Message Signature HashInput Digest Other Query : Type*) where
  terminal : Terminal Message Signature HashInput Digest Other Query
  wins : Bool
  inputWasPresent : Bool

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- One unit of fuel permits one adversary action; finalization is an action.
Fuel is an interaction budget, not a Lean/runtime cost model. Honest-service
internal queries are not claimed to be bounded by this budget. -/
def run
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Nat → PublicKey → SecretKey → State → World HashInput Digest Other →
      Trace Message HashInput Query → PMF (Terminal Message Signature HashInput Digest Other Query)
  | 0, _, _, _, _, trace => PMF.pure (.exhausted trace)
  | fuel + 1, pk, sk, state, world, trace => (adversary.step pk state).bind fun action =>
      match action with
      | .abort => PMF.pure (.aborted trace)
      | .finish message signature =>
          (scheme.prepareVerification pk message signature world).map fun result =>
            match result.1 with
            | none => .rejected trace
            | some input => .attempt ⟨message, signature, input, scheme.signatureDigest signature,
                result.2, trace⟩
      | .sign message next => (scheme.sign sk message world).bind fun result =>
          run scheme adversary fuel pk sk (next result.1) result.2
            { trace with signingRequests := message :: trace.signingRequests }
      | .hash input next => (RandomOracle.query world.hashTable input).bind fun result =>
          run scheme adversary fuel pk sk (next result.1)
            { world with hashTable := result.2 }
            { trace with hashRequests := input :: trace.hashRequests }
      | .query input next => (scheme.publicOracle input world).bind fun result =>
          run scheme adversary fuel pk sk (next result.1) result.2
            { trace with publicRequests := input :: trace.publicRequests }

/-- Repeated signing requests remain in the log. EUF-CMA freshness excludes
every requested message; it is not the stronger new-signature-on-old-message game. -/
def finalize (terminal : Terminal Message Signature HashInput Digest Other Query) :
    PMF (Checked Message Signature HashInput Digest Other Query) :=
  match terminal with
  | .attempt a => (RandomOracle.query a.world.hashTable a.input).map fun result =>
      ⟨terminal, decide (a.message ∉ a.trace.signingRequests ∧ result.1 = a.target),
        (a.world.hashTable a.input).isSome⟩
  | _ => PMF.pure ⟨terminal, false, false⟩

def terminalLaw
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) : PMF (Terminal Message Signature HashInput Digest Other Query) :=
  scheme.keygen.bind fun generated =>
    (adversary.start generated.1).bind fun state =>
      run scheme adversary fuel generated.1 generated.2.1 state generated.2.2 ⟨[], [], []⟩

def experiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) : PMF (Checked Message Signature HashInput Digest Other Query) :=
  (terminalLaw scheme adversary fuel).bind finalize

def advantage
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) : ℝ≥0∞ :=
  ((experiment scheme adversary fuel).map Checked.wins) true

end
end SDitH.Spec.SignatureSecurity
