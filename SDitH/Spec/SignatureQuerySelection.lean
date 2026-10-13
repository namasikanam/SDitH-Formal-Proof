import SDitH.Spec.SignatureReplay

/-! Instrumentation for selecting a useful adversarial HashPiop request.
Each logged request records whether the input was absent immediately before
that request. The chronological log is private experiment instrumentation;
it is not given to the adversary. No oracle/simulation property is assumed. -/

namespace SDitH.Spec.SignatureQuerySelection

open SignatureSecurity SignatureReplay
open scoped Classical
noncomputable section

structure Recorded (Message Signature HashInput Digest Other Query : Type*) where
  terminal : Terminal Message Signature HashInput Digest Other Query
  requests : List (HashInput × Bool)

structure CheckedRecord (Message Signature HashInput Digest Other Query : Type*) where
  checked : Checked Message Signature HashInput Digest Other Query
  requests : List (HashInput × Bool)

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

def prepend (input : HashInput) (fresh : Bool)
    (record : Recorded Message Signature HashInput Digest Other Query) :
    Recorded Message Signature HashInput Digest Other Query :=
  { record with requests := (input, fresh) :: record.requests }

/-- Same services and choices as run, with a chronological adversarial hash log.
Freshness is observed before querying, rather than inferred from the final table. -/
def record
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Nat → PublicKey → SecretKey → State → World HashInput Digest Other →
      Trace Message HashInput Query → PMF (Recorded Message Signature HashInput Digest Other Query)
  | 0, _, _, _, _, trace => PMF.pure ⟨.exhausted trace, []⟩
  | fuel + 1, pk, sk, state, world, trace => (adversary.step pk state).bind fun action =>
      match action with
      | .abort => PMF.pure ⟨.aborted trace, []⟩
      | .finish message signature =>
          (scheme.prepareVerification pk message signature world).map fun result =>
            ⟨match result.1 with
              | none => .rejected trace
              | some input => .attempt ⟨message, signature, input, scheme.signatureDigest signature,
                  result.2, trace⟩, []⟩
      | .sign message next => (scheme.sign sk message world).bind fun result =>
          record scheme adversary fuel pk sk (next result.1) result.2
            { trace with signingRequests := message :: trace.signingRequests }
      | .hash input next => (RandomOracle.query world.hashTable input).bind fun result =>
          (record scheme adversary fuel pk sk (next result.1)
            { world with hashTable := result.2 }
            { trace with hashRequests := input :: trace.hashRequests }).map
              (prepend input (world.hashTable input).isNone)
      | .query input next => (scheme.publicOracle input world).bind fun result =>
          record scheme adversary fuel pk sk (next result.1) result.2
            { trace with publicRequests := input :: trace.publicRequests }

def finalizeRecord (record : Recorded Message Signature HashInput Digest Other Query) :
    PMF (CheckedRecord Message Signature HashInput Digest Other Query) :=
  (finalize record.terminal).map fun checked => ⟨checked, record.requests⟩

def marked (index : Nat) (record : CheckedRecord Message Signature HashInput Digest Other Query) : Bool :=
  record.checked.wins && match record.requests[index]?, record.checked.terminal with
    | some (input, true), .attempt a => decide (a.input = input)
    | _, _ => false

def checkedTarget (input : HashInput) (checked : Checked Message Signature HashInput Digest Other Query) : Bool :=
  checked.wins && match checked.terminal with
    | .attempt a => decide (a.input = input)
    | _ => false

def selectedRecord (index : Nat) (record : Recorded Message Signature HashInput Digest Other Query) : PMF Bool :=
  (finalizeRecord record).map (marked index)

def recordedExperiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) : PMF (CheckedRecord Message Signature HashInput Digest Other Query) :=
  scheme.keygen.bind fun generated =>
    (adversary.start generated.1).bind fun state =>
      (record scheme adversary fuel generated.1 generated.2.1 state generated.2.2 ⟨[], [], []⟩).bind finalizeRecord

/-- Select an index uniformly before running an experiment with fuel+1 actions.
An index beyond the requests actually made yields an ended cut and zero success. -/
def randomCutExperiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) :
    PMF (Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State) :=
  (PMF.uniformOfFintype (Fin (fuel + 1))).bind fun index =>
    cutExperiment scheme adversary index.val (fuel + 1)

def randomSingleExperiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) : PMF Bool :=
  (randomCutExperiment scheme adversary fuel).bind (singleAtCut scheme adversary)

def randomForkExperiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) : PMF Bool :=
  (randomCutExperiment scheme adversary fuel).bind (forkAtCut scheme adversary)

end
end SDitH.Spec.SignatureQuerySelection
