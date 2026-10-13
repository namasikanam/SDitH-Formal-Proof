import SDitH.Spec.SignatureSecurity

/-! Replay semantics for the abstract §5.3 chosen-message game. A cut is made
after selecting an adversarial hash action but before answering it. The saved
state includes the honest signing key and world: this is a replay experiment,
not yet a reduction that can answer signing queries without a witness. Later
oracle simulation must remove that dependence; it is not assumed here. -/

namespace SDitH.Spec.SignatureReplay

open SignatureSecurity
noncomputable section
open scoped Classical

structure Snapshot (PublicKey SecretKey Message HashInput Digest Other Query State : Type*) where
  remaining : Nat
  publicKey : PublicKey
  secretKey : SecretKey
  input : HashInput
  next : Digest → State
  world : World HashInput Digest Other
  trace : Trace Message HashInput Query

inductive Cut (PublicKey SecretKey Message Signature HashInput Digest Other Query State : Type*) where
  | ended (terminal : Terminal Message Signature HashInput Digest Other Query)
  | saved (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)

structure Branch (Message Signature HashInput Digest Other Query : Type*) where
  answer : Digest
  checked : Checked Message Signature HashInput Digest Other Query

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- `index` counts adversarial hash requests (including repeated queries),
not honest-service calls. Termination before that index is retained. -/
def cut
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Nat → Nat → PublicKey → SecretKey → State → World HashInput Digest Other →
      Trace Message HashInput Query →
        PMF (Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State)
  | _, 0, _, _, _, _, trace => PMF.pure (.ended (.exhausted trace))
  | index, fuel + 1, pk, sk, state, world, trace => (adversary.step pk state).bind fun action =>
      match action with
      | .abort => PMF.pure (.ended (.aborted trace))
      | .finish message signature =>
          (scheme.prepareVerification pk message signature world).map fun result =>
            .ended (match result.1 with
            | none => .rejected trace
            | some input => .attempt ⟨message, signature, input, scheme.signatureDigest signature,
                result.2, trace⟩)
      | .sign message next => (scheme.sign sk message world).bind fun result =>
          cut scheme adversary index fuel pk sk (next result.1) result.2
            { trace with signingRequests := message :: trace.signingRequests }
      | .hash input next =>
          match index with
          | 0 => PMF.pure (.saved ⟨fuel, pk, sk, input, next, world, trace⟩)
          | index + 1 => (RandomOracle.query world.hashTable input).bind fun result =>
              cut scheme adversary index fuel pk sk (next result.1)
                { world with hashTable := result.2 }
                { trace with hashRequests := input :: trace.hashRequests }
      | .query input next => (scheme.publicOracle input world).bind fun result =>
          cut scheme adversary index fuel pk sk (next result.1) result.2
            { trace with publicRequests := input :: trace.publicRequests }

/-- Resume with the original lazy oracle. Stored queries are never resampled. -/
def resume
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State) :
    PMF (Terminal Message Signature HashInput Digest Other Query) :=
  (RandomOracle.query snapshot.world.hashTable snapshot.input).bind fun result =>
    run scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey
      (snapshot.next result.1) { snapshot.world with hashTable := result.2 }
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }

def complete
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State →
      PMF (Terminal Message Signature HashInput Digest Other Query)
  | .ended terminal => PMF.pure terminal
  | .saved snapshot => resume scheme adversary snapshot

def cutExperiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (index fuel : Nat) :
    PMF (Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State) :=
  scheme.keygen.bind fun generated =>
    (adversary.start generated.1).bind fun state =>
      cut scheme adversary index fuel generated.1 generated.2.1 state generated.2.2 ⟨[], [], []⟩

/-- A continuation with an explicit answer. It is a legitimate fresh-oracle
continuation only when the saved input was absent; the correspondence is proved
under that premise rather than silently overwriting an earlier answer. -/
def continueWith
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (answer : Digest) : PMF (Checked Message Signature HashInput Digest Other Query) :=
  (run scheme adversary snapshot.remaining snapshot.publicKey snapshot.secretKey
    (snapshot.next answer)
    { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
    { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).bind finalize

def freshBranch
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State) :
    PMF (Branch Message Signature HashInput Digest Other Query) :=
  (PMF.uniformOfFintype Digest).bind fun answer =>
    (continueWith scheme adversary snapshot answer).map (fun checked => ⟨answer, checked⟩)

/-- Both copies use the same saved pre-answer state; their answers and future
random choices are sampled independently. Existing inputs explicitly refuse
this fresh-query fork. `none` is a fork-algorithm result, not signature rejection. -/
def forkAt
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State) :
    PMF (Option (Branch Message Signature HashInput Digest Other Query ×
      Branch Message Signature HashInput Digest Other Query)) :=
  match snapshot.world.hashTable snapshot.input with
  | some _ => PMF.pure none
  | none => (freshBranch scheme adversary snapshot).bind fun left =>
      (freshBranch scheme adversary snapshot).map fun right => some (left, right)

def targetWin (input : HashInput) (branch : Branch Message Signature HashInput Digest Other Query) : Bool :=
  branch.checked.wins && match branch.checked.terminal with
    | .attempt a => decide (a.input = input)
    | _ => false

def forkWins (input : HashInput) :
    Option (Branch Message Signature HashInput Digest Other Query ×
      Branch Message Signature HashInput Digest Other Query) → Bool
  | none => false
  | some (left, right) => targetWin input left && targetWin input right &&
      decide (left.answer ≠ right.answer)

/-- One target-winning continuation at an actually reached fresh cut. A cut
that is never reached or names a stored input contributes zero success. -/
def singleAtCut
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State → PMF Bool
  | .ended _ => PMF.pure false
  | .saved snapshot =>
      match snapshot.world.hashTable snapshot.input with
      | some _ => PMF.pure false
      | none => (freshBranch scheme adversary snapshot).map (targetWin snapshot.input)

def forkAtCut
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State → PMF Bool
  | .ended _ => PMF.pure false
  | .saved snapshot => (forkAt scheme adversary snapshot).map (forkWins snapshot.input)

def singleExperiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (index fuel : Nat) : PMF Bool :=
  (cutExperiment scheme adversary index fuel).bind (singleAtCut scheme adversary)

/-- Actual random prefix followed by the defined two-continuation fork. The
honest signing secret is still used; this is not yet a witness-free simulator. -/
def forkExperiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (index fuel : Nat) : PMF Bool :=
  (cutExperiment scheme adversary index fuel).bind (forkAtCut scheme adversary)

end
end SDitH.Spec.SignatureReplay
