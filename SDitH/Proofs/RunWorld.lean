import SDitH.Proofs.ChargeCutExpect

/-! The game run with its final world. The run threaded with its world
returns the terminal and the world at the end; the run is its first
component. Under the oracles' resampling laws (signing, public oracle and
verification preparation), the run with world from a resampled world has
the law of the run followed by a fresh resampling of its final world, with
an attempt's embedded world replaced alike. -/

namespace SDitH.Proofs.RunWorld

open Spec.SignatureSecurity
open GameResample ChargeExpect ChargeCutExpect
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The run with its final world. -/
def runW (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Nat → PublicKey → SecretKey → State → World HashInput Digest Other → Trace Message HashInput Query →
      PMF (Terminal Message Signature HashInput Digest Other Query × World HashInput Digest Other)
  | 0, _, _, _, world, trace => PMF.pure (.exhausted trace, world)
  | fuel + 1, pk, sk, state, world, trace => (adversary.step pk state).bind fun action =>
      match action with
      | .abort => PMF.pure (.aborted trace, world)
      | .finish message signature =>
          (scheme.prepareVerification pk message signature world).map fun result =>
            (match result.1 with
              | none => .rejected trace
              | some input => .attempt ⟨message, signature, input, scheme.signatureDigest signature, result.2, trace⟩,
              result.2)
      | .sign message next => (scheme.sign sk message world).bind fun result =>
          runW scheme adversary fuel pk sk (next result.1) result.2
            { trace with signingRequests := message :: trace.signingRequests }
      | .hash input next => (Spec.RandomOracle.query world.hashTable input).bind fun result =>
          runW scheme adversary fuel pk sk (next result.1)
            { world with hashTable := result.2 }
            { trace with hashRequests := input :: trace.hashRequests }
      | .query input next => (scheme.publicOracle input world).bind fun result =>
          runW scheme adversary fuel pk sk (next result.1) result.2
            { trace with publicRequests := input :: trace.publicRequests }

/-- The run is the first component of the run with world. -/
theorem run_eq_runW (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
      (trace : Trace Message HashInput Query),
      run scheme adversary fuel pk sk state world trace = (runW scheme adversary fuel pk sk state world trace).map Prod.fst := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state world trace
    simp only [run, runW, PMF.pure_map]
  | succ fuel ih =>
    intro pk sk state world trace
    simp only [run, runW, PMF.map_bind]
    congr 1
    funext action
    cases action with
    | abort => simp only [PMF.pure_map]
    | finish message signature =>
      rw [PMF.map_comp]
      rfl
    | sign message next =>
      simp only [PMF.map_bind, ih]
    | hash input next =>
      simp only [PMF.map_bind, ih]
    | query input next =>
      simp only [PMF.map_bind, ih]

/-- A terminal with an attempt's embedded world replaced. -/
def withWorld (t : Terminal Message Signature HashInput Digest Other Query) (world : World HashInput Digest Other) :
    Terminal Message Signature HashInput Digest Other Query :=
  match t with
  | .attempt a => .attempt { a with world := world }
  | t => t

/-- The run with world obeys the resampling law, with an attempt's embedded
world replaced alike. -/
theorem runW_postLaw (res : Other → PMF Other) (hidem : ∀ other, (res other).bind res = res other)
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw res (scheme.sign sk message))
    (hpubLaw : ∀ query : Query, PostLaw res (scheme.publicOracle query))
    (hprepLaw : ∀ (pk : PublicKey) (message : Message) (signature : Signature),
      PostLaw res (scheme.prepareVerification pk message signature)) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
      (trace : Trace Message HashInput Query),
      (resampleW res world).bind (fun w => runW scheme adversary fuel pk sk state w trace) =
        (resampleW res world).bind fun w => (runW scheme adversary fuel pk sk state w trace).bind fun r =>
          (resampleW res r.2).map fun w' => (withWorld r.1 w', w') := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state world trace
    simp only [runW, PMF.pure_bind, withWorld, PMF.map, Function.comp_def]
    rw [resampleW_bind res hidem]
  | succ fuel ih =>
    intro pk sk state world trace
    simp only [runW, PMF.bind_bind]
    rw [PMF.bind_comm]
    conv_rhs => rw [PMF.bind_comm]
    congr 1
    funext action
    cases action with
    | abort =>
      dsimp only
      simp only [PMF.pure_bind, withWorld, PMF.map, Function.comp_def]
      rw [resampleW_bind res hidem]
    | finish message signature =>
      dsimp only
      simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
      conv_lhs => rw [postLaw_bind (hprepLaw pk message signature)]
      congr 1
      funext w
      congr 1
      funext result
      congr 1
      funext w'
      cases result.1 <;> rfl
    | sign message next =>
      dsimp only
      simp only [PMF.bind_bind]
      conv_lhs => rw [postLaw_bind (hsignLaw sk message)]
      conv_rhs => rw [postLaw_bind (hsignLaw sk message)]
      congr 1
      funext w
      congr 1
      funext r
      exact ih pk sk (next r.1) r.2 _
    | hash input next =>
      dsimp only
      simp only [PMF.bind_bind, resampleW, PMF.bind_map, Function.comp_def]
      rw [PMF.bind_comm]
      conv_rhs => rw [PMF.bind_comm]
      congr 1
      funext result
      have h := ih pk sk (next result.1) { world with hashTable := result.2 }
        { trace with hashRequests := input :: trace.hashRequests }
      simp only [resampleW, PMF.bind_map, Function.comp_def] at h
      exact h
    | query input next =>
      dsimp only
      simp only [PMF.bind_bind]
      conv_lhs => rw [postLaw_bind (hpubLaw input)]
      conv_rhs => rw [postLaw_bind (hpubLaw input)]
      congr 1
      funext w
      congr 1
      funext r
      exact ih pk sk (next r.1) r.2 _

end
end SDitH.Proofs.RunWorld
