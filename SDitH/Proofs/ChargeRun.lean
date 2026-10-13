import SDitH.Proofs.RunHybridGen

/-! The run hybrid with a world-dependent signing charge. The per-call
signing bound may depend on the world at the call (a bound that holds
only on average over the hidden cipher family cannot be a constant at
every world), so the hybrid charges the current world's term at every
signing query and sums the charges in expectation along the run. The run
bound then holds with the expected cumulative charge in place of the fuel
times a constant; the constant form is the special case of a constant
charge. -/

namespace SDitH.Proofs.ChargeRun

open Spec.SignatureSecurity
open RunHybrid PrefixFromHead
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The expected cumulative signing charge along a run: the charge of the
current world at every signing query, averaged over the run's choices. -/
def charge (eps : World HashInput Digest Other → ℝ≥0∞)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Nat → PublicKey → SecretKey → State → World HashInput Digest Other → Trace Message HashInput Query → ℝ≥0∞
  | 0, _, _, _, _, _ => 0
  | fuel + 1, pk, sk, state, world, trace => ∑' action, (adversary.step pk state) action *
      match action with
      | .abort => 0
      | .finish _ _ => 0
      | .sign message next => eps world + ∑' r, (sch.sign sk message world) r *
          charge eps sch adversary fuel pk sk (next r.1) r.2
            { trace with signingRequests := message :: trace.signingRequests }
      | .hash input next => ∑' r, (Spec.RandomOracle.query world.hashTable input) r *
          charge eps sch adversary fuel pk sk (next r.1) { world with hashTable := r.2 }
            { trace with hashRequests := input :: trace.hashRequests }
      | .query input next => ∑' r, (sch.publicOracle input world) r *
          charge eps sch adversary fuel pk sk (next r.1) r.2
            { trace with publicRequests := input :: trace.publicRequests }

/-- The run hybrid with the expected cumulative charge: with a per-call
signing bound under continuations whose term depends on the world, at
worlds satisfying a counted invariant within the budget, the runs are
within the expected cumulative charge of the first scheme's run. -/
theorem run_le_run_add_charge (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : World HashInput Digest Other → ℝ≥0∞) (B : Nat)
    (Inv : Nat → World HashInput Digest Other → Prop)
    (hmono : ∀ (n m : Nat) (world : World HashInput Digest Other), n ≤ m → Inv n world → Inv m world)
    (hquery : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat)
      (r : Digest × (HashInput → Option Digest)), Inv n world →
      r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps world)
    (hpres : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
      (r : Signature × World HashInput Digest Other), Inv n world →
      r ∈ (sch₁.sign sk message world).support → Inv (n + 1) r.2)
    (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
      Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) (m : Nat) (hm : Inv m world) (hB : m + fuel ≤ B)
    (h : Terminal Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    ((run sch₁ adversary fuel pk sk state world trace).bind h) c ≤
      ((run sch₂ adversary fuel pk sk state world trace).bind h) c +
        charge eps sch₁ adversary fuel pk sk state world trace := by
  induction fuel generalizing state world trace m with
  | zero =>
    simp only [run, charge, add_zero]
    exact le_rfl
  | succ fuel ih =>
    simp only [run, charge, PMF.bind_bind]
    refine bind_le_bind_add_cost _ _ _ _ c (fun action _ => ?_)
    cases action with
    | abort =>
      dsimp only
      exact le_self_add
    | finish message signature =>
      dsimp only
      rw [hagree.prepareVerification, hagree.signatureDigest]
      exact le_self_add
    | sign message next =>
      dsimp only
      rw [PMF.bind_bind, PMF.bind_bind]
      calc _ ≤ ((sch₁.sign sk message world).bind fun result =>
            (run sch₂ adversary fuel pk sk (next result.1) result.2
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c +
            ∑' r, (sch₁.sign sk message world) r * charge eps sch₁ adversary fuel pk sk (next r.1) r.2
              { trace with signingRequests := message :: trace.signingRequests } :=
            bind_le_bind_add_cost _ _ _ _ c (fun result hres =>
              ih (next result.1) result.2 _ (m + 1) (hpres sk message world m result hm hres) (by omega))
        _ ≤ (((sch₂.sign sk message world).bind fun result =>
            (run sch₂ adversary fuel pk sk (next result.1) result.2
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c + eps world) +
            ∑' r, (sch₁.sign sk message world) r * charge eps sch₁ adversary fuel pk sk (next r.1) r.2
              { trace with signingRequests := message :: trace.signingRequests } :=
            add_le_add_left (hsign sk hsk message world (hmono m B world (by omega) hm) _ c) _
        _ = _ := by rw [add_assoc]
    | hash input next =>
      dsimp only
      rw [PMF.bind_bind, PMF.bind_bind]
      exact bind_le_bind_add_cost _ _ _ _ c (fun result hq =>
        ih (next result.1) _ _ (m + 1) (hquery world input m result hm hq) (by omega))
    | query input next =>
      dsimp only
      rw [hagree.publicOracle, PMF.bind_bind, PMF.bind_bind]
      exact bind_le_bind_add_cost _ _ _ _ c (fun result hr =>
        ih (next result.1) result.2 _ (m + 1) (hpub input world m result hm hr) (by omega))

end
end SDitH.Proofs.ChargeRun
