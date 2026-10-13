import SDitH.Proofs.ChargeRun

/-! The run hybrid with the per-call signing bound stated for the game's
own continuations. The per-call bound over every continuation is not
satisfiable when the signing output carries the hidden path, so the bound
is taken only for continuations of the run's shape: the second scheme's
run from the signing output, then the final evaluation. The hybrid's
proof applies the per-call bound exactly to such continuations. -/

namespace SDitH.Proofs.ChargeRunCont

open Spec.SignatureSecurity
open RunHybrid PrefixFromHead ChargeRun
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The run hybrid with the expected cumulative charge, with the per-call
bound for the run's continuations. -/
theorem run_le_run_add_charge_cont
    (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : World HashInput Digest Other → ℝ≥0∞) (B : Nat)
    (Inv : Nat → World HashInput Digest Other → Prop)
    (hmono : ∀ (n m : Nat) (world : World HashInput Digest Other), n ≤ m → Inv n world → Inv m world)
    (hquery : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat)
      (r : Digest × (HashInput → Option Digest)), Inv n world →
      r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (fuel : Nat) (pk : PublicKey) (next : Signature → State) (trace : Trace Message HashInput Query)
        (h : Terminal Message Signature HashInput Digest Other Query → PMF C) (c : C),
      ((sch₁.sign sk message world).bind fun r => (run sch₂ adversary fuel pk sk (next r.1) r.2 trace).bind h) c ≤
        ((sch₂.sign sk message world).bind fun r => (run sch₂ adversary fuel pk sk (next r.1) r.2 trace).bind h) c +
          eps world)
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
            add_le_add_left (hsign sk hsk message world (hmono m B world (by omega) hm) fuel pk next _ h c) _
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
end SDitH.Proofs.ChargeRunCont
