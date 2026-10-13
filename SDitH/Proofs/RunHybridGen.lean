import SDitH.Proofs.RunHybrid

/-! The run hybrid under an abstract counted invariant. The per-call signing
bound is assumed only at worlds satisfying the invariant at a global
budget; the invariant is monotone in its count, grows by one along a
query or a signing call, and is kept by the public oracle, so the run
bound holds when the starting count plus the fuel is within the budget. -/

namespace SDitH.Proofs.RunHybridGen

open Spec.SignatureSecurity
open RunHybrid
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The run hybrid under an abstract counted invariant. -/
theorem run_le_run_add_gen (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : ℝ≥0∞) (B : Nat)
    (Inv : Nat → World HashInput Digest Other → Prop)
    (hmono : ∀ (n m : Nat) (world : World HashInput Digest Other), n ≤ m → Inv n world → Inv m world)
    (hquery : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat)
      (r : Digest × (HashInput → Option Digest)), Inv n world →
      r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps)
    (hpres : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
      (r : Signature × World HashInput Digest Other), Inv n world →
      r ∈ (sch₁.sign sk message world).support → Inv (n + 1) r.2)
    (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
      Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) (m : Nat) (hm : Inv m world) (hB : m + fuel ≤ B)
    (h : Terminal Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    ((run sch₁ adversary fuel pk sk state world trace).bind h) c ≤
      ((run sch₂ adversary fuel pk sk state world trace).bind h) c + fuel * eps := by
  induction fuel generalizing state world trace m with
  | zero =>
    simp only [run, Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  | succ fuel ih =>
    have hstep : (fuel : ℝ≥0∞) * eps ≤ ((fuel + 1 : Nat) : ℝ≥0∞) * eps :=
      mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ fuel)) le_rfl
    simp only [run, PMF.bind_bind]
    refine bind_le_bind_add_const' _ _ _ _ c (fun action _ => ?_)
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
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c + fuel * eps :=
            bind_le_bind_add_const' _ _ _ _ c (fun result hres =>
              ih (next result.1) result.2 _ (m + 1) (hpres sk message world m result hm hres) (by omega))
        _ ≤ (((sch₂.sign sk message world).bind fun result =>
            (run sch₂ adversary fuel pk sk (next result.1) result.2
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c + eps) + fuel * eps :=
            add_le_add_left (hsign sk hsk message world (hmono m B world (by omega) hm) _ c) _
        _ = _ := by push_cast; ring
    | hash input next =>
      dsimp only
      rw [PMF.bind_bind, PMF.bind_bind]
      exact (bind_le_bind_add_const' _ _ _ _ c (fun result hq =>
        ih (next result.1) _ _ (m + 1) (hquery world input m result hm hq) (by omega))).trans
        (add_le_add_right hstep _)
    | query input next =>
      dsimp only
      rw [hagree.publicOracle, PMF.bind_bind, PMF.bind_bind]
      exact (bind_le_bind_add_const' _ _ _ _ c (fun result hr =>
        ih (next result.1) result.2 _ (m + 1) (hpub input world m result hm hr) (by omega))).trans
        (add_le_add_right hstep _)

end
end SDitH.Proofs.RunHybridGen
