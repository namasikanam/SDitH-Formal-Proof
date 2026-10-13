import SDitH.Spec.SignatureSecurity
import SDitH.Proofs.PrefixFromHead

/-! The hybrid over signing calls of the game's run. Two schemes agreeing
off signing, with a per-call bound under continuations for good secret
keys, give a run bound linear in the fuel: each unit of fuel permits at
most one signing call, and the other actions (abort, finish, hash,
public query) are identical. -/

namespace SDitH.Proofs.RunHybrid

open Spec.SignatureSecurity
open PrefixFromHead
open scoped Classical ENNReal

noncomputable section

section Generic

variable {A B : Type*}

/-- Two continuations within a constant pointwise are within that constant
after a bind. -/
theorem bind_le_bind_add_const' (p : PMF A) (f g : A → PMF B) (c : ℝ≥0∞) (b : B)
    (h : ∀ a ∈ p.support, f a b ≤ g a b + c) : (p.bind f) b ≤ (p.bind g) b + c := by
  have hc := bind_le_bind_add_cost p f g (fun _ => c) b h
  rwa [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul] at hc

end Generic

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- Two schemes agreeing off signing. -/
structure AgreeOffSign
    (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer) : Prop where
  keygen : sch₁.keygen = sch₂.keygen
  prepareVerification : sch₁.prepareVerification = sch₂.prepareVerification
  signatureDigest : sch₁.signatureDigest = sch₂.signatureDigest
  publicOracle : sch₁.publicOracle = sch₂.publicOracle

/-- The run hybrid: with a per-call signing bound under continuations for
good secret keys, the runs are within the fuel times the bound. -/
theorem run_le_run_add (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : ℝ≥0∞)
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other)
      (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) (h : Terminal Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    ((run sch₁ adversary fuel pk sk state world trace).bind h) c ≤
      ((run sch₂ adversary fuel pk sk state world trace).bind h) c + fuel * eps := by
  induction fuel generalizing state world trace with
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
            bind_le_bind_add_const' _ _ _ _ c (fun result _ => ih (next result.1) result.2 _)
        _ ≤ (((sch₂.sign sk message world).bind fun result =>
            (run sch₂ adversary fuel pk sk (next result.1) result.2
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c + eps) + fuel * eps :=
            add_le_add_left (hsign sk hsk message world _ c) _
        _ = _ := by push_cast; ring
    | hash input next =>
      dsimp only
      rw [PMF.bind_bind, PMF.bind_bind]
      exact (bind_le_bind_add_const' _ _ _ _ c (fun result _ => ih (next result.1) _ _)).trans
        (add_le_add_right hstep _)
    | query input next =>
      dsimp only
      rw [hagree.publicOracle, PMF.bind_bind, PMF.bind_bind]
      exact (bind_le_bind_add_const' _ _ _ _ c (fun result _ => ih (next result.1) result.2 _)).trans
        (add_le_add_right hstep _)

end
end SDitH.Proofs.RunHybrid
