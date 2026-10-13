import SDitH.Proofs.RunHybrid
import SDitH.Proofs.TableSupport

/-! The run hybrid under the table-support invariant. The per-call signing
bound is assumed only at worlds whose hash table is supported by at most
a global budget; the invariant is carried along the run (a query or a
signing call adds at most one input, the public oracle and verification
leave the table), so the run bound holds when the starting support plus
the fuel is within the budget. -/

namespace SDitH.Proofs.RunHybridInv

open Spec.SignatureSecurity
open RunHybrid TableSupport
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The run hybrid under the table-support invariant. -/
theorem run_le_run_add_inv (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : ℝ≥0∞) (B : Nat)
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Supported world.hashTable B → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps)
    (hpres : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
      (r : Signature × World HashInput Digest Other), Supported world.hashTable n →
      r ∈ (sch₁.sign sk message world).support → Supported r.2.hashTable (n + 1))
    (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (r : Answer × World HashInput Digest Other),
      r ∈ (sch₂.publicOracle query world).support → r.2.hashTable = world.hashTable)
    (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State) (world : World HashInput Digest Other)
    (trace : Trace Message HashInput Query) (m : Nat) (hm : Supported world.hashTable m) (hB : m + fuel ≤ B)
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
            add_le_add_left (hsign sk hsk message world (supported_mono hm (by omega)) _ c) _
        _ = _ := by push_cast; ring
    | hash input next =>
      dsimp only
      rw [PMF.bind_bind, PMF.bind_bind]
      exact (bind_le_bind_add_const' _ _ _ _ c (fun result hq =>
        ih (next result.1) _ _ (m + 1) (supported_query hm input result hq) (by omega))).trans
        (add_le_add_right hstep _)
    | query input next =>
      dsimp only
      rw [hagree.publicOracle, PMF.bind_bind, PMF.bind_bind]
      exact (bind_le_bind_add_const' _ _ _ _ c (fun result hr =>
        ih (next result.1) result.2 _ m (by rw [hpub input world result hr]; exact hm) (by omega))).trans
        (add_le_add_right hstep _)

end
end SDitH.Proofs.RunHybridInv
