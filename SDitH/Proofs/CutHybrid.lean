import SDitH.Proofs.RunHybrid
import SDitH.Spec.SignatureReplay

/-! The hybrid over signing calls of the cut run, the continuation, the
fresh branch, the fork and the cut experiment. Each is a run or a bind of
runs of two schemes agreeing off signing, so each is within a multiple of
the per-call bound: the cut within the fuel, the continuation and a
fresh branch within the snapshot's remaining fuel, the fork within twice
it, and the cut experiment within the fuel for good generated keys. -/

namespace SDitH.Proofs.CutHybrid

open Spec.SignatureSecurity Spec.SignatureReplay
open RunHybrid
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : ℝ≥0∞)
  (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other)
    (h : Signature × World HashInput Digest Other → PMF C) (c : C),
    ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps)

include hagree hsign in
/-- The cut hybrid: the cut runs are within the fuel times the bound. -/
theorem cut_le_cut_add (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State)
    (world : World HashInput Digest Other) (trace : Trace Message HashInput Query)
    (h : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State → PMF C) (c : C) :
    ((cut sch₁ adversary index fuel pk sk state world trace).bind h) c ≤
      ((cut sch₂ adversary index fuel pk sk state world trace).bind h) c + fuel * eps := by
  induction fuel generalizing index state world trace with
  | zero =>
    simp only [cut, Nat.cast_zero, zero_mul, add_zero]
    exact le_rfl
  | succ fuel ih =>
    have hstep : (fuel : ℝ≥0∞) * eps ≤ ((fuel + 1 : Nat) : ℝ≥0∞) * eps :=
      mul_le_mul' (Nat.cast_le.mpr (Nat.le_succ fuel)) le_rfl
    simp only [cut, PMF.bind_bind]
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
            (cut sch₂ adversary index fuel pk sk (next result.1) result.2
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c + fuel * eps :=
            bind_le_bind_add_const' _ _ _ _ c (fun result _ => ih index (next result.1) result.2 _)
        _ ≤ (((sch₂.sign sk message world).bind fun result =>
            (cut sch₂ adversary index fuel pk sk (next result.1) result.2
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c + eps) + fuel * eps :=
            add_le_add_left (hsign sk hsk message world _ c) _
        _ = _ := by push_cast; ring
    | hash input next =>
      dsimp only
      cases index with
      | zero =>
        dsimp only
        exact le_self_add
      | succ index =>
        dsimp only
        rw [PMF.bind_bind, PMF.bind_bind]
        exact (bind_le_bind_add_const' _ _ _ _ c (fun result _ => ih index (next result.1) _ _)).trans
          (add_le_add_right hstep _)
    | query input next =>
      dsimp only
      rw [hagree.publicOracle, PMF.bind_bind, PMF.bind_bind]
      exact (bind_le_bind_add_const' _ _ _ _ c (fun result _ => ih index (next result.1) result.2 _)).trans
        (add_le_add_right hstep _)

include hagree hsign in
/-- The continuation hybrid: within the snapshot's remaining fuel times the
bound. -/
theorem continueWith_le (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hsk : Good snapshot.secretKey) (answer : Digest)
    (h : Checked Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    ((continueWith sch₁ adversary snapshot answer).bind h) c ≤
      ((continueWith sch₂ adversary snapshot answer).bind h) c + snapshot.remaining * eps := by
  unfold continueWith
  rw [PMF.bind_bind, PMF.bind_bind]
  exact run_le_run_add sch₁ sch₂ adversary hagree Good eps hsign snapshot.remaining _ _ hsk _ _ _ _ c

include hagree hsign in
/-- The fresh-branch hybrid: within the snapshot's remaining fuel times the
bound. -/
theorem freshBranch_le (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hsk : Good snapshot.secretKey) (h : Branch Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    ((freshBranch sch₁ adversary snapshot).bind h) c ≤
      ((freshBranch sch₂ adversary snapshot).bind h) c + snapshot.remaining * eps := by
  unfold freshBranch
  rw [PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_const' _ _ _ _ c (fun answer _ => ?_)
  rw [PMF.bind_map, PMF.bind_map]
  exact continueWith_le sch₁ sch₂ adversary hagree Good eps hsign snapshot hsk answer _ c

include hagree hsign in
/-- The fork hybrid: within twice the snapshot's remaining fuel times the
bound. -/
theorem forkAt_le (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hsk : Good snapshot.secretKey)
    (h : Option (Branch Message Signature HashInput Digest Other Query × Branch Message Signature HashInput Digest Other Query) →
      PMF C) (c : C) :
    ((forkAt sch₁ adversary snapshot).bind h) c ≤
      ((forkAt sch₂ adversary snapshot).bind h) c + 2 * snapshot.remaining * eps := by
  unfold forkAt
  cases hlook : snapshot.world.hashTable snapshot.input with
  | some d =>
    dsimp only
    exact le_self_add
  | none =>
    dsimp only
    rw [PMF.bind_bind, PMF.bind_bind]
    calc _ ≤ ((freshBranch sch₁ adversary snapshot).bind fun left =>
          ((freshBranch sch₂ adversary snapshot).map fun right => some (left, right)).bind h) c +
            snapshot.remaining * eps :=
          bind_le_bind_add_const' _ _ _ _ c (fun left _ => by
            rw [PMF.bind_map, PMF.bind_map]
            exact freshBranch_le sch₁ sch₂ adversary hagree Good eps hsign snapshot hsk _ c)
      _ ≤ (((freshBranch sch₂ adversary snapshot).bind fun left =>
          ((freshBranch sch₂ adversary snapshot).map fun right => some (left, right)).bind h) c +
            snapshot.remaining * eps) + snapshot.remaining * eps :=
          add_le_add_left (freshBranch_le sch₁ sch₂ adversary hagree Good eps hsign snapshot hsk _ c) _
      _ = _ := by ring

include hagree hsign in
/-- The cut-experiment hybrid: within the fuel times the bound, for good
generated keys. -/
theorem cutExperiment_le (hgood : ∀ generated ∈ sch₁.keygen.support, Good generated.2.1) (index fuel : Nat)
    (h : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State → PMF C) (c : C) :
    ((cutExperiment sch₁ adversary index fuel).bind h) c ≤
      ((cutExperiment sch₂ adversary index fuel).bind h) c + fuel * eps := by
  unfold cutExperiment
  rw [← hagree.keygen, PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_const' _ _ _ _ c (fun generated hg => ?_)
  rw [PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_const' _ _ _ _ c (fun state _ => ?_)
  exact cut_le_cut_add sch₁ sch₂ adversary hagree Good eps hsign index fuel _ _ (hgood generated hg) state _ _ h c

end
end SDitH.Proofs.CutHybrid
