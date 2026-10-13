import SDitH.Proofs.RunHybridGen
import SDitH.Proofs.CutHybrid
import SDitH.Proofs.EventHybrid

/-! The replay hybrids under an abstract counted invariant. The cut run
carries the invariant like the run; a saved snapshot's world satisfies
it at the starting count plus the cut's fuel; the continuation starts at
the snapshot's world with one programmed input; so the continuation, the
fresh branch, the fork and the cut experiment are within the same
multiples of the per-call bound as before, with the per-call bound
assumed only at worlds satisfying the invariant at the budget. -/

namespace SDitH.Proofs.CutHybridGen

open Spec.SignatureSecurity Spec.SignatureReplay
open RunHybrid RunHybridGen CutHybrid EventHybrid
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

variable (Inv : Nat → World HashInput Digest Other → Prop)
  (hmono : ∀ (n m : Nat) (world : World HashInput Digest Other), n ≤ m → Inv n world → Inv m world)
  (hquery : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat)
    (r : Digest × (HashInput → Option Digest)), Inv n world →
    r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })

section Saved

variable (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hpres : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
    (r : Signature × World HashInput Digest Other), Inv n world →
    r ∈ (sch.sign sk message world).support → Inv (n + 1) r.2)
  (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
    Inv n world → r ∈ (sch.publicOracle query world).support → Inv (n + 1) r.2)

include hmono hquery hpres hpub in
/-- A saved snapshot's world satisfies the invariant at the starting count
plus the cut's fuel. -/
theorem cut_saved_gen :
    ∀ (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (world : World HashInput Digest Other)
      (trace : Trace Message HashInput Query) (m : Nat), Inv m world →
      ∀ (c : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State),
      c ∈ (cut sch adversary index fuel pk sk state world trace).support →
      ∀ snapshot, c = .saved snapshot → Inv (m + fuel) snapshot.world := by
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state world trace m _ c hc snapshot hs
    simp only [cut, PMF.mem_support_pure_iff] at hc
    subst hc
    cases hs
  | succ fuel ih =>
    intro pk sk state world trace m hm c hc snapshot hs
    simp only [cut] at hc
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
    cases action with
    | abort =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst hrest
      cases hs
    | finish message signature =>
      obtain ⟨result, _, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst hres
      cases hr : result.1 with
      | none => rw [hr] at hs; cases hs
      | some input => rw [hr] at hs; cases hs
    | sign message next =>
      obtain ⟨result, hres, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      have := ih index pk sk _ _ _ (m + 1) (hpres sk message world m result hm hres) c hrun snapshot hs
      exact hmono _ _ _ (by omega) this
    | hash input next =>
      cases index with
      | zero =>
        simp only [PMF.mem_support_pure_iff] at hrest
        subst hrest
        cases hs
        exact hmono _ _ _ (by omega) hm
      | succ index =>
        obtain ⟨result, hq, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
        have := ih index pk sk _ _ _ (m + 1) (hquery world input m result hm hq) c hrun snapshot hs
        exact hmono _ _ _ (by omega) this
    | query input next =>
      obtain ⟨result, hr, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      have := ih index pk sk _ _ _ (m + 1) (hpub input world m result hm hr) c hrun snapshot hs
      exact hmono _ _ _ (by omega) this

end Saved

variable (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : ℝ≥0∞) (B : Nat)
  (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
    Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
    ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps)
  (hpres : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
    (r : Signature × World HashInput Digest Other), Inv n world →
    r ∈ (sch₁.sign sk message world).support → Inv (n + 1) r.2)
  (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
    Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
  (hupdate : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat) (d : Digest), Inv n world →
    Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) })

include hmono hquery hagree hsign hpres hpub in
/-- The cut hybrid under the invariant. -/
theorem cut_le_cut_add_gen (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State)
    (world : World HashInput Digest Other) (trace : Trace Message HashInput Query) (m : Nat)
    (hm : Inv m world) (hB : m + fuel ≤ B)
    (h : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State → PMF C) (c : C) :
    ((cut sch₁ adversary index fuel pk sk state world trace).bind h) c ≤
      ((cut sch₂ adversary index fuel pk sk state world trace).bind h) c + fuel * eps := by
  induction fuel generalizing index state world trace m with
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
            bind_le_bind_add_const' _ _ _ _ c (fun result hres =>
              ih index (next result.1) result.2 _ (m + 1) (hpres sk message world m result hm hres) (by omega))
        _ ≤ (((sch₂.sign sk message world).bind fun result =>
            (cut sch₂ adversary index fuel pk sk (next result.1) result.2
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c + eps) + fuel * eps :=
            add_le_add_left (hsign sk hsk message world (hmono m B world (by omega) hm) _ c) _
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
        exact (bind_le_bind_add_const' _ _ _ _ c (fun result hq =>
          ih index (next result.1) _ _ (m + 1) (hquery world input m result hm hq) (by omega))).trans
          (add_le_add_right hstep _)
    | query input next =>
      dsimp only
      rw [hagree.publicOracle, PMF.bind_bind, PMF.bind_bind]
      exact (bind_le_bind_add_const' _ _ _ _ c (fun result hr =>
        ih index (next result.1) result.2 _ (m + 1) (hpub input world m result hm hr) (by omega))).trans
        (add_le_add_right hstep _)

include hmono hquery hagree hsign hpres hpub hupdate in
/-- The continuation hybrid under the invariant: the snapshot's world with
one programmed input. -/
theorem continueWith_le_gen (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world)
    (hB : m + 1 + snapshot.remaining ≤ B) (answer : Digest)
    (h : Checked Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    ((continueWith sch₁ adversary snapshot answer).bind h) c ≤
      ((continueWith sch₂ adversary snapshot answer).bind h) c + snapshot.remaining * eps := by
  unfold continueWith
  rw [PMF.bind_bind, PMF.bind_bind]
  exact run_le_run_add_gen sch₁ sch₂ adversary hagree Good eps B Inv hmono hquery hsign hpres hpub snapshot.remaining _ _
    hsk _ _ _ (m + 1) (hupdate snapshot.world snapshot.input m answer hm) (by omega) _ c

include hmono hquery hagree hsign hpres hpub hupdate in
/-- The fresh-branch hybrid under the invariant. -/
theorem freshBranch_le_gen (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world)
    (hB : m + 1 + snapshot.remaining ≤ B) (h : Branch Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    ((freshBranch sch₁ adversary snapshot).bind h) c ≤
      ((freshBranch sch₂ adversary snapshot).bind h) c + snapshot.remaining * eps := by
  unfold freshBranch
  rw [PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_const' _ _ _ _ c (fun answer _ => ?_)
  rw [PMF.bind_map, PMF.bind_map]
  exact continueWith_le_gen Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hsign hpres hpub hupdate snapshot hsk m
    hm hB answer _ c

include hmono hquery hagree hsign hpres hpub hupdate in
/-- The fork hybrid under the invariant. -/
theorem forkAt_le_gen (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world)
    (hB : m + 1 + snapshot.remaining ≤ B)
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
            exact freshBranch_le_gen Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hsign hpres hpub hupdate snapshot
              hsk m hm hB _ c)
      _ ≤ (((freshBranch sch₂ adversary snapshot).bind fun left =>
          ((freshBranch sch₂ adversary snapshot).map fun right => some (left, right)).bind h) c +
            snapshot.remaining * eps) + snapshot.remaining * eps :=
          add_le_add_left (freshBranch_le_gen Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hsign hpres hpub hupdate
            snapshot hsk m hm hB _ c) _
      _ = _ := by ring

include hmono hquery hagree hsign hpres hpub in
/-- The cut-experiment hybrid under the invariant, from initial worlds
satisfying it at zero. -/
theorem cutExperiment_le_gen (hgood : ∀ generated ∈ sch₁.keygen.support, Good generated.2.1)
    (hkeygen : ∀ generated ∈ sch₁.keygen.support, Inv 0 generated.2.2) (index fuel : Nat)
    (hB : fuel ≤ B) (h : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State → PMF C) (c : C) :
    ((cutExperiment sch₁ adversary index fuel).bind h) c ≤
      ((cutExperiment sch₂ adversary index fuel).bind h) c + fuel * eps := by
  unfold cutExperiment
  rw [← hagree.keygen, PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_const' _ _ _ _ c (fun generated hg => ?_)
  rw [PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_const' _ _ _ _ c (fun state _ => ?_)
  exact cut_le_cut_add_gen Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hsign hpres hpub index fuel _ _
    (hgood generated hg) state _ _ 0 (hkeygen generated hg) (by omega) h c

end
end SDitH.Proofs.CutHybridGen
