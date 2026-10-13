import SDitH.Proofs.ChargeCut
import SDitH.Proofs.ChargeRunCont

/-! The replay hybrids with the per-call signing bounds stated for the
game's own continuations: the cut run's continuations at a signing query
and the run's continuations within a branch. The charges are those of the
replay hybrids; only the shape of the per-call hypotheses changes. -/

namespace SDitH.Proofs.ChargeCutCont

open Spec.SignatureSecurity Spec.SignatureReplay
open RunHybrid RunHybridGen CutHybrid CutHybridGen EventHybrid PrefixFromHead ChargeRun ChargeExpect ChargeCut ChargeRunCont
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

variable (Inv : Nat → World HashInput Digest Other → Prop)
  (hmono : ∀ (n m : Nat) (world : World HashInput Digest Other), n ≤ m → Inv n world → Inv m world)
  (hquery : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat)
    (r : Digest × (HashInput → Option Digest)), Inv n world →
    r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
  (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : World HashInput Digest Other → ℝ≥0∞) (B : Nat)
  (hpres : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
    (r : Signature × World HashInput Digest Other), Inv n world →
    r ∈ (sch₁.sign sk message world).support → Inv (n + 1) r.2)
  (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
    Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
  (hupdate : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat) (d : Digest), Inv n world →
    Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) })

/-- The per-call bound for the run's continuations. -/
def SignRun : Prop :=
  ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
    Inv B world → ∀ (fuel : Nat) (pk : PublicKey) (next : Signature → State) (trace : Trace Message HashInput Query)
      (h : Terminal Message Signature HashInput Digest Other Query → PMF C) (c : C),
    ((sch₁.sign sk message world).bind fun r => (run sch₂ adversary fuel pk sk (next r.1) r.2 trace).bind h) c ≤
      ((sch₂.sign sk message world).bind fun r => (run sch₂ adversary fuel pk sk (next r.1) r.2 trace).bind h) c +
        eps world

/-- The per-call bound for the cut run's continuations. -/
def SignCut : Prop :=
  ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
    Inv B world → ∀ (index fuel : Nat) (pk : PublicKey) (next : Signature → State) (trace : Trace Message HashInput Query)
      (h : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State → PMF C) (c : C),
    ((sch₁.sign sk message world).bind fun r => (cut sch₂ adversary index fuel pk sk (next r.1) r.2 trace).bind h) c ≤
      ((sch₂.sign sk message world).bind fun r => (cut sch₂ adversary index fuel pk sk (next r.1) r.2 trace).bind h) c +
        eps world

include hmono hquery hagree hpres hpub in
/-- The cut hybrid with the charge. -/
theorem cut_le_cut_add_charge (hsign : SignCut (C := C) Inv sch₁ sch₂ adversary Good eps B)
    (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (hsk : Good sk) (state : State)
    (world : World HashInput Digest Other) (trace : Trace Message HashInput Query) (m : Nat)
    (hm : Inv m world) (hB : m + fuel ≤ B)
    (h : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State → PMF C) (c : C) :
    ((cut sch₁ adversary index fuel pk sk state world trace).bind h) c ≤
      ((cut sch₂ adversary index fuel pk sk state world trace).bind h) c +
        chargeCut eps sch₁ adversary index fuel pk sk state world trace := by
  induction fuel generalizing index state world trace m with
  | zero =>
    simp only [cut, chargeCut, add_zero]
    exact le_rfl
  | succ fuel ih =>
    simp only [cut, chargeCut, mean, PMF.bind_bind]
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
            (cut sch₂ adversary index fuel pk sk (next result.1) result.2
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c +
            ∑' r, (sch₁.sign sk message world) r * chargeCut eps sch₁ adversary index fuel pk sk (next r.1) r.2
              { trace with signingRequests := message :: trace.signingRequests } :=
            bind_le_bind_add_cost _ _ _ _ c (fun result hres =>
              ih index (next result.1) result.2 _ (m + 1) (hpres sk message world m result hm hres) (by omega))
        _ ≤ (((sch₂.sign sk message world).bind fun result =>
            (cut sch₂ adversary index fuel pk sk (next result.1) result.2
              { trace with signingRequests := message :: trace.signingRequests }).bind h) c + eps world) +
            ∑' r, (sch₁.sign sk message world) r * chargeCut eps sch₁ adversary index fuel pk sk (next r.1) r.2
              { trace with signingRequests := message :: trace.signingRequests } :=
            add_le_add_left (hsign sk hsk message world (hmono m B world (by omega) hm) index fuel pk next _ h c) _
        _ = _ := by rw [add_assoc]
    | hash input next =>
      dsimp only
      cases index with
      | zero =>
        dsimp only
        exact le_self_add
      | succ index =>
        dsimp only
        rw [PMF.bind_bind, PMF.bind_bind]
        exact bind_le_bind_add_cost _ _ _ _ c (fun result hq =>
          ih index (next result.1) _ _ (m + 1) (hquery world input m result hm hq) (by omega))
    | query input next =>
      dsimp only
      rw [hagree.publicOracle, PMF.bind_bind, PMF.bind_bind]
      exact bind_le_bind_add_cost _ _ _ _ c (fun result hr =>
        ih index (next result.1) result.2 _ (m + 1) (hpub input world m result hm hr) (by omega))

include hmono hquery hagree hpres hpub hupdate in
/-- The continuation hybrid with the charge of the run from the snapshot's
world with the programmed answer. -/
theorem continueWith_le_charge (hsign : SignRun (C := C) Inv sch₁ sch₂ adversary Good eps B)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world)
    (hB : m + 1 + snapshot.remaining ≤ B) (answer : Digest)
    (h : Checked Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    ((continueWith sch₁ adversary snapshot answer).bind h) c ≤
      ((continueWith sch₂ adversary snapshot answer).bind h) c +
        charge eps sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
          { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
          { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests } := by
  unfold continueWith
  rw [PMF.bind_bind, PMF.bind_bind]
  exact run_le_run_add_charge_cont sch₁ sch₂ adversary hagree Good eps B Inv hmono hquery hsign hpres hpub
    snapshot.remaining _ _ hsk _ _ _ (m + 1) (hupdate snapshot.world snapshot.input m answer hm) (by omega) _ c

include hmono hquery hagree hpres hpub hupdate in
/-- The fresh-branch hybrid with the branch charge. -/
theorem freshBranch_le_charge (hsign : SignRun (C := C) Inv sch₁ sch₂ adversary Good eps B)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world)
    (hB : m + 1 + snapshot.remaining ≤ B) (h : Branch Message Signature HashInput Digest Other Query → PMF C) (c : C) :
    ((freshBranch sch₁ adversary snapshot).bind h) c ≤
      ((freshBranch sch₂ adversary snapshot).bind h) c + chargeBranch eps sch₁ adversary snapshot := by
  unfold freshBranch chargeBranch mean
  rw [PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_cost _ _ _ _ c (fun answer _ => ?_)
  rw [PMF.bind_map, PMF.bind_map]
  exact continueWith_le_charge Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hpres hpub hupdate hsign snapshot hsk
    m hm hB answer _ c

include hmono hquery hagree hpres hpub hupdate in
/-- The fork hybrid with two branch charges. -/
theorem forkAt_le_charge (hsign : SignRun (C := C) Inv sch₁ sch₂ adversary Good eps B)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world)
    (hB : m + 1 + snapshot.remaining ≤ B)
    (h : Option (Branch Message Signature HashInput Digest Other Query × Branch Message Signature HashInput Digest Other Query) →
      PMF C) (c : C) :
    ((forkAt sch₁ adversary snapshot).bind h) c ≤
      ((forkAt sch₂ adversary snapshot).bind h) c + 2 * chargeBranch eps sch₁ adversary snapshot := by
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
            chargeBranch eps sch₁ adversary snapshot :=
          bind_le_bind_add_const' _ _ _ _ c (fun left _ => by
            rw [PMF.bind_map, PMF.bind_map]
            exact freshBranch_le_charge Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hpres hpub hupdate hsign
              snapshot hsk m hm hB _ c)
      _ ≤ (((freshBranch sch₂ adversary snapshot).bind fun left =>
          ((freshBranch sch₂ adversary snapshot).map fun right => some (left, right)).bind h) c +
            chargeBranch eps sch₁ adversary snapshot) + chargeBranch eps sch₁ adversary snapshot :=
          add_le_add_left (freshBranch_le_charge Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hpres hpub
            hupdate hsign snapshot hsk m hm hB _ c) _
      _ = _ := by ring

include hmono hquery hagree hpres hpub in
/-- The cut-experiment hybrid with the experiment's charge. -/
theorem cutExperiment_le_charge (hsign : SignCut (C := C) Inv sch₁ sch₂ adversary Good eps B)
    (hgood : ∀ generated ∈ sch₁.keygen.support, Good generated.2.1)
    (hkeygen : ∀ generated ∈ sch₁.keygen.support, Inv 0 generated.2.2) (index fuel : Nat)
    (hB : fuel ≤ B) (h : Cut PublicKey SecretKey Message Signature HashInput Digest Other Query State → PMF C) (c : C) :
    ((cutExperiment sch₁ adversary index fuel).bind h) c ≤
      ((cutExperiment sch₂ adversary index fuel).bind h) c + chargeExperiment eps sch₁ adversary index fuel := by
  unfold cutExperiment chargeExperiment mean
  rw [← hagree.keygen, PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_cost _ _ _ _ c (fun generated hg => ?_)
  rw [PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_cost _ _ _ _ c (fun state _ => ?_)
  exact cut_le_cut_add_charge Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hpres hpub hsign index fuel _ _
    (hgood generated hg) state _ _ 0 (hkeygen generated hg) (by omega) h c

include hmono hquery hagree hpres hpub hupdate in
/-- The event-experiment hybrid with the experiment's charge and the fork
charge. -/
theorem eventExp_le_charge (hsignRun : SignRun (C := Bool) Inv sch₁ sch₂ adversary Good eps B)
    (hsignCut : SignCut (C := Bool) Inv sch₁ sch₂ adversary Good eps B)
    (hpres₂ : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
      (r : Signature × World HashInput Digest Other), Inv n world →
      r ∈ (sch₂.sign sk message world).support → Inv (n + 1) r.2)
    (hgood : ∀ generated ∈ sch₁.keygen.support, Good generated.2.1)
    (hkeygen : ∀ generated ∈ sch₁.keygen.support, Inv 0 generated.2.2)
    (E : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State →
      Option (Branch Message Signature HashInput Digest Other Query × Branch Message Signature HashInput Digest Other Query) →
      Bool)
    (index fuel : Nat) (hB : 2 * fuel + 1 ≤ B) :
    (eventExp sch₁ adversary E index fuel) true ≤
      (eventExp sch₂ adversary E index fuel) true +
        (chargeExperiment eps sch₁ adversary index fuel + chargeFork eps sch₁ sch₂ adversary index fuel) := by
  unfold eventExp
  refine (cutExperiment_le_charge Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hpres hpub hsignCut hgood
    hkeygen index fuel (by omega) _ true).trans ?_
  rw [add_comm (chargeExperiment eps sch₁ adversary index fuel) (chargeFork eps sch₁ sch₂ adversary index fuel),
    ← add_assoc]
  refine add_le_add_left ?_ _
  unfold chargeFork mean
  refine bind_le_bind_add_cost _ _ _ _ true (fun c hc => ?_)
  cases c with
  | ended t =>
    dsimp only
    exact le_self_add
  | saved snapshot =>
    dsimp only
    obtain ⟨generated, hg, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
    obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
    have hg₁ : generated ∈ sch₁.keygen.support := by rw [hagree.keygen]; exact hg
    have hrem : snapshot.remaining ≤ fuel :=
      ForkEventUnion.cut_remaining_le sch₂ adversary index fuel _ _ state _ _ _ hcut snapshot rfl
    have hkey : snapshot.secretKey = generated.2.1 :=
      cut_saved_secretKey sch₂ adversary index fuel _ _ state _ _ _ hcut snapshot rfl
    have hsk : Good snapshot.secretKey := by
      rw [hkey]
      exact hgood generated hg₁
    have hsup : Inv (0 + fuel) snapshot.world :=
      cut_saved_gen Inv hmono hquery sch₂ adversary hpres₂ hpub index fuel _ _ state _ _ 0 (hkeygen generated hg₁) _ hcut
        snapshot rfl
    rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    exact forkAt_le_charge Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hpres hpub hupdate hsignRun snapshot hsk _
      hsup (by omega) _ true

end
end SDitH.Proofs.ChargeCutCont
