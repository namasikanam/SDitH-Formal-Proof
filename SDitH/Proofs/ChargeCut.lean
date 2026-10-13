import SDitH.Proofs.ChargeExpect
import SDitH.Proofs.CutHybridGen

/-! The replay hybrids with a world-dependent signing charge. The cut run
charges the current world's term at every signing query like the run; a
branch from a saved snapshot charges the run from the snapshot's world
with the programmed answer, averaged over the uniform answer; the fork
charges two branches; the cut experiment charges the cut from the
generated key; and the event experiment is within the cut experiment's
charge plus the fork charge averaged over the second scheme's cut
experiment. -/

namespace SDitH.Proofs.ChargeCut

open Spec.SignatureSecurity Spec.SignatureReplay
open RunHybrid RunHybridGen CutHybrid CutHybridGen EventHybrid PrefixFromHead ChargeRun ChargeExpect
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State C : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The expected cumulative signing charge along a cut run. -/
def chargeCut (eps : World HashInput Digest Other → ℝ≥0∞)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) :
    Nat → Nat → PublicKey → SecretKey → State → World HashInput Digest Other → Trace Message HashInput Query → ℝ≥0∞
  | _, 0, _, _, _, _, _ => 0
  | index, fuel + 1, pk, sk, state, world, trace => mean (adversary.step pk state) fun action =>
      match action with
      | .abort => 0
      | .finish _ _ => 0
      | .sign message next => eps world + mean (sch.sign sk message world) fun r =>
          chargeCut eps sch adversary index fuel pk sk (next r.1) r.2
            { trace with signingRequests := message :: trace.signingRequests }
      | .hash input next =>
          match index with
          | 0 => 0
          | index + 1 => mean (Spec.RandomOracle.query world.hashTable input) fun r =>
              chargeCut eps sch adversary index fuel pk sk (next r.1) { world with hashTable := r.2 }
                { trace with hashRequests := input :: trace.hashRequests }
      | .query input next => mean (sch.publicOracle input world) fun r =>
          chargeCut eps sch adversary index fuel pk sk (next r.1) r.2
            { trace with publicRequests := input :: trace.publicRequests }

/-- The charge of a branch from a saved snapshot: the run from the
snapshot's world with the programmed answer, averaged over the answer. -/
def chargeBranch (eps : World HashInput Digest Other → ℝ≥0∞)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State) : ℝ≥0∞ :=
  mean (PMF.uniformOfFintype Digest) fun answer =>
    charge eps sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer)
      { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }

/-- The charge of the cut experiment: the cut's charge from the generated
key and the adversary's start. -/
def chargeExperiment (eps : World HashInput Digest Other → ℝ≥0∞)
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) (index fuel : Nat) : ℝ≥0∞ :=
  mean sch.keygen fun generated => mean (adversary.start generated.1) fun state =>
    chargeCut eps sch adversary index fuel generated.1 generated.2.1 state generated.2.2 ⟨[], [], []⟩

/-- The fork charge averaged over the second scheme's cut experiment: two
branch charges at a saved snapshot. -/
def chargeFork (eps : World HashInput Digest Other → ℝ≥0∞)
    (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State) (index fuel : Nat) : ℝ≥0∞ :=
  mean (cutExperiment sch₂ adversary index fuel) fun c => match c with
    | .ended _ => 0
    | .saved snapshot => 2 * chargeBranch eps sch₁ adversary snapshot

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

include hmono hquery hagree hpres hpub in
/-- The cut hybrid with the charge. -/
theorem cut_le_cut_add_charge
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps world)
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
            add_le_add_left (hsign sk hsk message world (hmono m B world (by omega) hm) _ c) _
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
theorem continueWith_le_charge
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps world)
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
  exact run_le_run_add_charge sch₁ sch₂ adversary hagree Good eps B Inv hmono hquery hsign hpres hpub snapshot.remaining _ _
    hsk _ _ _ (m + 1) (hupdate snapshot.world snapshot.input m answer hm) (by omega) _ c

include hmono hquery hagree hpres hpub hupdate in
/-- The fresh-branch hybrid with the branch charge. -/
theorem freshBranch_le_charge
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps world)
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
theorem forkAt_le_charge
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps world)
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
theorem cutExperiment_le_charge
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF C) (c : C),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps world)
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
theorem eventExp_le_charge
    (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
      Inv B world → ∀ (h : Signature × World HashInput Digest Other → PMF Bool) (c : Bool),
      ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps world)
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
  refine (cutExperiment_le_charge Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hpres hpub hsign hgood
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
    exact forkAt_le_charge Inv hmono hquery sch₁ sch₂ adversary hagree Good eps B hpres hpub hupdate hsign snapshot hsk _
      hsup (by omega) _ true

end
end SDitH.Proofs.ChargeCut
