import SDitH.Proofs.EventRestore
import SDitH.Proofs.MeanHybridContW

/-! The mean-form hybrids for the restored fork's branches. The counted
invariant holds along the run with its final world (with the verification
preparation's preservation as a hypothesis), and a fresh branch with its
final world from a resampled snapshot world is within the remaining fuel
times the per-call bound for continuations of the run with its final
world. -/

namespace SDitH.Proofs.MeanForkCont

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open GameResample ChargeExpect RunWorld GamePrune PruneLawRun HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq ForkRestoreEnd EventRestore SharedResample SignBridge HiddenSlice MeanHybrid ChargeCutExpect
open RunHybrid MeanHybridCont MeanHybridContW
open scoped Classical ENNReal

noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable {lambda s wit rnd : Nat}
  (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
    Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (ε : ℝ≥0∞) (B : Nat)
  (Inv : Nat → GW HashInput Digest lambda s wit rnd → Prop)
  (hmono : ∀ (n m : Nat) (world : GW HashInput Digest lambda s wit rnd), n ≤ m → Inv n world → Inv m world)
  (hres : ∀ (n : Nat) (world : GW HashInput Digest lambda s wit rnd), Inv n world →
    ∀ w ∈ (resampleW resample world).support, Inv n w)
  (hquery : ∀ (world : GW HashInput Digest lambda s wit rnd) (input : HashInput) (n : Nat)
    (r : Digest × (HashInput → Option Digest)), Inv n world →
    r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
  (hpres : ∀ (sk : SecretKey) (message : Message) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
    (r : Signature × GW HashInput Digest lambda s wit rnd), Inv n world →
    r ∈ (sch₁.sign sk message world).support → Inv (n + 1) r.2)
  (hpub : ∀ (query : Query) (world : GW HashInput Digest lambda s wit rnd) (n : Nat)
    (r : Answer × GW HashInput Digest lambda s wit rnd),
    Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
  (hprepInv : ∀ (pk : PublicKey) (message : Message) (signature : Signature) (world : GW HashInput Digest lambda s wit rnd)
    (n : Nat) (r : Option HashInput × GW HashInput Digest lambda s wit rnd), Inv n world →
    r ∈ (sch₂.prepareVerification pk message signature world).support → Inv (n + 1) r.2)
  (hupdate : ∀ (world : GW HashInput Digest lambda s wit rnd) (input : HashInput) (n : Nat) (d : Digest), Inv n world →
    Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) })
  (hsignLaw : ∀ (sk : SecretKey) (message : Message), PostLaw resample (sch₁.sign sk message))
  (hpubLaw : ∀ query : Query, PostLaw resample (sch₂.publicOracle query))

include hagree hmono hquery hpres hpub hprepInv in
/-- The invariant along the first scheme's run with its final world. -/
theorem runW_inv : ∀ (fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State) (w : GW HashInput Digest lambda s wit rnd)
    (trace : Trace Message HashInput Query) (n : Nat), Inv n w →
    ∀ r ∈ (runW sch₁ adversary fuel pk sk state w trace).support, Inv (n + fuel) r.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state w trace n hn r hr
    simp only [runW, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simpa using hn
  | succ fuel ih =>
    intro pk sk state w trace n hn r hr
    simp only [runW, PMF.mem_support_bind_iff] at hr
    obtain ⟨action, -, hr⟩ := hr
    cases action with
    | abort =>
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hmono _ _ _ (by omega) hn
    | finish message signature =>
      simp only [PMF.support_map, Set.mem_image] at hr
      obtain ⟨result, hres', rfl⟩ := hr
      rw [hagree.prepareVerification] at hres'
      exact hmono _ _ _ (by omega) (hprepInv pk message signature w n result hn hres')
    | sign message next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres', hr⟩ := hr
      exact hmono _ _ _ (by omega) (ih pk sk _ _ _ (n + 1) (hpres sk message w n result hn hres') r hr)
    | hash input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres', hr⟩ := hr
      exact hmono _ _ _ (by omega) (ih pk sk _ _ _ (n + 1) (hquery w input n result hn hres') r hr)
    | query input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres', hr⟩ := hr
      rw [hagree.publicOracle] at hres'
      exact hmono _ _ _ (by omega) (ih pk sk _ _ _ (n + 1) (hpub input w n result hn hres') r hr)

include hagree hmono hres hquery hpres hpub hupdate hsignLaw hpubLaw in
/-- The fresh branch with its final world, from a resampled snapshot world,
is within the remaining fuel times the per-call bound. -/
theorem freshBranchW_le_mean (hsign : SignRunWMean (C := Bool) resample sch₁ sch₂ adversary Good ε B Inv)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (hsk : Good snapshot.secretKey) (m : Nat) (hm : Inv m snapshot.world) (hB : m + 1 + snapshot.remaining ≤ B)
    (K : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd → PMF Bool) :
    mean (resampleW resample snapshot.world) (fun y =>
        mean (freshBranchW sch₁ adversary { snapshot with world := y }) fun rw => (K rw) true) ≤
      mean (resampleW resample snapshot.world) (fun y =>
        mean (freshBranchW sch₂ adversary { snapshot with world := y }) fun rw => (K rw) true) +
        snapshot.remaining * ε := by
  simp only [freshBranchW, mean_bind, mean_map]
  rw [mean_comm]
  conv_rhs => rw [mean_comm, ← mean_add_const]
  refine mean_le_mean _ _ _ fun answer _ => ?_
  dsimp only
  rw [mean_resampleW_update' snapshot.world (fun t => Function.update t snapshot.input (some answer))
    (fun y => mean (runW sch₁ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        mean (finalize r.1) fun c => (K (⟨answer, c⟩, r.2)) true),
    mean_resampleW_update' snapshot.world (fun t => Function.update t snapshot.input (some answer))
    (fun y => mean (runW sch₂ adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
      { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }) fun r =>
        mean (finalize r.1) fun c => (K (⟨answer, c⟩, r.2)) true)]
  have hF : ∀ (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)
      Query Answer) (y : GW HashInput Digest lambda s wit rnd),
      mean (runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests })
        (fun r => mean (finalize r.1) fun c => (K (⟨answer, c⟩, r.2)) true) =
      ((runW sch adversary snapshot.remaining snapshot.publicKey snapshot.secretKey (snapshot.next answer) y
        { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }).bind fun r =>
          (finalize r.1).bind fun c => K (⟨answer, c⟩, r.2)) true := by
    intro sch y
    simp only [mean_bind_apply]
  simp only [hF]
  exact runW_le_runW_mean_cont resample sch₁ sch₂ adversary hagree Good ε B Inv hmono hres hquery hpres hpub hsignLaw hpubLaw
    hsign snapshot.remaining _ _ hsk _ _ _ (m + 1) (hupdate snapshot.world snapshot.input m answer hm) (by omega) _ true

end
end SDitH.Proofs.MeanForkCont
