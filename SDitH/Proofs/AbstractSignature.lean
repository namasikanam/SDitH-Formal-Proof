import SDitH.Spec.AbstractSignature
import SDitH.Proofs.SignatureSecurity

namespace SDitH.Proofs.AbstractSignature

open Spec.SignatureSecurity Spec.AbstractSignature
open scoped Classical ENNReal
noncomputable section

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- Lazy evaluation can add only the queried input. -/
theorem oracle_lookup_origin {Input : Type*} (table : Input → Option Digest) (input : Input)
    (result : Digest × (Input → Option Digest))
    (hr : result ∈ (Spec.RandomOracle.query table input).support)
    (q : Input) (answer : Digest) (hq : result.2 q = some answer) :
    q = input ∨ table q = some answer := by
  unfold Spec.RandomOracle.query at hr
  cases he : table input with
  | some old =>
    rw [he, PMF.mem_support_pure_iff] at hr
    subst result
    exact Or.inr hq
  | none =>
    rw [he] at hr
    obtain ⟨fresh, _, hresult⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst result
    by_cases hqi : q = input
    · exact Or.inl hqi
    · exact Or.inr (by simpa [Function.update_of_ne hqi] using hq)

theorem oracle_accounted
    (table : HashInput PublicKey Message Payload → Option Digest)
    (trace : Trace Message (HashInput PublicKey Message Payload) Query)
    (ha : Accounted table trace) (input : HashInput PublicKey Message Payload)
    (result : Digest × (HashInput PublicKey Message Payload → Option Digest))
    (hr : result ∈ (Spec.RandomOracle.query table input).support) :
    Accounted result.2 { trace with hashRequests := input :: trace.hashRequests } := by
  intro q answer hq
  rcases oracle_lookup_origin table input result hr q answer hq with he | hold
  · exact Or.inl (by simp [he])
  · rcases ha q answer hold with hhash | hsign
    · exact Or.inl (List.mem_cons_of_mem _ hhash)
    · exact Or.inr hsign

theorem signing_accounted
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (secret : PublicKey × SecretKey) (message : Message)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (trace : Trace Message (HashInput PublicKey Message Payload) Query)
    (ha : Accounted world.hashTable trace)
    (result : Signature Digest Body × World (HashInput PublicKey Message Payload) Digest Other)
    (hr : result ∈ ((scheme components).sign secret message world).support) :
    Accounted result.2.hashTable { trace with signingRequests := message :: trace.signingRequests } := by
  obtain ⟨prepared, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨hashResult, hhash, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨opened, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst result
  intro q answer hq
  rcases oracle_lookup_origin world.hashTable ⟨secret.1, message, prepared.1⟩ hashResult hhash q answer hq with he | hold
  · exact Or.inr (by simp [he])
  · rcases ha q answer hold with hhash | hsign
    · exact Or.inl hhash
    · exact Or.inr (List.mem_cons_of_mem _ hsign)

/-- Before the final HashPiop query, verification and the other public-oracle
interface leave that table unchanged by construction. No security contract for
their other computations is needed for this invariant. -/
theorem run_accounted
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) (pk : PublicKey) (secret : PublicKey × SecretKey) (state : State)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (trace : Trace Message (HashInput PublicKey Message Payload) Query)
    (ha : Accounted world.hashTable trace)
    (a : Attempt Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (hout : Terminal.attempt a ∈ (run (scheme components) adversary fuel pk secret state world trace).support) :
    Accounted a.world.hashTable a.trace ∧ a.input.message = a.message := by
  induction fuel generalizing state world trace with
  | zero => simp [run] at hout
  | succ fuel ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | abort => simp at hnext
    | finish message signature =>
      obtain ⟨prepared, hp, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      obtain ⟨result, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      subst prepared
      cases hh : result.1 with
      | none => simp [hh] at he
      | some payload =>
        simp only [hh, Option.map_some, Terminal.attempt.injEq] at he
        subst a
        exact ⟨ha, rfl⟩
    | sign message next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      exact ih (next result.1) result.2 _
        (signing_accounted components secret message world trace ha result hr) hrest
    | hash input next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      exact ih (next result.1) _ _ (oracle_accounted world.hashTable trace ha input result hr) hrest
    | query input next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨answer, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst result
      exact ih (next answer.1) { world with other := answer.2 }
        { trace with publicRequests := input :: trace.publicRequests } ha hrest

theorem terminal_law_accounted
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat)
    (a : Attempt Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (ha : Terminal.attempt a ∈ (terminalLaw (scheme components) adversary fuel).support) :
    Accounted a.world.hashTable a.trace ∧ a.input.message = a.message := by
  obtain ⟨generated, hg, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha
  obtain ⟨keys, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hg
  subst generated
  obtain ⟨state, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  apply run_accounted components adversary fuel keys.1 (keys.1, keys.2.1) state _ _ _ a hrun
  intro input answer h
  simp at h

/-- A fresh-message attempt with a present final-hash input must have queried
that exact input through the adversary's hash interface. Signing-oracle queries
on other messages cannot account for it in this typed abstract model. -/
theorem present_fresh_attempt_was_queried
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat)
    (a : Attempt Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (ha : Terminal.attempt a ∈ (terminalLaw (scheme components) adversary fuel).support)
    (hfresh : a.message ∉ a.trace.signingRequests)
    (answer : Digest) (hpresent : a.world.hashTable a.input = some answer) :
    a.input ∈ a.trace.hashRequests := by
  obtain ⟨haccount, hmessage⟩ := terminal_law_accounted components adversary fuel a ha
  rcases haccount a.input answer hpresent with hhash | hsign
  · exact hhash
  · exact False.elim (hfresh (hmessage ▸ hsign))

/-- This event supplies a concrete earlier adversarial query for a winning
forgery. It does not assert an extracted witness or a successful fork. -/
def queriedWinning
    (checked : Checked Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Other Query) : Bool :=
  match checked.terminal with
  | .attempt a => checked.wins && decide (a.input ∈ a.trace.hashRequests)
  | _ => false

theorem present_winner_has_query
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat)
    (checked : Checked Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Other Query)
    (hc : checked ∈ (experiment (scheme components) adversary fuel).support)
    (hw : checked.wins = true) (hp : checked.inputWasPresent = true) :
    queriedWinning checked = true := by
  obtain ⟨terminal, ht, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
  obtain ⟨a, he, hchecked, hfresh, hpresent⟩ :=
    SignatureSecurity.finalize_winning_attempt terminal checked hfinal hw
  subst terminal
  rw [hpresent] at hp
  obtain ⟨answer, ha⟩ := Option.isSome_iff_exists.mp hp
  have hquery := present_fresh_attempt_was_queried components adversary fuel a ht hfresh answer ha
  simp [queriedWinning, hchecked, hw, hquery]

theorem present_winning_mass_le_queried
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) :
    ((experiment (scheme components) adversary fuel).map
      (fun checked => checked.wins && checked.inputWasPresent)) true ≤
    ((experiment (scheme components) adversary fuel).map queriedWinning) true := by
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_mono
  intro checked ⟨hwin, hc⟩
  have hh : checked.wins = true ∧ checked.inputWasPresent = true := by simpa using hwin
  exact present_winner_has_query components adversary fuel checked hc hh.1 hh.2

/-- First reduction step in the abstract EUF-CMA game: a forgery yields an
earlier adversarial query to its exact final verification input, except for
the 1/|Digest| guessing term. All signing-query/table provenance is proved.
The forking, simulation and RSD-extraction steps are not assumptions here and
remain to be proved. -/
theorem forgery_to_prior_hash_query
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) :
    advantage (scheme components) adversary fuel ≤
      ((experiment (scheme components) adversary fuel).map queriedWinning) true +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  apply le_trans (SignatureSecurity.advantage_le_present_plus_guess (scheme components) adversary fuel)
  exact add_le_add (present_winning_mass_le_queried components adversary fuel) le_rfl

end
end SDitH.Proofs.AbstractSignature
