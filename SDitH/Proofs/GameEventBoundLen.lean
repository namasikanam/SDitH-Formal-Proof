import SDitH.Proofs.GameEventBound
import SDitH.Proofs.HashCipherTrace

/-! The game-level event bound for events whose per-service probability
depends on a size of the other-state, such as the fresh-query log length.
Each service grows the size by at most a fixed amount and raises the event
by at most an increasing function of the size before the call; with the
remaining fuel accounted, the size stays below a fixed level throughout
the run, so the event at the attempt is bounded by its indicator at the
start plus the fuel times twice the function at that level. The log
length of a traced run grows by at most the budget. -/

namespace SDitH.Proofs.GameEventBoundLen

open Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrap
open GameEventBound (terminalBad)
open scoped Classical ENNReal
noncomputable section

section Trace

variable {Input Digest Key Block State : Type*} [Fintype Digest] [Nonempty Digest]

omit [Fintype Digest] [Nonempty Digest] in
theorem record_length (table : Input → Option Digest) (input : Input) (answer : Digest)
    (log : List (Spec.RandomOracleTrace.Entry Input Digest)) :
    (Spec.RandomOracleTrace.record table input answer log).length ≤ log.length + 1 := by
  unfold Spec.RandomOracleTrace.record
  cases table input with
  | some _ => exact Nat.le_succ _
  | none => exact le_rfl

/-- A traced run adds at most one fresh entry per unit of budget. -/
theorem run_trace_length (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Spec.IdealCipher.Family Key Block) (fuel : Nat) (state : State) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Spec.RandomOracleTrace.Entry Input Digest))
    (out : Spec.HashCipherTrace.Result Input Digest Key Block State)
    (hout : out ∈ (Spec.HashCipherTrace.runFixed procedure family fuel state table hashes ciphers log).support) :
    out.trace.length ≤ log.length + fuel := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [Spec.HashCipherTrace.runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact le_rfl
  | succ fuel ih =>
    simp only [Spec.HashCipherTrace.runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst out
      exact Nat.le_add_right _ _
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      have h := ih (next result.1) result.2 _ ciphers _ inner hinner
      have hrec := record_length table input result.1 log
      simp only [HashCipherTrace.mark_trace]
      omega
    | cipher request next =>
      have h := ih _ table hashes _ log out hrest
      omega

end Trace

section Game

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- Each service grows the size by at most `growth` and raises the event by
at most `epsilon` of the size before the call. -/
structure ServiceBoundLen (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (bad : Other → Bool) (size : Other → Nat) (growth : Nat) (epsilon : Nat → ℝ≥0∞) : Prop where
  prepare : ∀ pk sk msg other,
    ((components.prepareSigning pk sk msg other).map (fun r => bad r.2.2)) true ≤ indicator (bad other) + epsilon (size other)
  prepare_size : ∀ pk sk msg other r, r ∈ (components.prepareSigning pk sk msg other).support → size r.2.2 ≤ size other + growth
  open_ : ∀ st d other, ((components.openSigning st d other).map (fun r => bad r.2)) true ≤ indicator (bad other) + epsilon (size other)
  open_size : ∀ st d other r, r ∈ (components.openSigning st d other).support → size r.2 ≤ size other + growth
  verify : ∀ pk msg sig other,
    ((components.prepareVerification pk msg sig other).map (fun r => bad r.2)) true ≤ indicator (bad other) + epsilon (size other)
  verify_size : ∀ pk msg sig other r, r ∈ (components.prepareVerification pk msg sig other).support →
    size r.2 ≤ size other + growth
  oracle : ∀ q other, ((components.publicOracle q other).map (fun r => bad r.2)) true ≤ indicator (bad other) + epsilon (size other)
  oracle_size : ∀ q other r, r ∈ (components.publicOracle q other).support → size r.2 ≤ size other + growth

variable (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
  (bad : Other → Bool) (size : Other → Nat) (growth : Nat) (epsilon : Nat → ℝ≥0∞)

theorem sign_bound_len (hb : ServiceBoundLen components bad size growth epsilon) (hmono : Monotone epsilon)
    (L : Nat) (sk : PublicKey × SecretKey) (message : Message)
    (world : World (HashInput PublicKey Message Payload) Digest Other) (hsize : size world.other + growth ≤ L) :
    (((scheme components).sign sk message world).map (fun r => bad r.2.other)) true ≤
      indicator (bad world.other) + (epsilon L + epsilon L) := by
  dsimp only [scheme]
  rw [← add_assoc]
  refine RandomOracleTrap.bind_map_indicator_le _ _ _ (fun prepared => bad prepared.2.2) (epsilon L) ?_ |>.trans ?_
  · intro prepared hprep
    rw [PMF.map_bind]
    refine ChallengeMixtures.bind_true_le _ _ _ fun hashResult _ => ?_
    rw [PMF.map_comp]
    refine (hb.open_ prepared.2.1 hashResult.1 prepared.2.2).trans (add_le_add_right (hmono ?_) _)
    exact (hb.prepare_size _ _ _ _ prepared hprep).trans hsize
  · refine add_le_add_left ((hb.prepare sk.1 sk.2 message world.other).trans (add_le_add_right (hmono ?_) _)) _
    omega

theorem sign_size (hb : ServiceBoundLen components bad size growth epsilon) (sk : PublicKey × SecretKey) (message : Message)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (r : Signature Digest Body × World (HashInput PublicKey Message Payload) Digest Other)
    (hr : r ∈ ((scheme components).sign sk message world).support) : size r.2.other ≤ size world.other + (growth + growth) := by
  obtain ⟨prepared, hprep, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨hashed, _, hopen⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨opened, hopened, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hopen
  subst hres
  have h1 := hb.prepare_size _ _ _ _ prepared hprep
  have h2 := hb.open_size _ _ _ opened hopened
  show size opened.2 ≤ _
  omega

theorem verify_bound_len (hb : ServiceBoundLen components bad size growth epsilon) (hmono : Monotone epsilon)
    (L : Nat) (pk : PublicKey) (message : Message) (signature : Signature Digest Body)
    (world : World (HashInput PublicKey Message Payload) Digest Other) (hsize : size world.other ≤ L) :
    (((scheme components).prepareVerification pk message signature world).map (fun r => bad r.2.other)) true ≤
      indicator (bad world.other) + epsilon L := by
  dsimp only [scheme]
  rw [PMF.map_comp]
  exact (hb.verify pk message signature world.other).trans (add_le_add_right (hmono hsize) _)

theorem oracle_bound_len (hb : ServiceBoundLen components bad size growth epsilon) (hmono : Monotone epsilon)
    (L : Nat) (query : Query) (world : World (HashInput PublicKey Message Payload) Digest Other)
    (hsize : size world.other ≤ L) :
    (((scheme components).publicOracle query world).map (fun r => bad r.2.other)) true ≤
      indicator (bad world.other) + epsilon L := by
  dsimp only [scheme]
  rw [PMF.map_comp]
  exact (hb.oracle query world.other).trans (add_le_add_right (hmono hsize) _)

theorem oracle_size (hb : ServiceBoundLen components bad size growth epsilon) (query : Query)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (r : Answer × World (HashInput PublicKey Message Payload) Digest Other)
    (hr : r ∈ ((scheme components).publicOracle query world).support) : size r.2.other ≤ size world.other + growth := by
  obtain ⟨result, hresult, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  subst hres
  exact hb.oracle_size _ _ result hresult

/-- Along the run, with the size plus the remaining growth below a level,
the event at the attempt is bounded by its indicator at the start plus the
fuel times twice the function at that level. -/
theorem run_event_bound_len (hb : ServiceBoundLen components bad size growth epsilon) (hmono : Monotone epsilon)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State) (L : Nat) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : PublicKey × SecretKey) (state : State)
      (world : World (HashInput PublicKey Message Payload) Digest Other)
      (trace : Trace Message (HashInput PublicKey Message Payload) Query),
      size world.other + fuel * (growth + growth) ≤ L →
      ((Spec.SignatureSecurity.run (scheme components) adversary fuel pk sk state world trace).map (terminalBad bad)) true ≤
        indicator (bad world.other) + fuel * (epsilon L + epsilon L) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state world trace _
    simp [Spec.SignatureSecurity.run, PMF.pure_map, PMF.pure_apply, terminalBad]
  | succ fuel ih =>
    intro pk sk state world trace hsize
    have hsucc : (fuel + 1) * (growth + growth) = fuel * (growth + growth) + (growth + growth) := Nat.succ_mul _ _
    rw [hsucc] at hsize
    simp only [Spec.SignatureSecurity.run, PMF.map_bind]
    refine ChallengeMixtures.bind_true_le _ _ _ fun action _ => ?_
    cases action with
    | abort =>
      simp [PMF.pure_map, PMF.pure_apply, terminalBad]
    | finish message signature =>
      rw [PMF.map_comp]
      refine (ForkCutRun.map_true_mono _ _
        (fun r : Option (HashInput PublicKey Message Payload) × World (HashInput PublicKey Message Payload) Digest Other =>
          bad r.2.other) ?_).trans ?_
      · intro result h
        simp only [Function.comp] at h
        cases hr : result.1 with
        | none => rw [hr] at h; simp [terminalBad] at h
        | some input => rw [hr] at h; exact h
      · exact (verify_bound_len components bad size growth epsilon hb hmono L pk message signature world (by omega)).trans
          (add_le_add_right ((le_self_add).trans (GameEventBound.le_succ_mul fuel (epsilon L + epsilon L))) _)
    | sign message next =>
      refine (RandomOracleTrap.bind_map_indicator_le _ _ _
        (fun r : Signature Digest Body × World (HashInput PublicKey Message Payload) Digest Other => bad r.2.other)
        (fuel * (epsilon L + epsilon L)) fun result hresult => ih pk sk (next result.1) result.2 _ ?_).trans ?_
      · have := sign_size components bad size growth epsilon hb sk message world result hresult
        omega
      · refine (add_le_add_left (sign_bound_len components bad size growth epsilon hb hmono L sk message world (by omega)) _).trans
          (le_of_eq ?_)
        rw [GameEventBound.succ_mul_eq]
        ring
    | hash input next =>
      rw [PMF.map_bind]
      refine ChallengeMixtures.bind_true_le _ _ _ fun result _ => ?_
      refine (ih pk sk (next result.1) _ _ (by show size world.other + _ ≤ L; omega)).trans ?_
      show indicator (bad world.other) + _ ≤ _
      exact add_le_add_right (mul_le_mul_left (Nat.cast_le.mpr (Nat.le_succ fuel)) _) _
    | query input next =>
      refine (RandomOracleTrap.bind_map_indicator_le _ _ _
        (fun r : Answer × World (HashInput PublicKey Message Payload) Digest Other => bad r.2.other)
        (fuel * (epsilon L + epsilon L)) fun result hresult => ih pk sk (next result.1) result.2 _ ?_).trans ?_
      · have := oracle_size components bad size growth epsilon hb input world result hresult
        omega
      · refine (add_le_add_left (oracle_bound_len components bad size growth epsilon hb hmono L input world (by omega)) _).trans ?_
        calc indicator (bad world.other) + epsilon L + fuel * (epsilon L + epsilon L)
            ≤ indicator (bad world.other) + (epsilon L + epsilon L) + fuel * (epsilon L + epsilon L) := by
              gcongr
              exact le_self_add
          _ = indicator (bad world.other) + (fuel + 1 : ℕ) * (epsilon L + epsilon L) := by
              rw [GameEventBound.succ_mul_eq]
              ring

/-- A fresh branch from a snapshot, with the size plus the remaining growth below a level. -/
theorem branch_event_bound_len (hb : ServiceBoundLen components bad size growth epsilon) (hmono : Monotone epsilon)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (snapshot : Snapshot PublicKey (PublicKey × SecretKey) Message (HashInput PublicKey Message Payload) Digest Other Query State)
    (L : Nat) (hsize : size snapshot.world.other + snapshot.remaining * (growth + growth) ≤ L) :
    ((freshBranch (scheme components) adversary snapshot).map (fun branch => terminalBad bad branch.checked.terminal)) true ≤
      indicator (bad snapshot.world.other) + snapshot.remaining * (epsilon L + epsilon L) := by
  simp only [freshBranch, PMF.map_bind]
  refine ChallengeMixtures.bind_true_le _ _ _ fun answer _ => ?_
  rw [PMF.map_comp]
  unfold continueWith
  refine (RandomOracleTrap.bind_map_indicator_le _ _ _ (terminalBad bad) 0 fun terminal _ => ?_).trans ?_
  · exact GameEventBound.finalize_event bad terminal
  · rw [add_zero]
    exact run_event_bound_len components bad size growth epsilon hb hmono adversary L snapshot.remaining
      snapshot.publicKey snapshot.secretKey (snapshot.next answer) _ _ hsize

end Game

end
end SDitH.Proofs.GameEventBoundLen
