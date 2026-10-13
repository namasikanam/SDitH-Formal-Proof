import SDitH.Proofs.SharedGameInvariant
import SDitH.Proofs.ChallengeMixtures
import SDitH.Proofs.RandomOracleTrap

/-! A game-level bound for a Boolean event on the other-state. If every
service call raises the event with probability at most its indicator
before the call plus a constant, then along the abstract run each
adversary action contributes at most twice that constant (a signing
request calls two services), so the event at the attempt is bounded by
its indicator at the start plus the fuel times twice the constant. The
same holds for a fresh branch from a snapshot, since finalization keeps
the terminal. This is the accounting of per-run trace bounds over the
whole game, independent of which event is charged. -/

namespace SDitH.Proofs.GameEventBound

open Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrap
open scoped Classical ENNReal
noncomputable section

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- Each service raises the event by at most a constant beyond its indicator. -/
structure ServiceBound (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (bad : Other → Bool) (B : ℝ≥0∞) : Prop where
  prepare : ∀ pk sk msg other,
    ((components.prepareSigning pk sk msg other).map (fun r => bad r.2.2)) true ≤ indicator (bad other) + B
  open_ : ∀ st d other, ((components.openSigning st d other).map (fun r => bad r.2)) true ≤ indicator (bad other) + B
  verify : ∀ pk msg sig other,
    ((components.prepareVerification pk msg sig other).map (fun r => bad r.2)) true ≤ indicator (bad other) + B
  oracle : ∀ q other, ((components.publicOracle q other).map (fun r => bad r.2)) true ≤ indicator (bad other) + B

/-- The event at an attempt; no event at other terminals. -/
def terminalBad (bad : Other → Bool) :
    Terminal Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query → Bool
  | .attempt a => bad a.world.other
  | _ => false

omit [Fintype Digest] [Nonempty Digest] in
theorem indicator_le_indicator_add (b : Bool) (c : ℝ≥0∞) : indicator b ≤ indicator b + c := le_self_add

omit [Fintype Digest] [Nonempty Digest] in
theorem pure_true_le (b : Bool) (c : ℝ≥0∞) : (PMF.pure b) true ≤ indicator b + c := by
  rw [PMF.pure_apply]
  exact (RandomOracleTrap.ite_le_indicator b).trans le_self_add

omit [Fintype Digest] [Nonempty Digest] in
theorem le_succ_mul (fuel : Nat) (C : ℝ≥0∞) : C ≤ (fuel + 1 : ℕ) * C := by
  calc C = 1 * C := (one_mul C).symm
    _ ≤ (fuel + 1 : ℕ) * C := mul_le_mul_left (by norm_cast; omega) C

omit [Fintype Digest] [Nonempty Digest] in
theorem succ_mul_eq (fuel : Nat) (C : ℝ≥0∞) : (fuel + 1 : ℕ) * C = fuel * C + C := by
  rw [Nat.cast_succ, add_mul, one_mul]

variable (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
  (bad : Other → Bool) (B : ℝ≥0∞)

theorem sign_bound (hb : ServiceBound components bad B) (sk : PublicKey × SecretKey) (message : Message)
    (world : World (HashInput PublicKey Message Payload) Digest Other) :
    (((scheme components).sign sk message world).map (fun r => bad r.2.other)) true ≤ indicator (bad world.other) + (B + B) := by
  dsimp only [scheme]
  rw [← add_assoc]
  refine RandomOracleTrap.bind_map_indicator_le _ _ _ (fun prepared => bad prepared.2.2) B ?_ |>.trans ?_
  · intro prepared _
    rw [PMF.map_bind]
    refine ChallengeMixtures.bind_true_le _ _ _ fun hashResult _ => ?_
    rw [PMF.map_comp]
    exact hb.open_ prepared.2.1 hashResult.1 prepared.2.2
  · exact add_le_add_left (hb.prepare sk.1 sk.2 message world.other) B

theorem verify_bound (hb : ServiceBound components bad B) (pk : PublicKey) (message : Message) (signature : Signature Digest Body)
    (world : World (HashInput PublicKey Message Payload) Digest Other) :
    (((scheme components).prepareVerification pk message signature world).map (fun r => bad r.2.other)) true ≤
      indicator (bad world.other) + B := by
  dsimp only [scheme]
  rw [PMF.map_comp]
  exact hb.verify pk message signature world.other

theorem oracle_bound (hb : ServiceBound components bad B) (query : Query) (world : World (HashInput PublicKey Message Payload) Digest Other) :
    (((scheme components).publicOracle query world).map (fun r => bad r.2.other)) true ≤ indicator (bad world.other) + B := by
  dsimp only [scheme]
  rw [PMF.map_comp]
  exact hb.oracle query world.other

/-- Along the run, the event at the attempt is bounded by its indicator at
the start plus the fuel times twice the service constant. -/
theorem run_event_bound (hb : ServiceBound components bad B) (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : PublicKey × SecretKey) (state : State)
      (world : World (HashInput PublicKey Message Payload) Digest Other)
      (trace : Trace Message (HashInput PublicKey Message Payload) Query),
      ((Spec.SignatureSecurity.run (scheme components) adversary fuel pk sk state world trace).map (terminalBad bad)) true ≤
        indicator (bad world.other) + fuel * (B + B) := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state world trace
    simp [Spec.SignatureSecurity.run, PMF.pure_map, PMF.pure_apply, terminalBad]
  | succ fuel ih =>
    intro pk sk state world trace
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
      · exact (verify_bound components bad B hb pk message signature world).trans
          (add_le_add_right ((le_self_add).trans (le_succ_mul fuel (B + B))) _)
    | sign message next =>
      refine (RandomOracleTrap.bind_map_indicator_le _ _ _
        (fun r : Signature Digest Body × World (HashInput PublicKey Message Payload) Digest Other => bad r.2.other)
        (fuel * (B + B)) fun result _ => ih pk sk (next result.1) result.2 _).trans ?_
      refine (add_le_add_left (sign_bound components bad B hb sk message world) _).trans (le_of_eq ?_)
      rw [succ_mul_eq]
      ring
    | hash input next =>
      rw [PMF.map_bind]
      refine ChallengeMixtures.bind_true_le _ _ _ fun result _ => ?_
      refine (ih pk sk (next result.1) _ _).trans ?_
      show indicator (bad world.other) + _ ≤ _
      exact add_le_add_right (mul_le_mul_left (Nat.cast_le.mpr (Nat.le_succ fuel)) _) _
    | query input next =>
      refine (RandomOracleTrap.bind_map_indicator_le _ _ _
        (fun r : Answer × World (HashInput PublicKey Message Payload) Digest Other => bad r.2.other)
        (fuel * (B + B)) fun result _ => ih pk sk (next result.1) result.2 _).trans ?_
      refine (add_le_add_left (oracle_bound components bad B hb input world) _).trans ?_
      calc indicator (bad world.other) + B + fuel * (B + B)
          ≤ indicator (bad world.other) + (B + B) + fuel * (B + B) := by
            gcongr
            exact le_self_add
        _ = indicator (bad world.other) + (fuel + 1 : ℕ) * (B + B) := by
            rw [succ_mul_eq]
            ring

/-- Finalization keeps the terminal, hence the event. -/
theorem finalize_event (terminal : Terminal Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query) :
    ((finalize terminal).map (fun checked => terminalBad bad checked.terminal)) true ≤ indicator (terminalBad bad terminal) + 0 := by
  rw [add_zero]
  cases terminal with
  | attempt a =>
    simp only [finalize, PMF.map_comp]
    show ((Spec.RandomOracle.query a.world.hashTable a.input).map (fun _ => terminalBad bad (.attempt a))) true ≤ _
    exact le_of_eq (RandomOracleTrap.map_const_true _ _)
  | exhausted t =>
    simp only [finalize, PMF.pure_map, PMF.pure_apply]
    exact RandomOracleTrap.ite_le_indicator _
  | aborted t =>
    simp only [finalize, PMF.pure_map, PMF.pure_apply]
    exact RandomOracleTrap.ite_le_indicator _
  | rejected t =>
    simp only [finalize, PMF.pure_map, PMF.pure_apply]
    exact RandomOracleTrap.ite_le_indicator _

/-- A fresh branch from a snapshot: the event at its attempt is bounded by
its indicator at the snapshot plus the remaining fuel times twice the constant. -/
theorem branch_event_bound (hb : ServiceBound components bad B) (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (snapshot : Snapshot PublicKey (PublicKey × SecretKey) Message (HashInput PublicKey Message Payload) Digest Other Query State) :
    ((freshBranch (scheme components) adversary snapshot).map (fun branch => terminalBad bad branch.checked.terminal)) true ≤
      indicator (bad snapshot.world.other) + snapshot.remaining * (B + B) := by
  simp only [freshBranch, PMF.map_bind]
  refine ChallengeMixtures.bind_true_le _ _ _ fun answer _ => ?_
  rw [PMF.map_comp]
  unfold continueWith
  refine (RandomOracleTrap.bind_map_indicator_le _ _ _ (terminalBad bad) 0 fun terminal _ => ?_).trans ?_
  · exact finalize_event bad terminal
  · rw [add_zero]
    exact run_event_bound components bad B hb adversary snapshot.remaining snapshot.publicKey snapshot.secretKey
      (snapshot.next answer) _ _

end
end SDitH.Proofs.GameEventBound
