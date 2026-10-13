import SDitH.Proofs.AbstractSignature
import SDitH.Proofs.SignatureFork

/-! Oracle consistency for the actual two-continuation signature replay.
These proofs derive persistence from the defined abstract services, without
assuming it as a contract. A successful fork gives two winning attempts at
one input with different final-hash digests. This is not yet PIOP extraction:
different digest strings need not yield usable different algebraic challenges. -/

namespace SDitH.Proofs.SignatureReplayConsistency

open Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open scoped Classical ENNReal
noncomputable section

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

theorem oracle_preserves_answer {Input : Type*}
    (table : Input → Option Digest) (input q : Input) (answer : Digest)
    (hq : table q = some answer) (result : Digest × (Input → Option Digest))
    (hr : result ∈ (Spec.RandomOracle.query table input).support) :
    result.2 q = some answer := by
  unfold Spec.RandomOracle.query at hr
  cases he : table input with
  | some old =>
    rw [he, PMF.mem_support_pure_iff] at hr
    subst result
    exact hq
  | none =>
    rw [he] at hr
    obtain ⟨fresh, _, hresult⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst result
    have hne : q ≠ input := by
      intro h
      subst q
      rw [he] at hq
      contradiction
    simpa [Function.update_of_ne hne] using hq

theorem signing_preserves_answer
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (secret : PublicKey × SecretKey) (message : Message)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (q : HashInput PublicKey Message Payload) (answer : Digest)
    (hq : world.hashTable q = some answer)
    (result : Signature Digest Body × World (HashInput PublicKey Message Payload) Digest Other)
    (hr : result ∈ ((scheme components).sign secret message world).support) :
    result.2.hashTable q = some answer := by
  obtain ⟨prepared, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨hashResult, hhash, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨opened, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst result
  exact oracle_preserves_answer world.hashTable ⟨secret.1, message, prepared.1⟩ q answer hq hashResult hhash

theorem run_preserves_answer
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) (pk : PublicKey) (secret : PublicKey × SecretKey) (state : State)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (trace : Trace Message (HashInput PublicKey Message Payload) Query)
    (q : HashInput PublicKey Message Payload) (answer : Digest)
    (hq : world.hashTable q = some answer)
    (a : Attempt Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (hout : Terminal.attempt a ∈ (run (scheme components) adversary fuel pk secret state world trace).support) :
    a.world.hashTable q = some answer := by
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
        exact hq
    | sign message next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      exact ih (next result.1) result.2 _
        (signing_preserves_answer components secret message world q answer hq result hr) hrest
    | hash input next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      exact ih (next result.1) _ _ (oracle_preserves_answer world.hashTable input q answer hq result hr) hrest
    | query input next =>
      obtain ⟨result, hr, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨output, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst result
      exact ih (next output.1) { world with other := output.2 }
        { trace with publicRequests := input :: trace.publicRequests } hq hrest

theorem finalize_present_target {Sig Input : Type*}
    (a : Attempt Message Sig Input Digest Other Query)
    (checked : Checked Message Sig Input Digest Other Query)
    (hc : checked ∈ (finalize (.attempt a)).support) (hw : checked.wins = true)
    (answer : Digest) (hq : a.world.hashTable a.input = some answer) :
    a.target = answer := by
  simp only [finalize, Spec.RandomOracle.query, hq, PMF.pure_map, PMF.mem_support_pure_iff] at hc
  subst checked
  exact (of_decide_eq_true hw).2.symm

/-- Target-winning branches contain actual fresh-message accepted attempts at
the saved input, and their tested target equals the sampled branch answer. -/
theorem branch_winning_attempt
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (snapshot : Snapshot PublicKey (PublicKey × SecretKey) Message
      (HashInput PublicKey Message Payload) Digest Other Query State)
    (branch : Branch Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (hb : branch ∈ (freshBranch (scheme components) adversary snapshot).support)
    (hw : targetWin snapshot.input branch = true) :
    ∃ a, branch.checked.terminal = .attempt a ∧ a.input = snapshot.input ∧
      a.message ∉ a.trace.signingRequests ∧ a.target = branch.answer ∧
      a.world.hashTable a.input = some branch.answer := by
  obtain ⟨answer, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
  obtain ⟨checked, hc, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst branch
  obtain ⟨terminal, ht, hfinal⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
  have hwin : checked.wins = true := by
    have hh := hw
    simp only [targetWin, Bool.and_eq_true] at hh
    exact hh.1
  obtain ⟨a, he, hchecked, hfresh, _⟩ :=
    SignatureSecurity.finalize_winning_attempt terminal checked hfinal hwin
  subst terminal
  have hinput : a.input = snapshot.input := by
    simpa only [targetWin, hchecked, hwin, Bool.true_and, decide_eq_true_eq] using hw
  have hpersist := run_preserves_answer components adversary snapshot.remaining
    snapshot.publicKey snapshot.secretKey (snapshot.next answer)
    { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some answer) }
    { snapshot.trace with hashRequests := snapshot.input :: snapshot.trace.hashRequests }
    snapshot.input answer (by simp) a ht
  rw [← hinput] at hpersist
  exact ⟨a, hchecked, hinput, hfresh,
    finalize_present_target a checked hfinal hwin answer hpersist, hpersist⟩

/-- The defined successful fork yields two accepted attempts with identical
typed HashPiop input and distinct tested digests. No witness-extraction claim
is hidden in this statement. -/
theorem successful_fork_attempts
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (snapshot : Snapshot PublicKey (PublicKey × SecretKey) Message
      (HashInput PublicKey Message Payload) Digest Other Query State)
    (result : Option (Branch Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query ×
      Branch Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query))
    (hr : result ∈ (forkAt (scheme components) adversary snapshot).support)
    (hw : forkWins snapshot.input result = true) :
    ∃ left right a b, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      left.checked.wins = true ∧ right.checked.wins = true ∧
      a.input = snapshot.input ∧ b.input = snapshot.input ∧
      a.message ∉ a.trace.signingRequests ∧ b.message ∉ b.trace.signingRequests ∧
      a.target ≠ b.target := by
  cases he : snapshot.world.hashTable snapshot.input with
  | some answer =>
    simp only [forkAt, he, PMF.mem_support_pure_iff] at hr
    subst result
    simp [forkWins] at hw
  | none =>
    rw [forkAt, he] at hr
    obtain ⟨left, hl, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    obtain ⟨right, hright, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
    subst result
    have hh : (targetWin snapshot.input left = true ∧ targetWin snapshot.input right = true) ∧
        left.answer ≠ right.answer := by simpa only [forkWins, Bool.and_eq_true, decide_eq_true_eq] using hw
    obtain ⟨a, ha, hai, haf, hat, _⟩ := branch_winning_attempt components adversary snapshot left hl hh.1.1
    obtain ⟨b, hb, hbi, hbf, hbt, _⟩ := branch_winning_attempt components adversary snapshot right hright hh.1.2
    have hlwin : left.checked.wins = true := by
      have h := hh.1.1
      simp only [targetWin, Bool.and_eq_true] at h
      exact h.1
    have hrwin : right.checked.wins = true := by
      have h := hh.1.2
      simp only [targetWin, Bool.and_eq_true] at h
      exact h.1
    exact ⟨left, right, a, b, rfl, ha, hb, hlwin,
      hrwin, hai, hbi, haf, hbf, by simpa only [hat, hbt] using hh.2⟩

end
end SDitH.Proofs.SignatureReplayConsistency
