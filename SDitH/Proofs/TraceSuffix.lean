import SDitH.Proofs.HeadLastRun

/-! The mention event persists along a run. A run's trace is its starting
log with new entries in front, so a prefix event raised on the starting log
is raised on the run's trace; the same holds for a continuation from a
finished state. This lifts the mention events raised after the head (the
outer string) to the whole prefix run and to the tail's run. -/

namespace SDitH.Proofs.TraceSuffix

open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.HashCipherProgram
open RunBind PrefixLinesFreshRun
open scoped Classical

noncomputable section

variable {Input Digest Key Block State A B : Type*}

/-- A prefix event on a log is raised on any extension of the log. -/
theorem prefixBad_append (bad : List (Entry Input Digest) → Input → Digest → Bool) (new log : List (Entry Input Digest))
    (h : prefixBad bad log = true) : prefixBad bad (new ++ log) = true := by
  induction new with
  | nil => simpa using h
  | cons entry rest ih =>
    rw [List.cons_append, RandomOracleMention.prefixBad_cons, ih, Bool.or_true]

/-- The recorded log is the log with at most one new entry in front. -/
theorem record_suffix (table : Input → Option Digest) (input : Input) (answer : Digest) (log : List (Entry Input Digest)) :
    ∃ new, record table input answer log = new ++ log := by
  unfold record
  cases table input with
  | none => exact ⟨[⟨table, input, answer⟩], rfl⟩
  | some _ => exact ⟨[], rfl⟩

variable [Fintype Digest] [Nonempty Digest]

/-- A run's trace is its starting log with new entries in front. -/
theorem runFixed_trace_suffix (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Spec.IdealCipher.Family Key Block) (fuel : Nat) (state : State) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support) :
    ∃ new, out.trace = new ++ log := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact ⟨[], rfl⟩
  | succ fuel ih =>
    simp only [runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst out
      exact ⟨[], rfl⟩
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      obtain ⟨new0, hrec⟩ := record_suffix table input result.1 log
      obtain ⟨new, hnew⟩ := ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers
        (record table input result.1 log) inner hinner
      refine ⟨new ++ new0, ?_⟩
      rw [HashCipherTrace.mark_trace, hnew, hrec, List.append_assoc]
    | cipher request next =>
      exact ih _ table hashes _ log out hrest

/-- A prefix event on the starting log is raised on the run's trace. -/
theorem runFixed_prefixBad (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Spec.IdealCipher.Family Key Block) (bad : List (Entry Input Digest) → Input → Digest → Bool) (fuel : Nat)
    (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support)
    (h : prefixBad bad log = true) : prefixBad bad out.trace = true := by
  obtain ⟨new, hnew⟩ := runFixed_trace_suffix procedure family fuel state table hashes ciphers log out hout
  rw [hnew]
  exact prefixBad_append bad new log h

/-- A prefix event on a finished result's trace is raised on the trace of
any continuation from it. -/
theorem continueRun_prefixBad (family : Spec.IdealCipher.Family Key Block)
    (bad : List (Entry Input Digest) → Input → Digest → Bool) (m : Nat) (f : A → Program Input Digest Key Block B)
    (mid : Result Input Digest Key Block (Program Input Digest Key Block A)) (v : A) (hmid : mid.state = .done v)
    (out : Result Input Digest Key Block (Program Input Digest Key Block B))
    (hout : out ∈ (continueRun family m f mid).support) (h : prefixBad bad mid.trace = true) :
    prefixBad bad out.trace = true := by
  obtain ⟨out', hout', _, _, htrace⟩ := continueRun_done_support family m f mid v hmid out hout
  rw [htrace]
  exact runFixed_prefixBad procedure family bad m (f v) mid.hashTable mid.hashHistory mid.cipherHistory mid.trace out'
    hout' h

end
end SDitH.Proofs.TraceSuffix
