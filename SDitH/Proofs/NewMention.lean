import SDitH.Proofs.TraceSuffix
import SDitH.Proofs.StoredLinesMention
import SDitH.Proofs.ChainFresh
import SDitH.Proofs.InputPresentTail

/-! The prefix event relative to a base log. The event over the first k
entries of a trace checks each against all older entries; relative to a
base log it is the event over the entries newer than the base. It
persists under new entries, is monotone in the count, splits at the
base's head, and is raised by a stored input mentioning one of the new
entries' answers. Its trap bound over a run has no indicator term for
the base log: it is the sum of the per-query steps alone. -/

namespace SDitH.Proofs.NewMention

open Spec.HashCipherTrace Spec.RandomOracleTrace Spec.RandomOracleMention Spec.RandomOracleTrap Spec.ProductOracle
open Spec.HashCipherProgram
open TraceSuffix InputPresentTail SignCompare
open scoped Classical ENNReal BigOperators

noncomputable section

section Event

variable {Input Digest : Type*}

/-- The prefix event over the first k entries, each checked against all
older entries. -/
def prefixBadN (bad : List (Entry Input Digest) → Input → Digest → Bool) :
    Nat → List (Entry Input Digest) → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | k + 1, entry :: rest => bad rest entry.input entry.answer || prefixBadN bad k rest

theorem prefixBadN_cons (bad : List (Entry Input Digest) → Input → Digest → Bool) (k : Nat) (entry : Entry Input Digest)
    (rest : List (Entry Input Digest)) :
    prefixBadN bad (k + 1) (entry :: rest) = (bad rest entry.input entry.answer || prefixBadN bad k rest) := rfl

/-- The event splits at a list boundary. -/
theorem prefixBadN_append (bad : List (Entry Input Digest) → Input → Digest → Bool) (new rest : List (Entry Input Digest))
    (k : Nat) :
    prefixBadN bad (new.length + k) (new ++ rest) = (prefixBadN bad new.length (new ++ rest) || prefixBadN bad k rest) := by
  induction new with
  | nil => simp [prefixBadN]
  | cons e new ih =>
    rw [List.cons_append, List.length_cons, show new.length + 1 + k = (new.length + k) + 1 by omega, prefixBadN_cons,
      prefixBadN_cons, ih, Bool.or_assoc]

/-- Monotone in the count. -/
theorem prefixBadN_mono (bad : List (Entry Input Digest) → Input → Digest → Bool) (k k' : Nat)
    (trace : List (Entry Input Digest)) (hk : k ≤ k') (h : prefixBadN bad k trace = true) : prefixBadN bad k' trace = true := by
  induction trace generalizing k k' with
  | nil =>
    cases k with
    | zero => simp [prefixBadN] at h
    | succ k => simp [prefixBadN] at h
  | cons e rest ih =>
    cases k with
    | zero => simp [prefixBadN] at h
    | succ k =>
      obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
      rw [prefixBadN_cons] at h ⊢
      rcases Bool.or_eq_true_iff.mp h with h1 | h1
      · rw [h1, Bool.true_or]
      · rw [ih k k'' (by omega) h1, Bool.or_true]

/-- Persistence under new entries in front. -/
theorem prefixBadN_persist (bad : List (Entry Input Digest) → Input → Digest → Bool) (new rest : List (Entry Input Digest))
    (k : Nat) (h : prefixBadN bad k rest = true) : prefixBadN bad (new.length + k) (new ++ rest) = true := by
  rw [prefixBadN_append, h, Bool.or_true]

/-- The event relative to a base log: the entries newer than the base. -/
def newBad (bad : List (Entry Input Digest) → Input → Digest → Bool) (base trace : List (Entry Input Digest)) : Bool :=
  prefixBadN bad (trace.length - base.length) trace

/-- Relative to the base, a trace extending the base's extension by one
entry raises the event iff the extension does or the entry's check does. -/
theorem newBad_cons (bad : List (Entry Input Digest) → Input → Digest → Bool) (base : List (Entry Input Digest))
    (e : Entry Input Digest) (new : List (Entry Input Digest)) :
    newBad bad base (new ++ e :: base) = (newBad bad (e :: base) (new ++ e :: base) || bad base e.input e.answer) := by
  unfold newBad
  rw [List.length_append, List.length_cons,
    show new.length + (base.length + 1) - base.length = new.length + 1 by omega,
    show new.length + (base.length + 1) - (base.length + 1) = new.length + 0 by omega, prefixBadN_append,
    prefixBadN_append, prefixBadN_cons]
  simp [prefixBadN]

/-- The base itself raises no relative event. -/
theorem newBad_self (bad : List (Entry Input Digest) → Input → Digest → Bool) (base : List (Entry Input Digest)) :
    newBad bad base base = false := by
  simp [newBad, prefixBadN]

variable {D M : Type*}

/-- A stored input mentioning the newest answer, which is new. -/
theorem prefixBadN_of_stored_head (mentions : Input → Finset D) (table : Input → Option (D × M))
    (newest : Entry Input (D × M)) (older : List (Entry Input (D × M))) (htraced : Traced table (newest :: older))
    (L : Input) (d : D × M) (hstored : table L = some d) (hne : L ≠ newest.input)
    (hmention : newest.answer.1 ∈ mentions L) (k : Nat) :
    prefixBadN (digestMention mentions) (k + 1) (newest :: older) = true := by
  obtain ⟨entry, hentry, hinput, _, _, _⟩ := htraced.1 L d hstored
  have holder : entry ∈ older := by
    simp only [List.mem_cons] at hentry
    rcases hentry with h | h
    · exact absurd (by rw [← hinput, h]) hne
    · exact h
  have hhead : digestMention mentions older newest.input newest.answer = true := by
    unfold digestMention
    rw [List.any_eq_true]
    exact ⟨entry, holder, by rw [hinput]; exact decide_eq_true hmention⟩
  rw [prefixBadN_cons, hhead, Bool.true_or]

/-- A stored input mentioning the second newest answer, which is new. -/
theorem prefixBadN_of_stored (mentions : Input → Finset D) (table : Input → Option (D × M))
    (newest auxEntry : Entry Input (D × M)) (older : List (Entry Input (D × M)))
    (htraced : Traced table (newest :: auxEntry :: older)) (L : Input) (d : D × M) (hstored : table L = some d)
    (hne1 : L ≠ newest.input) (hne2 : L ≠ auxEntry.input) (hmention : auxEntry.answer.1 ∈ mentions L) (k : Nat) :
    prefixBadN (digestMention mentions) (k + 2) (newest :: auxEntry :: older) = true := by
  obtain ⟨entry, hentry, hinput, _, _, _⟩ := htraced.1 L d hstored
  have holder : entry ∈ older := by
    simp only [List.mem_cons] at hentry
    rcases hentry with h | h | h
    · exact absurd (by rw [← hinput, h]) hne1
    · exact absurd (by rw [← hinput, h]) hne2
    · exact h
  have hmid : digestMention mentions older auxEntry.input auxEntry.answer = true := by
    unfold digestMention
    rw [List.any_eq_true]
    exact ⟨entry, holder, by rw [hinput]; exact decide_eq_true hmention⟩
  rw [prefixBadN_cons, prefixBadN_cons, hmid, Bool.true_or, Bool.or_true]

end Event

section Bound

/-- Two Boolean maps agreeing on the support have the same mass at true,
stated as a bound. -/
theorem map_true_le_of_support {A : Type*} (p : PMF A) (f g : A → Bool) (h : ∀ a ∈ p.support, f a = g a) :
    (p.map f) true ≤ (p.map g) true := by
  rw [RandomOracleTrap.map_true_eq, RandomOracleTrap.map_true_eq]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

variable {Input Digest Key Block State : Type*} [Fintype Digest] [Nonempty Digest]

/-- The relative event's trap bound over a run: the per-query steps alone. -/
theorem run_prefix_boundN (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Spec.IdealCipher.Family Key Block) (bad : List (Entry Input Digest) → Input → Digest → Bool)
    (epsilon : Nat → ℝ≥0∞)
    (hbad : ∀ log input, ((PMF.uniformOfFintype Digest).map (bad log input)) true ≤ epsilon log.length)
    (fuel : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest)) :
    ((runFixed procedure family fuel state table hashes ciphers log).map (fun out => newBad bad log out.trace)) true ≤
      ∑ i ∈ Finset.range fuel, epsilon (log.length + i) := by
  induction fuel generalizing state table hashes ciphers log with
  | zero =>
    simp only [runFixed, PMF.pure_map, PMF.pure_apply, Finset.range_zero, Finset.sum_empty, newBad_self]
    simp
  | succ fuel ih =>
    simp only [runFixed, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      simp only [PMF.pure_map, PMF.pure_apply, newBad_self]
      simp
    | hash input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, HashCipherTrace.mark_trace]
      cases he : table input with
      | some old =>
        have hrec : record table input old log = log := by simp [record, he]
        simp only [Spec.RandomOracle.query, he, PMF.pure_bind, hrec]
        refine (ih (next old) table ((input, old) :: hashes) ciphers log).trans ?_
        rw [Finset.sum_range_succ]
        exact le_self_add
      | none =>
        rw [query_bind_fresh' table input he]
        refine (bind_true_le_event_add _ _ (fun answer => bad log input answer)
          (∑ i ∈ Finset.range fuel, epsilon (log.length + 1 + i)) (fun answer _ hb => ?_)).trans ?_
        · have hrec : record table input answer log = ⟨table, input, answer⟩ :: log := by simp [record, he]
          rw [hrec]
          have hpt : ∀ out ∈ (runFixed procedure family fuel (next answer) (Function.update table input (some answer))
              ((input, answer) :: hashes) ciphers (⟨table, input, answer⟩ :: log)).support,
              newBad bad log out.trace = newBad bad (⟨table, input, answer⟩ :: log) out.trace := by
            intro out hout
            obtain ⟨new, hnew⟩ := runFixed_trace_suffix procedure family fuel _ _ _ ciphers _ out hout
            rw [hnew, newBad_cons]
            dsimp only at hb ⊢
            rw [hb, Bool.or_false]
          refine (map_true_le_of_support _ _ _ hpt).trans ?_
          have := ih (next answer) (Function.update table input (some answer)) ((input, answer) :: hashes) ciphers
            (⟨table, input, answer⟩ :: log)
          rwa [List.length_cons] at this
        · calc _ ≤ epsilon log.length + ∑ i ∈ Finset.range fuel, epsilon (log.length + 1 + i) :=
                add_le_add (hbad log input) le_rfl
            _ = _ := RandomOracleMention.sum_shift epsilon log.length fuel
    | cipher request next =>
      refine (ih _ table hashes _ log).trans ?_
      rw [Finset.sum_range_succ]
      exact le_self_add

end Bound

end
end SDitH.Proofs.NewMention
