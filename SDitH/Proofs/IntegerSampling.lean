import SDitH.Spec.IntegerSampling
import SDitH.Proofs.ByteSampling
import Mathlib.Tactic

namespace SDitH.Proofs.IntegerSampling

set_option maxRecDepth 4096

open Spec.IntegerSampling Spec.ByteSampling Spec.DomainSeparation
open scoped BigOperators

theorem word32_formula (bytes : Fin 4 → Byte) :
    (word32 bytes).val = (bytes 0).val + 256 * (bytes 1).val +
      256 ^ 2 * (bytes 2).val + 256 ^ 3 * (bytes 3).val := by
  change (∑ j : Fin 4, (bytes j).val * 256 ^ j.val) = _
  norm_num [Fin.sum_univ_succ, Nat.mul_comm]
  rw [show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
  omega

theorem word32_bijective : Function.Bijective word32 := wordEquiv.bijective

/-- Each original byte is recovered by division and remainder at its stated
little-endian position. This proves the representation, not PRG uniformity. -/
theorem byte_of_word32 (bytes : Fin 4 → Byte) (j : Fin 4) :
    (word32 bytes).val / 256 ^ j.val % 256 = (bytes j).val := by
  have h := congrArg (fun f : Fin 4 → Byte => (f j).val) (wordEquiv.symm_apply_apply bytes)
  exact h

theorem threshold_le (bound m : Nat) : threshold bound m ≤ bound :=
  Nat.div_mul_le_self bound m

theorem threshold_multiple (bound m : Nat) : m ∣ threshold bound m := by
  exact ⟨bound / m, Nat.mul_comm _ _⟩

theorem threshold_maximal (bound m candidate : Nat) (hm : 0 < m)
    (hmultiple : m ∣ candidate) (hle : candidate ≤ bound) :
    candidate ≤ threshold bound m := by
  obtain ⟨q, rfl⟩ := hmultiple
  have hq : q ≤ bound / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa [Nat.mul_comm] using hle)
  simpa only [threshold, Nat.mul_comm] using Nat.mul_le_mul_right m hq

theorem threshold_remainder (bound m : Nat) : bound - threshold bound m = bound % m := by
  have h := Nat.mod_add_div bound m
  unfold threshold
  rw [Nat.mul_comm m] at h
  omega

theorem threshold_pos (bound m : Nat) (hm : 0 < m) (hmb : m ≤ bound) :
    0 < threshold bound m := by
  exact Nat.mul_pos ((Nat.one_le_div_iff hm).mpr hmb) hm

/-- A rejection discards fewer than m words, and fewer than half of all
words whenever 1 <= m <= bound. No infinite-loop success is assumed. -/
theorem rejected_twice_lt_bound (bound m : Nat) (hm : 0 < m) (hmb : m ≤ bound) :
    2 * (bound - threshold bound m) < bound := by
  rw [threshold_remainder]
  have hmod := Nat.mod_lt bound hm
  have hdiv : 1 ≤ bound / m := (Nat.one_le_div_iff hm).mpr hmb
  have hmul : m ≤ m * (bound / m) := by nlinarith
  have he := Nat.mod_add_div bound m
  omega

theorem readCandidate_cursor (src : Reader) :
    (readCandidate src).next.position = src.position + 4 := rfl

theorem readCandidate_bound (src : Reader) : (readCandidate src).value < wordBound :=
  (word32 (readBytes src 4)).isLt

theorem readCandidate_value (src : Reader) :
    (readCandidate src).value = (src.stream src.position).val +
      256 * (src.stream (src.position + 1)).val +
      256 ^ 2 * (src.stream (src.position + 2)).val +
      256 ^ 3 * (src.stream (src.position + 3)).val := by
  simpa [readCandidate, readBytes] using word32_formula (readBytes src 4)

theorem attemptWith_accepted_iff (limit : Nat) (read : Reader → Candidate)
    (src : Reader) (candidate : Candidate) :
    attemptWith limit read src = .accepted candidate ↔ candidate = read src ∧
      (read src).value < limit := by
  unfold attemptWith
  dsimp only
  split <;> simp_all [eq_comm]

theorem attempt_accepted_iff (m : Nat) (src : Reader) (candidate : Candidate) :
    attempt m src = .accepted candidate ↔ candidate = readCandidate src ∧
      (readCandidate src).value < sourceThreshold m :=
  attemptWith_accepted_iff (sourceThreshold m) readCandidate src candidate

/-- A found observation is an accepted candidate after some number of rejected
four-byte reads, with the corresponding exact final cursor. -/
private theorem found_cursor_general (limit : Nat) (read : Reader → Candidate)
    (hread : ∀ src, (read src).next = advance src 4)
    (fuel : Nat) (src : Reader) (candidate : Candidate)
    (h : observeWith limit read fuel src = .found candidate) :
    ∃ attempts : Nat, 0 < attempts ∧ attempts ≤ fuel ∧
      candidate.next.position = src.position + 4 * attempts ∧
      candidate.next.stream = src.stream ∧ candidate.value < limit := by
  induction fuel generalizing src with
  | zero => simp [observeWith] at h
  | succ fuel ih =>
    cases he : attemptWith limit read src with
    | accepted result =>
      simp only [observeWith, he, Observation.found.injEq] at h
      subst result
      obtain ⟨rfl, hbound⟩ := (attemptWith_accepted_iff limit read src candidate).mp he
      rw [hread]
      exact ⟨1, by omega, by omega, by simp [advance], rfl, hbound⟩
    | rejected next =>
      have hn : next = advance src 4 := by
        unfold attemptWith at he
        dsimp only at he
        split at he <;> simp_all
      subst next
      simp only [observeWith, he] at h
      obtain ⟨attempts, hpos, hle, hcursor, hstream, hbound⟩ := ih (advance src 4) h
      simp only [advance] at hcursor hstream
      exact ⟨attempts + 1, by omega, by omega, by omega,
        hstream, hbound⟩

theorem found_cursor (m fuel : Nat) (src : Reader) (candidate : Candidate)
    (h : observeCandidate m fuel src = .found candidate) :
    ∃ attempts : Nat, 0 < attempts ∧ attempts ≤ fuel ∧
      candidate.next.position = src.position + 4 * attempts ∧
      candidate.next.stream = src.stream ∧ candidate.value < sourceThreshold m :=
  found_cursor_general (sourceThreshold m) readCandidate (fun _ => rfl) fuel src candidate h

private theorem found_stable_general (limit : Nat) (read : Reader → Candidate)
    (fuel extra : Nat) (src : Reader) (candidate : Candidate)
    (h : observeWith limit read fuel src = .found candidate) :
    observeWith limit read (fuel + extra) src = .found candidate := by
  induction fuel generalizing src with
  | zero => simp [observeWith] at h
  | succ fuel ih =>
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
    cases he : attemptWith limit read src with
    | accepted result => simpa only [observeWith, he] using h
    | rejected next =>
      simp only [observeWith, he] at h ⊢
      exact ih next h

/-- Observing more iterations cannot change an already found candidate. It
remains the first accepted read; this does not complete the undefined assignment. -/
theorem found_stable (m fuel extra : Nat) (src : Reader) (candidate : Candidate)
    (h : observeCandidate m fuel src = .found candidate) :
    observeCandidate m (fuel + extra) src = .found candidate :=
  found_stable_general (sourceThreshold m) readCandidate fuel extra src candidate h

private theorem first_accepted_general (limit : Nat) (read : Reader → Candidate) (src : Reader)
    (h : (read src).value < limit) :
    observeWith limit read 1 src = .found (read src) := by
  simp [observeWith, attemptWith, h]

/-- The undefined assignment is reachable for every legal nonempty range:
an all-zero byte stream reaches it after exactly the first four-byte read.
This is a fact about a concrete stream, not an assertion that a PRG emits it. -/
theorem zero_stream_reaches_assignment (m : Nat) (hm : 0 < m) (hmb : m ≤ wordBound)
    (position : Nat) :
    let src : Reader := ⟨fun _ => 0, position⟩
    observeCandidate m 1 src = .found (readCandidate src) ∧
      (readCandidate src).value = 0 ∧ (readCandidate src).next.position = position + 4 := by
  let src : Reader := ⟨fun _ => 0, position⟩
  have hz : (readCandidate src).value = 0 := by
    rw [readCandidate_value]
    norm_num [src]
  have ht := threshold_pos wordBound m hm hmb
  exact ⟨first_accepted_general (sourceThreshold m) readCandidate src (by simpa [hz, sourceThreshold] using ht), hz, rfl⟩

end SDitH.Proofs.IntegerSampling
