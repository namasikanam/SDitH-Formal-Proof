import SDitH.Proofs.RunCongr
import SDitH.Proofs.HiddenEntries

/-! Programs under a key relabelling. A program whose cipher requests all
have keys in a set, run against a family that agrees through the
relabelling on that set, gives the relabelled result of its run against
the original family: the same hash queries and answers, the remaining
program relabelled and every recorded cipher entry's key relabelled. A
relabelling that permutes a key list and fixes the other keys does not
change the history pruned at that list. These compare the commitment
phase under the exchange of a leaf's value, whose own key moves. -/

namespace SDitH.Proofs.ProgramRelabel

open Spec.HashCipherProgram (Program procedure)
open Spec.HashCipherTrace (Result runFixed mark)
open Spec.IdealCipher (Family Entry Query)
open PosteriorPrune (keyOf)
open HiddenEntries (pruneAt)
open RunCongr
open scoped Classical

noncomputable section

variable {Input Digest Key Block A B : Type*} [Fintype Digest] [Nonempty Digest]

/-- A request with its key relabelled. -/
def mapKey (ρ : Key → Key) : Query Key Block → Query Key Block
  | .encrypt key input => .encrypt (ρ key) input
  | .decrypt key output => .decrypt (ρ key) output

/-- An entry with its key relabelled. -/
def mapEntry (ρ : Key → Key) (e : Entry Key Block) : Entry Key Block := ⟨ρ e.key, e.input, e.output⟩

/-- A program with every request's key relabelled. -/
def mapKeys (ρ : Key → Key) : Program Input Digest Key Block A → Program Input Digest Key Block A
  | .done v => .done v
  | .hash input next => .hash input fun d => mapKeys ρ (next d)
  | .cipher request next => .cipher (mapKey ρ request) fun b => mapKeys ρ (next b)

omit [Fintype Digest] [Nonempty Digest] in
theorem mapKeys_bind (ρ : Key → Key) (p : Program Input Digest Key Block A) (g : A → Program Input Digest Key Block B) :
    mapKeys ρ (Spec.HashCipherProgram.bind p g) = Spec.HashCipherProgram.bind (mapKeys ρ p) fun v => mapKeys ρ (g v) := by
  induction p with
  | done v => rfl
  | hash input next ih =>
    simp only [Spec.HashCipherProgram.bind, mapKeys]
    congr 1
    funext d
    exact ih d
  | cipher request next ih =>
    simp only [Spec.HashCipherProgram.bind, mapKeys]
    congr 1
    funext b
    exact ih b

omit [Fintype Digest] [Nonempty Digest] in
theorem keyOf_mapKey (ρ : Key → Key) (request : Query Key Block) : keyOf (mapKey ρ request) = ρ (keyOf request) := by
  cases request <;> rfl

omit [Fintype Digest] [Nonempty Digest] in
theorem answer_mapKey (f f' : Family Key Block) (ρ : Key → Key) (request : Query Key Block)
    (h : f' (ρ (keyOf request)) = f (keyOf request)) :
    Spec.IdealCipher.answer f' (mapKey ρ request) = Spec.IdealCipher.answer f request := by
  cases request with
  | encrypt key input =>
    show f' (ρ key) input = f key input
    rw [show f' (ρ key) = f key from h]
  | decrypt key output =>
    show (f' (ρ key)).symm output = (f key).symm output
    rw [show f' (ρ key) = f key from h]

omit [Fintype Digest] [Nonempty Digest] in
theorem entry_mapKey (ρ : Key → Key) (request : Query Key Block) (b : Block) :
    Spec.IdealCipher.entry (mapKey ρ request) b = mapEntry ρ (Spec.IdealCipher.entry request b) := by
  cases request <;> rfl

/-- The relabelled result: the remaining program and the recorded entries
relabelled. -/
def mapResult (ρ : Key → Key) (out : Result Input Digest Key Block (Program Input Digest Key Block A)) :
    Result Input Digest Key Block (Program Input Digest Key Block A) :=
  { out with state := mapKeys ρ out.state, cipherHistory := out.cipherHistory.map (mapEntry ρ) }

/-- A program querying only within a set, run against a family agreeing
through the relabelling on the set, gives the relabelled result of its run
against the family. -/
theorem runFixed_mapKeys (S : Set Key) (f f' : Family Key Block) (ρ : Key → Key) (hff : ∀ κ ∈ S, f' (ρ κ) = f κ) :
    ∀ (fuel : Nat) (p : Program Input Digest Key Block A), QueriesIn S p →
      ∀ (table : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (Entry Key Block))
        (log : List (Spec.RandomOracleTrace.Entry Input Digest)),
        runFixed procedure f' fuel (mapKeys ρ p) table hashes (ciphers.map (mapEntry ρ)) log =
          (runFixed procedure f fuel p table hashes ciphers log).map (mapResult ρ) := by
  intro fuel
  induction fuel with
  | zero => intros; simp only [runFixed, PMF.pure_map]; rfl
  | succ fuel ih =>
    intro p hp table hashes ciphers log
    cases p with
    | done v => simp only [mapKeys, runFixed, step_done, PMF.pure_bind, PMF.pure_map]; rfl
    | hash input next =>
      simp only [mapKeys, runFixed, step_hash, PMF.pure_bind, PMF.map_bind]
      congr 1
      funext result
      rw [ih (next result.1) (hp result.1), PMF.map_comp, PMF.map_comp]
      congr 1
    | cipher request next =>
      simp only [mapKeys, runFixed, step_cipher, PMF.pure_bind]
      rw [answer_mapKey f f' ρ request (hff _ hp.1), entry_mapKey]
      have := ih (next (Spec.IdealCipher.answer f request)) (hp.2 _) table hashes
        (Spec.IdealCipher.entry request (Spec.IdealCipher.answer f request) :: ciphers) log
      simpa only [List.map_cons] using this

omit [Fintype Digest] [Nonempty Digest] in
/-- A relabelling permuting a key list and fixing the other keys does not
change the history pruned at the list. -/
theorem pruneAt_map (K : List Key) (ρ : Key → Key) (hK : ∀ k, ρ k ∈ K ↔ k ∈ K) (hfix : ∀ k, k ∉ K → ρ k = k)
    (H : List (Entry Key Block)) : pruneAt K (H.map (mapEntry ρ)) = pruneAt K H := by
  induction H with
  | nil => rfl
  | cons e H ih =>
    unfold pruneAt at ih ⊢
    simp only [List.map_cons, List.filter_cons]
    by_cases h : e.key ∈ K
    · have h' : (mapEntry ρ e).key ∈ K := (hK e.key).mpr h
      have h1 : decide ((mapEntry ρ e).key ∉ K) = false := decide_eq_false (not_not.mpr h')
      have h2 : decide (e.key ∉ K) = false := decide_eq_false (not_not.mpr h)
      rw [h1, h2, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ih]
    · have h' : mapEntry ρ e = e := by
        unfold mapEntry
        rw [hfix e.key h]
      rw [h', ih]

end
end SDitH.Proofs.ProgramRelabel
