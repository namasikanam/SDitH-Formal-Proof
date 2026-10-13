import SDitH.Proofs.RunCongr

/-! The keys a run records. A program querying within a key set records,
over its starting history, only entries whose keys lie in the set. -/

namespace SDitH.Proofs.RunKeys

open Spec.HashCipherProgram (Program procedure)
open Spec.HashCipherTrace (Result runFixed mark)
open Spec.IdealCipher (Family)
open RunCongr PosteriorPrune
open scoped Classical

noncomputable section

variable {Input Digest Key Block A : Type*} [Fintype Digest] [Nonempty Digest]

omit [Fintype Digest] [Nonempty Digest] in
theorem entry_key (request : Spec.IdealCipher.Query Key Block) (value : Block) :
    (Spec.IdealCipher.entry request value).key = keyOf request := by
  cases request <;> rfl

/-- A run querying within a key set records only entries at those keys over
its starting history. -/
theorem runFixed_keys (S : Set Key) (f : Family Key Block) :
    ∀ (fuel : Nat) (p : Program Input Digest Key Block A), QueriesIn S p →
      ∀ (table : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
        (log : List (Spec.RandomOracleTrace.Entry Input Digest)) (out : Result Input Digest Key Block (Program Input Digest Key Block A)),
        out ∈ (runFixed procedure f fuel p table hashes ciphers log).support →
        ∀ e ∈ out.cipherHistory, e ∈ ciphers ∨ e.key ∈ S := by
  intro fuel
  induction fuel with
  | zero =>
    intro p _ table hashes ciphers log out hout e he
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst hout
    exact Or.inl he
  | succ fuel ih =>
    intro p hp table hashes ciphers log out hout e he
    cases p with
    | done v =>
      simp only [runFixed, step_done, PMF.pure_bind, PMF.mem_support_pure_iff] at hout
      subst hout
      exact Or.inl he
    | hash input next =>
      simp only [runFixed, step_hash, PMF.pure_bind] at hout
      obtain ⟨result, -, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      exact ih (next result.1) (hp result.1) _ _ _ _ inner hinner e he
    | cipher request next =>
      simp only [runFixed, step_cipher, PMF.pure_bind] at hout
      rcases ih (next _) (hp.2 _) _ _ _ _ out hout e he with hmem | hS
      · rcases List.mem_cons.mp hmem with rfl | hmem'
        · right
          rw [entry_key]
          exact hp.1
        · exact Or.inl hmem'
      · exact Or.inr hS

end
end SDitH.Proofs.RunKeys
