import SDitH.Proofs.IdealCipher

namespace SDitH.Proofs.IdealCipherTrace

open Spec.IdealCipher
open scoped Classical
noncomputable section

variable {Key Block State : Type*}

/-- Every recorded forward/inverse query is an equation of the same family.
This is derived from execution, including repeats and changes of direction. -/
theorem runFixed_matches (procedure : Procedure Key Block State) (family : Family Key Block)
    (budget : Nat) (state : State) (history : List (Entry Key Block)) (h : Matches family history)
    (out : Result Key Block State) (hout : out ∈ (runFixed procedure family budget state history).support) :
    Matches family out.history := by
  induction budget generalizing state history out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact h
  | succ budget ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      rw [PMF.mem_support_pure_iff] at hnext
      subst out
      exact h
    | query request next =>
      exact ih (next (answer family request)) (entry request (answer family request) :: history)
        ((IdealCipher.matches_cons family history request _).mpr ⟨h, rfl⟩) out hnext

theorem runFixed_history_length (procedure : Procedure Key Block State) (family : Family Key Block)
    (budget : Nat) (state : State) (history : List (Entry Key Block))
    (out : Result Key Block State) (hout : out ∈ (runFixed procedure family budget state history).support) :
    out.history.length ≤ history.length + budget := by
  induction budget generalizing state history out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact Nat.le_refl _
  | succ budget ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      rw [PMF.mem_support_pure_iff] at hnext
      subst out
      exact Nat.le_add_right _ _
    | query request next =>
      have h := ih (next (answer family request)) (entry request (answer family request) :: history) out hnext
      simpa only [List.length_cons, Nat.add_right_comm history.length 1 budget] using h

variable [Fintype Key] [Fintype Block]

theorem runPosterior_invariants (procedure : Procedure Key Block State) (budget : Nat) (state : State)
    (world : World Key Block) (out : Result Key Block State)
    (hout : out ∈ (runPosterior procedure budget state world).support) :
    (∃ family, Matches family out.history) ∧ out.history.length ≤ world.history.length + budget := by
  rw [IdealCipher.runPosterior_eq] at hout
  obtain ⟨family, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  exact ⟨⟨family.val, runFixed_matches procedure family.val budget state world.history family.property out hrun⟩,
    runFixed_history_length procedure family.val budget state world.history out hrun⟩

theorem experiment_invariants (procedure : Procedure Key Block State) (budget : Nat) (initial : State)
    (out : Result Key Block State) (hout : out ∈ (experimentPosterior procedure budget initial).support) :
    (∃ family, Matches family out.history) ∧ out.history.length ≤ budget := by
  simpa only [empty, List.length_nil, Nat.zero_add] using
    runPosterior_invariants procedure budget initial empty out hout

end
end SDitH.Proofs.IdealCipherTrace
