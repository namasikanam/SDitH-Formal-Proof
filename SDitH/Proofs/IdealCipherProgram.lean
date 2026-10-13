import SDitH.Spec.IdealCipherProgram
import SDitH.Proofs.OracleProgram

namespace SDitH.Proofs.IdealCipherProgram

open Spec.IdealCipher Spec.OracleProgram Spec.IdealCipherProgram
open scoped Classical
noncomputable section

variable {Key Block A B : Type*}

theorem execute_bind (family : Family Key Block) (program : Program (Query Key Block) Block A)
    (next : A → Program (Query Key Block) Block B) (history : List (Entry Key Block)) :
    execute family (bind program next) history =
      execute family (next (execute family program history).1) (execute family program history).2 := by
  induction program generalizing history with
  | done value => rfl
  | query request tail ih =>
    exact ih (answer family request) (entry request (answer family request) :: history)

theorem execute_preserves_history (family : Family Key Block)
    (program : Program (Query Key Block) Block A) (history : List (Entry Key Block)) :
    history ⊆ (execute family program history).2 := by
  induction program generalizing history with
  | done value => exact List.Subset.refl _
  | query request next ih =>
    intro e he
    exact ih (answer family request) (entry request (answer family request) :: history) (List.mem_cons_of_mem _ he)

/-- A proved query budget suffices for every answer sequence. This derives
completion and its exact value and graph; no unsuccessful run is discarded. -/
theorem runFixed_execute (family : Family Key Block) (program : Program (Query Key Block) Block A)
    (budget : Nat) (hbound : Bounded budget program) (history : List (Entry Key Block)) :
    runFixed Spec.IdealCipherProgram.procedure family budget program history =
      PMF.pure ⟨.done (execute family program history).1, (execute family program history).2⟩ := by
  induction budget generalizing program history with
  | zero =>
    cases program with
    | done value => rfl
    | query request next => exact False.elim hbound
  | succ budget ih =>
    cases program with
    | done value => simp only [runFixed, Spec.IdealCipherProgram.procedure, PMF.pure_bind, execute]
    | query request next =>
      simp only [runFixed, Spec.IdealCipherProgram.procedure, PMF.pure_bind, execute]
      exact ih (next (answer family request)) (hbound (answer family request)) _

end
end SDitH.Proofs.IdealCipherProgram
