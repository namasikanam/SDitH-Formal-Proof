import SDitH.Proofs.RunCongr

/-! A run's dependence on its starting cipher history. The starting history
is only appended to: the run from a history is the run from the empty
history with the history appended to the result's cipher history. -/

namespace SDitH.Proofs.RunHistoryShift

open Spec.HashCipherProgram (Program procedure)
open Spec.HashCipherTrace (Result runFixed mark)
open Spec.IdealCipher (Family)
open RunCongr
open scoped Classical

noncomputable section

variable {Input Digest Key Block A : Type*} [Fintype Digest] [Nonempty Digest]

/-- The result with a history appended to its cipher history. -/
def appendHistory (ciphers : List (Spec.IdealCipher.Entry Key Block)) (out : Result Input Digest Key Block A) :
    Result Input Digest Key Block A :=
  { out with cipherHistory := out.cipherHistory ++ ciphers }

/-- The run from a history is the run from the empty history with the
history appended. -/
theorem runFixed_history_shift (f : Family Key Block) :
    ∀ (fuel : Nat) (p : Program Input Digest Key Block A) (table : Input → Option Digest) (hashes : List (Input × Digest))
      (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Spec.RandomOracleTrace.Entry Input Digest)),
      runFixed procedure f fuel p table hashes ciphers log =
        (runFixed procedure f fuel p table hashes [] log).map (appendHistory ciphers) := by
  intro fuel
  induction fuel with
  | zero => intros; simp only [runFixed, PMF.pure_map, appendHistory, List.nil_append]
  | succ fuel ih =>
    intro p table hashes ciphers log
    cases p with
    | done v => simp only [runFixed, step_done, PMF.pure_bind, PMF.pure_map, appendHistory, List.nil_append]
    | hash input next =>
      simp only [runFixed, step_hash, PMF.pure_bind, PMF.map_bind]
      congr 1
      funext result
      rw [ih (next result.1), PMF.map_comp, PMF.map_comp]
      rfl
    | cipher request next =>
      simp only [runFixed, step_cipher, PMF.pure_bind]
      rw [ih (next _) table hashes (Spec.IdealCipher.entry request _ :: ciphers), ih (next _) table hashes [_]]
      rw [PMF.map_comp]
      congr 1
      funext out
      simp [appendHistory, List.append_assoc]

end
end SDitH.Proofs.RunHistoryShift
