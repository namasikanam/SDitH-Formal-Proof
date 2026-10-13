import SDitH.Spec.HashCipherTrace
import SDitH.Spec.HashCipherProgram

/-! Fuel monotonicity of the traced run. With the deterministic stepping
procedure, a program bounded by a budget runs identically under any larger
budget: each query consumes one unit and the bound decreases, and a
finished program stops without consuming the rest. This is the fuel
accounting used by the run-splitting lemma of the signing procedures'
coupling. -/

namespace SDitH.Proofs.RunFuel

open Spec.HashCipherTrace Spec.HashCipherProgram
open scoped Classical

noncomputable section

variable {Input Digest Key Block A : Type*} [Fintype Digest] [Nonempty Digest]

/-- A bounded program's traced run does not change with extra fuel. -/
theorem runFixed_extra_fuel (family : Spec.IdealCipher.Family Key Block) (n extra : Nat)
    (program : Program Input Digest Key Block A) (hbound : Bounded n program) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Spec.RandomOracleTrace.Entry Input Digest)) :
    runFixed procedure family (n + extra) program table hashes ciphers log =
      runFixed procedure family n program table hashes ciphers log := by
  induction n generalizing program table hashes ciphers log with
  | zero =>
    cases program with
    | done value =>
      cases extra with
      | zero => rfl
      | succ extra => simp [runFixed, procedure]
    | hash input next => exact absurd hbound (by simp [Bounded])
    | cipher request next => exact absurd hbound (by simp [Bounded])
  | succ n ih =>
    cases program with
    | done value =>
      cases extra with
      | zero => rfl
      | succ extra => simp [runFixed, procedure]
    | hash input next =>
      rw [show n + 1 + extra = (n + extra) + 1 by omega]
      have hstep : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block A)).step (.hash input next) = PMF.pure (.hash input next) := rfl
      simp only [runFixed, hstep, PMF.pure_bind]
      congr 1
      funext result
      rw [ih (next result.1) (hbound result.1)]
    | cipher request next =>
      rw [show n + 1 + extra = (n + extra) + 1 by omega]
      have hstep : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block A)).step (.cipher request next) = PMF.pure (.cipher request next) := rfl
      simp only [runFixed, hstep, PMF.pure_bind]
      exact ih _ (hbound _) _ _ _ _

end
end SDitH.Proofs.RunFuel
