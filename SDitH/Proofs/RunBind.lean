import SDitH.Proofs.RunFuel

/-! The run-splitting lemma. The traced run of a program bind with the
deterministic stepping procedure is the run of the first program followed,
from its final state, by the run of the continuation at its value, with the
collision flags combined; the first program's unused fuel is absorbed by
the continuation's bound through fuel monotonicity. This lets the signing
procedures' runs be split into a witness-free prefix and a
witness-dependent tail. -/

namespace SDitH.Proofs.RunBind

open Spec.HashCipherTrace Spec.HashCipherProgram
open scoped Classical

noncomputable section

variable {Input Digest Key Block A B : Type*} [Fintype Digest] [Nonempty Digest]

/-- The continuation of a split run: from the first run's result, run the
continuation at the finished value and combine the collision flags. -/
def continueRun (family : Spec.IdealCipher.Family Key Block) (m : Nat) (f : A → Program Input Digest Key Block B)
    (out : Result Input Digest Key Block (Program Input Digest Key Block A)) :
    PMF (Result Input Digest Key Block (Program Input Digest Key Block B)) :=
  match out.state with
  | .done v => (runFixed procedure family m (f v) out.hashTable out.hashHistory out.cipherHistory out.trace).map
      fun out' => { out' with hashCollided := out.hashCollided || out'.hashCollided }
  | .hash input next => (runFixed procedure family m (bind (.hash input next) f) out.hashTable out.hashHistory
      out.cipherHistory out.trace).map fun out' => { out' with hashCollided := out.hashCollided || out'.hashCollided }
  | .cipher request next => (runFixed procedure family m (bind (.cipher request next) f) out.hashTable out.hashHistory
      out.cipherHistory out.trace).map fun out' => { out' with hashCollided := out.hashCollided || out'.hashCollided }

theorem continueRun_mark (family : Spec.IdealCipher.Family Key Block) (m : Nat) (f : A → Program Input Digest Key Block B)
    (hit : Bool) (out : Result Input Digest Key Block (Program Input Digest Key Block A)) :
    continueRun family m f (mark hit out) = (continueRun family m f out).map (mark hit) := by
  unfold continueRun mark
  cases out.state <;> simp only [PMF.map_comp] <;> congr 1 <;> funext out' <;> simp [Bool.or_assoc]

/-- The traced run of a bind is the run of the first program continued. -/
theorem runFixed_bind (family : Spec.IdealCipher.Family Key Block) (k m : Nat) (p : Program Input Digest Key Block A)
    (f : A → Program Input Digest Key Block B) (hp : Bounded k p) (hf : ∀ v, Bounded m (f v))
    (table : Input → Option Digest) (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Spec.RandomOracleTrace.Entry Input Digest)) :
    runFixed procedure family (k + m) (bind p f) table hashes ciphers log =
      (runFixed procedure family k p table hashes ciphers log).bind (continueRun family m f) := by
  induction k generalizing p table hashes ciphers log with
  | zero =>
    cases p with
    | done v =>
      rw [show Spec.HashCipherProgram.bind (Program.done v) f = f v from rfl, Nat.zero_add]
      conv_rhs => rw [runFixed]
      simp only [PMF.pure_bind, continueRun, Bool.false_or]
      exact (PMF.map_id _).symm
    | hash input next => exact absurd hp (by simp [Bounded])
    | cipher request next => exact absurd hp (by simp [Bounded])
  | succ k ih =>
    cases p with
    | done v =>
      have hstep : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block A)).step (.done v) = PMF.pure .stop := rfl
      rw [show Spec.HashCipherProgram.bind (Program.done v) f = f v from rfl,
        show k + 1 + m = m + (k + 1) by omega, RunFuel.runFixed_extra_fuel family m (k + 1) (f v) (hf v)]
      conv_rhs => rw [runFixed]
      simp only [hstep, PMF.pure_bind, continueRun, Bool.false_or]
      exact (PMF.map_id _).symm
    | hash input next =>
      have hstepA : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block A)).step (.hash input next) = PMF.pure (.hash input next) := rfl
      have hstepB : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block B)).step (.hash input (fun answer => Spec.HashCipherProgram.bind (next answer) f)) =
          PMF.pure (.hash input (fun answer => Spec.HashCipherProgram.bind (next answer) f)) := rfl
      rw [show Spec.HashCipherProgram.bind (Program.hash input next) f =
        Program.hash input (fun answer => Spec.HashCipherProgram.bind (next answer) f) from rfl,
        show k + 1 + m = (k + m) + 1 by omega]
      simp only [runFixed, hstepA, hstepB, PMF.pure_bind, PMF.bind_bind]
      congr 1
      funext result
      rw [ih (next result.1) (hp result.1), PMF.bind_map, PMF.map_bind]
      congr 1
      funext out
      show (continueRun family m f out).map (mark _) = continueRun family m f (mark _ out)
      exact (continueRun_mark family m f _ out).symm
    | cipher request next =>
      have hstepA : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block A)).step (.cipher request next) = PMF.pure (.cipher request next) := rfl
      have hstepB : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
          (Program Input Digest Key Block B)).step
            (.cipher request (fun answer => Spec.HashCipherProgram.bind (next answer) f)) =
          PMF.pure (.cipher request (fun answer => Spec.HashCipherProgram.bind (next answer) f)) := rfl
      rw [show Spec.HashCipherProgram.bind (Program.cipher request next) f =
        Program.cipher request (fun answer => Spec.HashCipherProgram.bind (next answer) f) from rfl,
        show k + 1 + m = (k + m) + 1 by omega]
      simp only [runFixed, hstepA, hstepB, PMF.pure_bind]
      exact ih _ (hp _) _ _ _ _

end
end SDitH.Proofs.RunBind
