import SDitH.Proofs.IdealCipher
import SDitH.Spec.SharedScheme

/-! Resampling the hidden cipher family from the posterior of the cipher
history. A shared program run against a family drawn from the posterior
of the starting history, followed by any continuation, equals the same
run followed by a fresh posterior draw at the resulting history before the
continuation: the family can be lazily resampled after every program.
This is the fixed-family counterpart, for the shared hash/cipher
interpreter, of the posterior-step law of the ideal cipher. -/

namespace SDitH.Proofs.CipherResample

open Spec.IdealCipher (Family Entry Matches Candidates World observe answer entry)
open Spec.HashCipher (Procedure)
open Spec.HashCipherTrace (Result runFixed mark)
open scoped Classical ENNReal

noncomputable section

variable {Key Block : Type*} [Fintype Key] [Fintype Block]

/-- The posterior family of a history: uniform among the families matching
it, or the identity family when none does. -/
def posterior (history : List (Entry Key Block)) : PMF (Family Key Block) :=
  if h : ∃ family : Family Key Block, Matches family history then
    (PMF.uniformOfFintype (Candidates (⟨history, h⟩ : World Key Block))).map Subtype.val
  else PMF.pure fun _ => Equiv.refl Block

/-- The posterior of a world's history is the uniform candidate family. -/
theorem posterior_world (world : World Key Block) :
    posterior world.history = (PMF.uniformOfFintype (Candidates world)).map Subtype.val := by
  unfold posterior
  rw [dif_pos world.possible]

/-- Resampling then ignoring the sample is no resampling. -/
theorem posterior_bind_const {R : Type*} (history : List (Entry Key Block)) (q : PMF R) :
    (posterior history).bind (fun _ => q) = q :=
  PMF.bind_const _ _

variable {Input Digest State R : Type*} [Fintype Digest] [Nonempty Digest]

/-- The resampling law of the shared interpreter: a run against a posterior
family, then a continuation of the result and the family, equals the run
followed by a fresh posterior draw at the resulting cipher history. -/
theorem runFixed_resample (procedure : Procedure Input Digest Key Block State) (fuel : Nat) (state : State)
    (table : Input → Option Digest) (hashes : List (Input × Digest)) (world : World Key Block)
    (log : List (Spec.RandomOracleTrace.Entry Input Digest))
    (next : Result Input Digest Key Block State → Family Key Block → PMF R) :
    (posterior world.history).bind (fun family =>
      (runFixed procedure family fuel state table hashes world.history log).bind fun out => next out family) =
    (posterior world.history).bind (fun family =>
      (runFixed procedure family fuel state table hashes world.history log).bind fun out =>
        (posterior out.cipherHistory).bind fun family' => next out family') := by
  induction fuel generalizing state table hashes world log next with
  | zero =>
    simp only [runFixed, PMF.pure_bind]
    rw [posterior_bind_const]
  | succ fuel ih =>
    simp only [runFixed, PMF.bind_bind]
    rw [PMF.bind_comm]
    conv_rhs => rw [PMF.bind_comm]
    congr 1
    funext action
    cases action with
    | stop =>
      simp only [PMF.pure_bind]
      rw [posterior_bind_const]
    | hash input next' =>
      simp only [PMF.bind_bind, PMF.bind_map]
      rw [PMF.bind_comm]
      conv_rhs => rw [PMF.bind_comm]
      congr 1
      funext result
      exact ih (next' result.1) result.2 _ world _ (fun out family =>
        next (mark (Spec.RandomOracleCollision.freshHit table hashes input result.1) out) family)
    | cipher request next' =>
      rw [posterior_world, PMF.bind_map, PMF.bind_map]
      have hstep := IdealCipher.posterior_step world request (fun value history family =>
        (runFixed procedure family fuel (next' value) table hashes history log).bind fun out => next out family)
      have hstep' := IdealCipher.posterior_step world request (fun value history family =>
        (runFixed procedure family fuel (next' value) table hashes history log).bind fun out =>
          (posterior out.cipherHistory).bind fun family' => next out family')
      simp only [Function.comp_def] at hstep hstep' ⊢
      rw [← hstep, ← hstep']
      congr 1
      funext sample
      have hpost := ih (next' (answer sample.val request)) table hashes
        (observe world request (answer sample.val request) ⟨sample.val, sample.property, rfl⟩) log next
      simp only [posterior_world, PMF.bind_map, Function.comp_def] at hpost
      exact hpost

section Shared

variable {lambda s wit rnd : Nat}

/-- Resampling a shared world's family from the posterior of its cipher
history. -/
def resample (world : Spec.SharedScheme.World lambda s wit rnd) : PMF (Spec.SharedScheme.World lambda s wit rnd) :=
  (posterior world.cipherHistory).map fun family => { world with family := family }

/-- Resampling twice is resampling once. -/
theorem resample_bind_resample (world : Spec.SharedScheme.World lambda s wit rnd)
    (g : Spec.SharedScheme.World lambda s wit rnd → PMF R) :
    (resample world).bind (fun w => (resample w).bind g) = (resample world).bind g := by
  unfold resample
  simp only [PMF.bind_map, Function.comp_def]
  exact posterior_bind_const _ _

/-- The resampling law of a shared program run: against a resampled world,
a run then a continuation equals the run, a fresh resampling of the result
world, then the continuation. -/
theorem runProgram_resample {A : Type*} (budget : Nat)
    (program : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Spec.DomainSeparation.Bits lambda)
      (Spec.DomainSeparation.Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd)
    (hpos : ∃ family : Family (Spec.DomainSeparation.Bits lambda) (Spec.DomainSeparation.Bits lambda), Matches family world.cipherHistory)
    (K : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Spec.DomainSeparation.Bits lambda)
      (Spec.DomainSeparation.Bits lambda) A × Spec.SharedScheme.World lambda s wit rnd → PMF R) :
    (resample world).bind (fun w => (Spec.SharedScheme.runProgram budget program w).bind K) =
    (resample world).bind (fun w => (Spec.SharedScheme.runProgram budget program w).bind fun r =>
      (resample r.2).bind fun w' => K (r.1, w')) := by
  have h := runFixed_resample Spec.HashCipherProgram.procedure budget program world.hashTable world.hashHistory
    ⟨world.cipherHistory, hpos⟩ world.trace
    (fun out family => K (out.state, ⟨family, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩))
  simp only [resample, Spec.SharedScheme.runProgram, PMF.bind_map, Function.comp_def]
  exact h

end Shared

end
end SDitH.Proofs.CipherResample
