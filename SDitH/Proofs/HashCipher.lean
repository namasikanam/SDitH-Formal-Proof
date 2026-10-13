import SDitH.Spec.HashCipher
import SDitH.Proofs.IdealCipherJoint

namespace SDitH.Proofs.HashCipher

open Spec.HashCipher Spec.IdealCipher
open scoped Classical
noncomputable section

variable {Input Digest Key Block State : Type*}
variable [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]

/-- Exact joint law for an interleaved execution. In particular, observations
of the lazy hash service require no extra conditional-independence premise. -/
theorem runPosterior_eq (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (budget : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (world : World Key Block) :
    Spec.HashCipher.runPosterior procedure budget state table hashes world =
      (PMF.uniformOfFintype (Candidates world)).bind (fun family =>
        (Spec.HashCipher.runFixed procedure family.val budget state table hashes world.history).map fun out => (family.val, out)) := by
  induction budget generalizing state table hashes world with
  | zero =>
    simp only [Spec.HashCipher.runPosterior, Spec.HashCipher.finish, Spec.HashCipher.runFixed, PMF.pure_map]
    rfl
  | succ budget ih =>
    simp only [Spec.HashCipher.runPosterior, Spec.HashCipher.runFixed, PMF.map_bind]
    rw [PMF.bind_comm]
    congr 1
    funext action
    cases action with
    | stop =>
      simp only [Spec.HashCipher.finish, PMF.pure_map]
      rfl
    | cipher request next =>
      simp_rw [ih]
      exact IdealCipherJoint.query_resample world request (fun value history family =>
        (Spec.HashCipher.runFixed procedure family budget (next value) table hashes history).map fun out => (family, out))
    | hash input next =>
      simp only [PMF.map_bind]
      rw [PMF.bind_comm]
      congr 1
      funext result
      simp only [ih, PMF.map_bind, PMF.map_comp, Function.comp_def, markJoint]

theorem experiments_eq (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (budget : Nat) (initial : State) :
    Spec.HashCipher.runPosterior procedure budget initial (fun _ => none) [] empty =
      jointExperiment procedure budget initial := by
  rw [runPosterior_eq, jointExperiment,
    ← IntegerSamplingProbability.map_uniform_equiv (IdealCipher.emptyEquiv (Key := Key) (Block := Block)), PMF.bind_map]
  rfl

theorem joint_assumption_model (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (budget : Nat) (initial : State) :
    jointExperiment procedure budget initial =
      (Assumptions.idealCipherFamily Key Block).bind (fun family =>
        (Spec.HashCipher.runFixed procedure family budget initial (fun _ => none) [] []).map fun out => (family, out)) := rfl

theorem joint_standalone_model (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (budget : Nat) (initial : State) :
    jointExperiment procedure budget initial = Assumptions.sharedOracleModel procedure budget initial := rfl

end
end SDitH.Proofs.HashCipher
