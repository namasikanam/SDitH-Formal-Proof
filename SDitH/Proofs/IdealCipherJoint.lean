import SDitH.Spec.IdealCipherJoint
import SDitH.Proofs.IdealCipher

namespace SDitH.Proofs.IdealCipherJoint

open Spec.IdealCipher
open scoped Classical
noncomputable section

variable {Key Block State R : Type*} [Fintype Key] [Fintype Block]

theorem query_resample (world : World Key Block) (request : Query Key Block)
    (next : Block → List (Entry Key Block) → Family Key Block → PMF R) :
    (query world request).bind (fun result =>
      (PMF.uniformOfFintype (Candidates result.2)).bind fun family =>
        next result.1 result.2.history family.val) =
    (PMF.uniformOfFintype (Candidates world)).bind (fun family =>
      next (answer family.val request) (entry request (answer family.val request) :: world.history) family.val) := by
  simp only [query, PMF.bind_map, Function.comp_def]
  exact IdealCipher.posterior_step world request next

/-- Preserve the complete joint law, including any terminal predicate of the
hidden family. The earlier transcript-only equality is a marginal of this law. -/
theorem runPosterior_eq (procedure : Procedure Key Block State) (budget : Nat)
    (state : State) (world : World Key Block) :
    Spec.IdealCipherJoint.runPosterior procedure budget state world =
      (PMF.uniformOfFintype (Candidates world)).bind (fun family =>
        (runFixed procedure family.val budget state world.history).map fun out => (family.val, out)) := by
  induction budget generalizing state world with
  | zero =>
    simp only [Spec.IdealCipherJoint.runPosterior, Spec.IdealCipherJoint.finish, runFixed, PMF.pure_map]
    rfl
  | succ budget ih =>
    simp only [Spec.IdealCipherJoint.runPosterior, runFixed, PMF.map_bind]
    rw [PMF.bind_comm]
    congr 1
    funext action
    cases action with
    | stop =>
      simp only [Spec.IdealCipherJoint.finish, PMF.pure_map]
      rfl
    | query request next =>
      simp_rw [ih]
      exact query_resample world request (fun value history family =>
        (runFixed procedure family budget (next value) history).map fun out => (family, out))

theorem experiment_eq (procedure : Procedure Key Block State) (budget : Nat) (initial : State) :
    Spec.IdealCipherJoint.experiment procedure budget initial =
      (PMF.uniformOfFintype (Family Key Block)).bind (fun family =>
        (runFixed procedure family budget initial []).map fun out => (family, out)) := by
  rw [Spec.IdealCipherJoint.experiment, runPosterior_eq,
    ← IntegerSamplingProbability.map_uniform_equiv (IdealCipher.emptyEquiv (Key := Key) (Block := Block)), PMF.bind_map]
  rfl

theorem marginal (procedure : Procedure Key Block State) (budget : Nat)
    (state : State) (world : World Key Block) :
    (Spec.IdealCipherJoint.runPosterior procedure budget state world).map Prod.snd =
      Spec.IdealCipher.runPosterior procedure budget state world := by
  rw [runPosterior_eq, IdealCipher.runPosterior_eq, PMF.map_bind]
  congr 1
  funext family
  simp only [PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

end
end SDitH.Proofs.IdealCipherJoint
