import SDitH.Spec.SignatureReplay
import SDitH.Proofs.SignatureSecurity

namespace SDitH.Proofs.SignatureReplay

open Spec.SignatureSecurity Spec.SignatureReplay
open scoped Classical ENNReal
noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The replay prefix is exactly a factorization of the existing game. No
assumption about the adversary or honest services is needed. -/
theorem complete_cut
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (index fuel : Nat) (pk : PublicKey) (sk : SecretKey) (state : State)
    (world : World HashInput Digest Other) (trace : Trace Message HashInput Query) :
    (cut scheme adversary index fuel pk sk state world trace).bind (complete scheme adversary) =
      run scheme adversary fuel pk sk state world trace := by
  induction fuel generalizing index state world trace with
  | zero => simp [cut, complete, run]
  | succ fuel ih =>
    simp only [cut, run, PMF.bind_bind]
    congr 1
    funext action
    cases action with
    | abort => simp [complete]
    | finish message signature =>
      simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, complete]
      rfl
    | sign message next =>
      simp only [PMF.bind_bind]
      congr 1
      funext result
      exact ih index (next result.1) result.2 _
    | hash input next =>
      cases index with
      | zero => simp [complete, resume]
      | succ index =>
        simp only [PMF.bind_bind]
        congr 1
        funext result
        exact ih index (next result.1) _ _
    | query input next =>
      simp only [PMF.bind_bind]
      congr 1
      funext result
      exact ih index (next result.1) result.2 _

theorem complete_cut_experiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (index fuel : Nat) :
    (cutExperiment scheme adversary index fuel).bind (complete scheme adversary) =
      terminalLaw scheme adversary fuel := by
  simp only [cutExperiment, terminalLaw, PMF.bind_bind, complete_cut]

theorem complete_checked_experiment
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (index fuel : Nat) :
    (cutExperiment scheme adversary index fuel).bind
      (fun saved => (complete scheme adversary saved).bind finalize) =
        experiment scheme adversary fuel := by
  rw [← PMF.bind_bind, complete_cut_experiment]
  rfl

theorem fresh_branch_refines_resume
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State)
    (hfresh : snapshot.world.hashTable snapshot.input = none) :
    (freshBranch scheme adversary snapshot).map Branch.checked =
      (resume scheme adversary snapshot).bind finalize := by
  simp only [freshBranch, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp only [resume, Spec.RandomOracle.query, hfresh, PMF.bind_map, PMF.bind_bind,
    Function.comp_def, continueWith]
  congr 1
  funext answer
  exact PMF.map_id _

/-- The saved query's answer remains exactly uniform even though subsequent
adversarial computations depend on it. This is a marginal, not a uniform law
conditioned on the adversary later winning. -/
theorem fresh_branch_answer_uniform
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State) :
    (freshBranch scheme adversary snapshot).map Branch.answer = PMF.uniformOfFintype Digest := by
  simp only [freshBranch, PMF.map_bind, PMF.map_comp, Function.comp_def]
  calc
    _ = (PMF.uniformOfFintype Digest).bind PMF.pure := by
      congr 1
      funext answer
      exact PMF.map_const _ _
    _ = _ := PMF.bind_pure _

end
end SDitH.Proofs.SignatureReplay
