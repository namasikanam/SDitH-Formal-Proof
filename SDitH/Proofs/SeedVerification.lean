import SDitH.Spec.SeedVerification
import SDitH.Proofs.IdealCipherProgram
import SDitH.Proofs.IdealCipherPipeline

namespace SDitH.Proofs.SeedVerification

open Spec.IdealCipher Spec.OracleProgram Spec.SeedVerification Spec.IdealCipherPairCollision
open scoped Classical ENNReal
noncomputable section

variable {Key Block Tag State : Type*}

theorem verify_bounded (project : Block → Tag) (claim : Claim Key Block) :
    Bounded 4 (verifyProgram project claim) := by
  intro _ _ _ _
  trivial

theorem execute_verify (family : Family Key Block) (project : Block → Tag) (claim : Claim Key Block)
    (history : List (Entry Key Block)) :
    Spec.IdealCipherProgram.execute family (verifyProgram project claim) history =
      (checked family project claim, verificationTrace family claim ++ history) := rfl

theorem run_verify (family : Family Key Block) (project : Block → Tag) (claim : Claim Key Block)
    (history : List (Entry Key Block)) :
    runFixed Spec.IdealCipherProgram.procedure family 4 (verifyProgram project claim) history =
      PMF.pure ⟨.done (checked family project claim), verificationTrace family claim ++ history⟩ := by
  rw [IdealCipherProgram.runFixed_execute family _ 4 (verify_bounded project claim), execute_verify]

theorem wins_done (value : Checked Key Block Tag) (history : List (Entry Key Block)) :
    wins (⟨.done value, history⟩ : Result Key Block (VerificationState Key Block Tag)) = true ↔
      value.claim.left ≠ value.claim.right ∧ value.left = value.right := by
  simp only [wins, decide_eq_true_eq]

variable [Fintype Key] [Fintype Block]

theorem experiment_law (adversary : Procedure Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Claim Key Block) :
    (Spec.SeedVerification.experiment adversary q initial project choose).map wins =
      (PMF.uniformOfFintype (Family Key Block)).bind (fun family =>
        (runFixed adversary family q initial []).map (fun start =>
          wins ⟨.done (checked family project (choose start.state)), []⟩)) := by
  simp only [Spec.SeedVerification.experiment, Spec.IdealCipherPipeline.experiment,
    Spec.IdealCipherPipeline.jointExperiment, PMF.map_bind,
    run_verify, PMF.pure_map]
  rfl

/-- Every supported joint execution completes all four calls and returns their
actual answers. The transcript equation derives coverage even for new inputs. -/
theorem joint_complete (adversary : Procedure Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Claim Key Block)
    (joint : Family Key Block × Result Key Block (VerificationState Key Block Tag))
    (hout : joint ∈ (Spec.IdealCipherPipeline.jointExperiment adversary q initial
      Spec.IdealCipherProgram.procedure 4 (fun state => verifyProgram project (choose state))).support) :
    ∃ start ∈ (runFixed adversary joint.1 q initial []).support,
      joint.2 = ⟨.done (checked joint.1 project (choose start.state)),
        verificationTrace joint.1 (choose start.state) ++ start.history⟩ := by
  obtain ⟨family, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨start, hs, hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  rw [run_verify, PMF.pure_map, PMF.mem_support_pure_iff] at hv
  subst joint
  exact ⟨start, hs, rfl⟩

theorem experiment_complete (adversary : Procedure Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Claim Key Block)
    (out : Result Key Block (VerificationState Key Block Tag))
    (hout : out ∈ (Spec.SeedVerification.experiment adversary q initial project choose).support) :
    ∃ family start, start ∈ (runFixed adversary family q initial []).support ∧
      out = ⟨.done (checked family project (choose start.state)), verificationTrace family (choose start.state) ++ start.history⟩ ∧
      out.history.length ≤ q + 4 := by
  obtain ⟨joint, hj, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  subst out
  obtain ⟨start, hs, hout⟩ := joint_complete adversary q initial project choose joint hj
  refine ⟨joint.1, start, hs, hout, ?_⟩
  have hl := IdealCipherTrace.runFixed_history_length adversary joint.1 q initial [] start hs
  rw [hout]
  simp only [List.length_append, verificationTrace, List.length_cons, List.length_nil] at hl ⊢
  omega

theorem winning_witnessed (adversary : Procedure Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Claim Key Block) (companion : Block → Block)
    (hrelated : ∀ state, (choose state).secondInput = companion (choose state).firstInput)
    (joint : Family Key Block × Result Key Block (VerificationState Key Block Tag))
    (hout : joint ∈ (Spec.IdealCipherPipeline.jointExperiment adversary q initial
      Spec.IdealCipherProgram.procedure 4 (fun state => verifyProgram project (choose state))).support)
    (hwin : wins joint.2 = true) : Witnessed project companion joint.1 joint.2.history := by
  obtain ⟨start, _, he⟩ := joint_complete adversary q initial project choose joint hout
  rw [he, wins_done] at hwin
  have hfirst := congrArg Prod.fst hwin.2
  have hsecond := congrArg Prod.snd hwin.2
  refine ⟨⟨(choose start.state).left, (choose start.state).firstInput,
      joint.1 (choose start.state).left (choose start.state).firstInput⟩, ?_,
    ⟨(choose start.state).right, (choose start.state).firstInput,
      joint.1 (choose start.state).right (choose start.state).firstInput⟩, ?_, hwin.1, rfl, hfirst, ?_⟩
  · simp only [he, verificationTrace, List.mem_append, List.mem_cons]
    tauto
  · simp only [he, verificationTrace, List.mem_append, List.mem_cons]
    tauto
  · change project (joint.1 (choose start.state).left (companion (choose start.state).firstInput)) =
      project (joint.1 (choose start.state).right (companion (choose start.state).firstInput))
    rw [← hrelated start.state]
    exact hsecond

/-- Both full commitment checks are included in q+4. No premise says that
constituent queries are fresh or present, and no coverage guard filters wins. -/
theorem binding_bound (adversary : Procedure Key Block State) (q : Nat) (initial : State)
    (project : Block → Tag) (choose : State → Claim Key Block) (companion : Block → Block)
    (hrelated : ∀ state, (choose state).secondInput = companion (choose state).firstInput)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((Spec.SeedVerification.experiment adversary q initial project choose).map wins) true ≤
      ((q + 4).choose 2 : ℝ≥0∞) * IdealCipherPairAdaptive.pairCost Block capacity (q + 4) := by
  exact IdealCipherPipeline.event_bound adversary q initial Spec.IdealCipherProgram.procedure 4
    (fun state => verifyProgram project (choose state)) project companion hinvolution hnofix capacity hcapacity wins
    (fun joint hj hw => winning_witnessed adversary q initial project choose companion hrelated joint hj hw)

end
end SDitH.Proofs.SeedVerification
