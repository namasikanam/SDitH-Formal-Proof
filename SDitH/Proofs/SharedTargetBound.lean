import SDitH.Proofs.GameEventBound
import SDitH.Proofs.ForkCutRun
import SDitH.Proofs.SharedSigning

/-! The fixed-target event charged over the shared game. Every shared
service runs at most one program within a budget, so the fixed-target
event on the shared world's log grows by at most the budget times the
inverse digest count per service call; with a common budget bound this is
a service bound, and the game-level lemma charges a fresh branch from a
snapshot with the remaining fuel times twice that constant. At a
well-formed snapshot the event is initially absent, so the branch bound
has no indicator term. -/

namespace SDitH.Proofs.SharedTargetBound

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrace
open Spec.SharedScheme Spec.SharedSigning Spec.HashCipherProgram Spec.RandomOracleTrap
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open ForkCutRun (targetBad)
open GameEventBound (ServiceBound terminalBad)
open SharedGameInvariant (WellFormed)
open scoped Classical ENNReal
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}

/-- The fixed-target event on a shared world. -/
def targetEvent {wit rnd : Nat} (P : List Bool → Option (Out lambda s wit rnd)) (target : Spec.BAVC.Digest lambda)
    (world : Spec.SharedScheme.World lambda s wit rnd) : Bool :=
  traceBad (targetBad P target) world.trace

/-- The inverse digest count. -/
def digestInv (lambda : Nat) : ℝ≥0∞ := (Fintype.card (Spec.BAVC.Digest lambda) : ℝ≥0∞)⁻¹

theorem runProgram_target_bound {A : Type*} {wit rnd : Nat} (P : List Bool → Option (Out lambda s wit rnd))
    (target : Spec.BAVC.Digest lambda) (budget : Nat)
    (program : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd) :
    ((runProgram budget program world).map (fun r => targetEvent P target r.2)) true ≤
      indicator (targetEvent P target world) + budget * digestInv lambda := by
  unfold runProgram
  rw [PMF.map_comp]
  exact ForkCutRun.run_target_bound procedure world.family P target budget program world.hashTable world.hashHistory
    world.cipherHistory world.trace

theorem budget_le {wit rnd : Nat} (P : List Bool → Option (Out lambda s wit rnd)) (target : Spec.BAVC.Digest lambda)
    (world : Spec.SharedScheme.World lambda s wit rnd) (budget bound : Nat) (h : budget ≤ bound) :
    indicator (targetEvent P target world) + budget * digestInv lambda ≤
      indicator (targetEvent P target world) + bound * digestInv lambda :=
  add_le_add_right (mul_le_mul_left (Nat.cast_le.mpr h) _) _

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- The shared services raise the fixed-target event by at most a common
budget bound times the inverse digest count. -/
theorem shared_target_service_bound [NeZero tau] [DecidableEq F]
    (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
    (P : List Bool → Option (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (target : Spec.BAVC.Digest lambda) (bound : Nat)
    (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) :
    ServiceBound (components S V verifyBudget publicKey sampleWitness) (targetEvent P target) (bound * digestInv lambda) where
  prepare := by
    intro pk sk msg other
    dsimp only [components]
    unfold Spec.SharedSigning.prepareSigning
    simp only [PMF.map_bind]
    refine ChallengeMixtures.bind_true_le _ _ _ fun salt _ => ?_
    refine ChallengeMixtures.bind_true_le _ _ _ fun root _ => ?_
    rw [PMF.map_comp]
    refine (ForkCutRun.map_true_mono _ _ (fun r => targetEvent P target r.2) ?_).trans ?_
    · intro result h
      simp only [Function.comp] at h
      split at h <;> exact h
    · exact (runProgram_target_bound P target _ _ other).trans (budget_le P target other _ bound hcommit)
  open_ := by
    intro st d other
    simp only [components, openSigning, PMF.pure_map, PMF.pure_apply]
    exact (RandomOracleTrap.ite_le_indicator _).trans le_self_add
  verify := by
    intro pk msg sig other
    change (((Spec.SharedSigning.prepareVerification S V verifyBudget pk msg sig other)).map
      (fun r => targetEvent P target r.2)) true ≤ _
    unfold Spec.SharedSigning.prepareVerification
    rcases hbody : sig.body with _ | body
    · simp only [PMF.pure_map, PMF.pure_apply]
      exact (RandomOracleTrap.ite_le_indicator _).trans le_self_add
    · unfold Spec.SharedScheme.prepareVerification
      rw [PMF.map_comp]
      exact (runProgram_target_bound P target _ _ other).trans (budget_le P target other _ bound hverify)
  oracle := by
    intro q other
    dsimp only [components]
    cases q <;> (
      simp only [Spec.SharedScheme.publicOracle]
      rw [PMF.map_comp]
      exact (runProgram_target_bound P target _ _ other).trans (budget_le P target other _ bound hone))

/-- At a well-formed snapshot, the fixed-target event at its own table is absent. -/
theorem targetEvent_wellFormed {wit rnd : Nat} (world : Spec.SharedScheme.World lambda s wit rnd) (hw : WellFormed world)
    (target : Spec.BAVC.Digest lambda) : targetEvent world.hashTable target world = false :=
  ForkCutRun.traceBad_target_preCut world.hashTable target world.trace (SharedGameInvariant.wellFormed_preCut world hw)
    hw.2.2.1

/-- A fresh branch from a well-formed snapshot raises the fixed-target
event at the snapshot's table with probability at most the remaining fuel
times twice the common budget bound times the inverse digest count. -/
theorem branch_target_bound [NeZero tau] [DecidableEq F]
    (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) {State : Type*}
    (adversary : Adversary (List Bool) (List Bool)
      (Signature (Spec.BAVC.Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
      (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)
    (snapshot : Snapshot (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State)
    (hw : WellFormed snapshot.world.other) (target : Spec.BAVC.Digest lambda) :
    ((freshBranch (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
      (fun branch => terminalBad (targetEvent snapshot.world.other.hashTable target) branch.checked.terminal)) true ≤
      snapshot.remaining * (bound * digestInv lambda + bound * digestInv lambda) := by
  have h := GameEventBound.branch_event_bound _ _ _
    (shared_target_service_bound S V verifyBudget publicKey sampleWitness snapshot.world.other.hashTable target bound
      hcommit hverify hone) adversary snapshot
  rwa [targetEvent_wellFormed _ hw, RandomOracleTrap.indicator_false, zero_add] at h

end
end SDitH.Proofs.SharedTargetBound
