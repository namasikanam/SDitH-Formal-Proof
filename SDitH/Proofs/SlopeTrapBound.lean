import SDitH.Proofs.SlopeCoverFork
import SDitH.Proofs.CandidateGameBounds
import SDitH.Proofs.ForgeryReduction
import SDitH.Proofs.MeanHybrid
import SDitH.Proofs.ForkRestoreEq

/-! The mask trap's probability in the real experiment: a program run
raises the trap on its world's trace with probability at most the number
of execution pairs times the budget times `2^-s` (each hash answer's mask
component is uniform and kills a fixed nonzero vector with that
probability), so the candidate scheme's services obey a service bound,
the cut experiment's saved snapshot carries the trap with probability at
most the fuel times twice the bound, and the random event experiment of
the trap is bounded accordingly. -/

namespace SDitH.Proofs.SlopeTrapBound

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrace
open Spec.RandomOracleMention Spec.ProductOracle Spec.BAVCChainInputs Spec.SlopeConsistency
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.HashCipherProgram Spec.RandomOracleTrap
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open Spec.SharedSlopeGame (vectorOf)
open GameEventBound (ServiceBound terminalBad)
open GameEventBoundLen (ServiceBoundLen)
open CutEventBound (cutBad)
open CandidateGameBounds CandidateReduction ForgeryReduction SlopeEventSetting SlopeCoverFork MeanHybrid ChargeExpect
open ForkRestoreEq (map_true)
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))

/-- The mask trap on a shared world. -/
def trapBad (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) : Bool :=
  decide (∃ e e' : Fin tau, traceBad (tableMaskTrap (vectorOf (slopeSetting S V) world.family e e')) world.trace = true)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem slopeTrap_eq {State : Type*} (snapshot : Snap F lambda s higherCount w widths State) :
    slopeTrap S V snapshot = trapBad S V snapshot.world.other := rfl

/-- One run's trap cost at a budget. -/
def εTrap (tau s b : Nat) : ℝ≥0∞ := ((tau * tau : Nat) : ℝ≥0∞) * ((b : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ s)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem εTrap_mono (tau s : Nat) {b b' : Nat} (h : b ≤ b') : εTrap tau s b ≤ εTrap tau s b' :=
  mul_le_mul' le_rfl (mul_le_mul' (Nat.cast_le.mpr h) le_rfl)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A program run raises the trap with probability at most the trap cost. -/
theorem runProgram_trap_bound {A : Type*} (budget : Nat)
    (program : Program (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda)
      (Bits lambda) A)
    (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    ((runProgram budget program world).map (fun r => trapBad S V r.2)) true ≤
      indicator (trapBad S V world) + εTrap tau s budget := by
  by_cases hw : trapBad S V world = true
  · rw [hw, RandomOracleTrap.indicator_true]
    exact (PMF.coe_le_one _ _).trans le_self_add
  rw [Bool.not_eq_true] at hw
  rw [hw, RandomOracleTrap.indicator_false, zero_add]
  unfold runProgram
  rw [PMF.map_comp]
  have hnone : ∀ e e' : Fin tau,
      traceBad (tableMaskTrap (vectorOf (slopeSetting S V) world.family e e')) world.trace = false := by
    intro e e'
    by_contra h
    rw [Bool.not_eq_false] at h
    have : trapBad S V world = true := decide_eq_true ⟨e, e', h⟩
    rw [this] at hw
    cases hw
  have hunion := ChallengeMixtures.boolean_union_bound
    (Spec.HashCipherTrace.runFixed procedure world.family budget program world.hashTable world.hashHistory
      world.cipherHistory world.trace)
    ((fun r => trapBad S V r.2) ∘ fun out =>
      (out.state, ⟨world.family, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩))
    (fun pair : Fin tau × Fin tau => fun out =>
      traceBad (tableMaskTrap (vectorOf (slopeSetting S V) world.family pair.1 pair.2)) out.trace) (by
      intro out _ hany
      obtain ⟨e, e', he⟩ := of_decide_eq_true hany
      exact ⟨(e, e'), he⟩)
  refine hunion.trans ?_
  calc
    _ ≤ ∑ _pair : Fin tau × Fin tau, (budget : ℝ≥0∞) * (Fintype.card (ZMod 2) : ℝ≥0∞)⁻¹ ^ s := by
      apply Finset.sum_le_sum
      intro pair _
      have h := HashCipherTrace.run_trace_bound procedure world.family
        (tableMaskTrap (vectorOf (slopeSetting S V) world.family pair.1 pair.2)) _
        (fun table input => ProductOracle.uniform_mask_trap_le (vectorOf (slopeSetting S V) world.family pair.1 pair.2)
          table input)
        budget program world.hashTable world.hashHistory world.cipherHistory world.trace
      rw [hnone pair.1 pair.2, RandomOracleTrap.indicator_false, zero_add] at h
      exact h
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, ZMod.card]
      unfold εTrap
      push_cast
      ring

variable (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)
  (bound : Nat)

/-- The trap's service bound. -/
theorem trap_service_bound (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) :
    ServiceBoundLen (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) (trapBad S V)
      (fun world => world.trace.length) bound (fun _ => εTrap tau s bound) :=
  candidate_service_bound_len S V verifyBudget publicKey sampleWitness bound hcommit hverify hone _ _
    (fun budget hb program world => (runProgram_trap_bound S V budget program world).trans
      (add_le_add le_rfl (εTrap_mono tau s hb)))

/-- The prefix bound of the trap over the cut experiment. -/
theorem prefix_trap_bound (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (index fuel : Nat) :
    ((cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (cutBad (trapBad S V))) true ≤ fuel * (εTrap tau s bound + εTrap tau s bound) :=
  prefix_event_bound S V verifyBudget publicKey sampleWitness adversary _ bound _
    (trap_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone)
    (fun _ _ _ => le_rfl)
    (fun world h => by simp [trapBad, traceBad, h]) index fuel

/-- The trap's probability in the random event experiment. -/
theorem slopeTrap_le (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot _ => slopeTrap S V snapshot) fuel)
        true ≤ ((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) := by
  unfold randomEventExperiment
  rw [mean_bind_apply]
  refine mean_le_const _ _ _ fun index _ => ?_
  refine le_trans ?_ (prefix_trap_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit hverify hone index.val
    (fuel + 1))
  unfold eventExperiment
  rw [mean_bind_apply, map_true]
  refine mean_le_mean _ _ _ fun c _ => ?_
  cases c with
  | ended t =>
    simp only [PMF.pure_apply]
    simp
  | saved snapshot =>
    rw [map_true, mean_const, slopeTrap_eq]
    exact le_rfl

end
end SDitH.Proofs.SlopeTrapBound
