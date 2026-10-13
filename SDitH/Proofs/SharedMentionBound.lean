import SDitH.Proofs.GameEventBoundLen
import SDitH.Proofs.SharedTargetBound
import SDitH.Proofs.ProductOracle
import SDitH.Proofs.BAVCChainInputs

/-! The mention event charged over the shared game. A fresh digest equal
to a value mentioned by an earlier fresh query input has per-query mass at
most the log length times the mention count times the inverse digest
count, so a program run within a budget raises the event by at most the
budget times that mass at the final length. With the fresh-query log
length as the size, each shared service grows it by at most the common
budget bound and raises the event by an increasing function of the
length, so the size-dependent game-level bound applies to a fresh branch
under a level on the snapshot's length plus the remaining growth. -/

namespace SDitH.Proofs.SharedMentionBound

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrace
open Spec.RandomOracleMention Spec.ProductOracle Spec.BAVCChainInputs
open Spec.SharedScheme Spec.SharedSigning Spec.HashCipherProgram Spec.RandomOracleTrap
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open GameEventBound (terminalBad)
open GameEventBoundLen (ServiceBoundLen)
open SharedTargetBound (digestInv)
open scoped Classical ENNReal BigOperators
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}

/-- The mention event on a shared world. -/
def mentionEvent (tau : Nat) {wit rnd : Nat} (world : Spec.SharedScheme.World lambda s wit rnd) : Bool :=
  prefixBad (digestMention (mentions lambda tau)) world.trace

/-- The per-run bound at a log length: budget times the mass at the final length. -/
def epsilonM (lambda tau bound : Nat) (n : Nat) : ℝ≥0∞ :=
  bound * (((n + bound : Nat) : ℝ≥0∞) * (tau + 2 : Nat) * digestInv lambda)

theorem epsilonM_mono (lambda tau bound : Nat) : Monotone (epsilonM lambda tau bound) := by
  intro a b hab
  unfold epsilonM
  gcongr

theorem sum_le_budget (f : Nat → ℝ≥0∞) (budget : Nat) (C : ℝ≥0∞) (h : ∀ i < budget, f i ≤ C) :
    ∑ i ∈ Finset.range budget, f i ≤ budget * C := by
  calc ∑ i ∈ Finset.range budget, f i ≤ ∑ _i ∈ Finset.range budget, C :=
        Finset.sum_le_sum fun i hi => h i (Finset.mem_range.mp hi)
    _ = budget * C := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem runProgram_mention_bound {A : Type*} {wit rnd : Nat} (bound budget : Nat) (hb : budget ≤ bound)
    (program : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd) :
    ((runProgram budget program world).map (fun r => mentionEvent tau r.2)) true ≤
      indicator (mentionEvent tau world) + epsilonM lambda tau bound world.trace.length := by
  unfold runProgram
  rw [PMF.map_comp]
  have h := HashCipherTrace.run_prefix_bound procedure world.family (digestMention (mentions lambda tau))
    (fun n => (n : ℝ≥0∞) * (tau + 2 : Nat) * digestInv lambda)
    (fun log input => ProductOracle.digest_mention_query_bound (mentions lambda tau) (tau + 2)
      (fun s => BAVCChainInputs.mentions_card_le s) log input)
    budget program world.hashTable world.hashHistory world.cipherHistory world.trace
  refine h.trans (add_le_add_right ?_ _)
  refine (sum_le_budget _ budget (((world.trace.length + bound : Nat) : ℝ≥0∞) * (tau + 2 : Nat) * digestInv lambda)
    fun i hi => ?_).trans ?_
  · gcongr
    omega
  · unfold epsilonM
    gcongr

theorem runProgram_trace_length {A : Type*} {wit rnd : Nat} (budget : Nat)
    (program : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd)
    (result : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A × Spec.SharedScheme.World lambda s wit rnd)
    (hr : result ∈ (runProgram budget program world).support) : result.2.trace.length ≤ world.trace.length + budget := by
  obtain ⟨out, hout, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  subst hres
  exact GameEventBoundLen.run_trace_length procedure world.family budget program world.hashTable world.hashHistory
    world.cipherHistory world.trace out hout

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- The shared services grow the log by at most the common budget bound and
raise the mention event by at most the per-run bound at the current length. -/
theorem shared_mention_service_bound [NeZero tau] [DecidableEq F]
    (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) :
    ServiceBoundLen (components S V verifyBudget publicKey sampleWitness) (mentionEvent tau)
      (fun world => world.trace.length) bound (epsilonM lambda tau bound) where
  prepare := by
    intro pk sk msg other
    dsimp only [components]
    unfold Spec.SharedSigning.prepareSigning
    simp only [PMF.map_bind]
    refine ChallengeMixtures.bind_true_le _ _ _ fun salt _ => ?_
    refine ChallengeMixtures.bind_true_le _ _ _ fun root _ => ?_
    rw [PMF.map_comp]
    refine (ForkCutRun.map_true_mono _ _ (fun r => mentionEvent tau r.2) ?_).trans ?_
    · intro result h
      simp only [Function.comp] at h
      split at h <;> exact h
    · exact runProgram_mention_bound bound _ hcommit _ other
  prepare_size := by
    intro pk sk msg other r hr
    obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
    obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hroot
    have h := runProgram_trace_length _ _ other run hrun
    rw [← hres]
    split <;> (show run.2.trace.length ≤ _; omega)
  open_ := by
    intro st d other
    simp only [components, openSigning, PMF.pure_map, PMF.pure_apply]
    exact (RandomOracleTrap.ite_le_indicator _).trans le_self_add
  open_size := by
    intro st d other r hr
    simp only [components, openSigning, PMF.mem_support_pure_iff] at hr
    subst hr
    exact Nat.le_add_right _ _
  verify := by
    intro pk msg sig other
    change (((Spec.SharedSigning.prepareVerification S V verifyBudget pk msg sig other)).map
      (fun r => mentionEvent tau r.2)) true ≤ _
    unfold Spec.SharedSigning.prepareVerification
    rcases hbody : sig.body with _ | body
    · simp only [PMF.pure_map, PMF.pure_apply]
      exact (RandomOracleTrap.ite_le_indicator _).trans le_self_add
    · unfold Spec.SharedScheme.prepareVerification
      rw [PMF.map_comp]
      exact runProgram_mention_bound bound _ hverify _ other
  verify_size := by
    intro pk msg sig other r hr
    change r ∈ (Spec.SharedSigning.prepareVerification S V verifyBudget pk msg sig other).support at hr
    unfold Spec.SharedSigning.prepareVerification at hr
    rcases hbody : sig.body with _ | body
    · rw [hbody] at hr
      simp only [PMF.mem_support_pure_iff] at hr
      subst hr
      exact Nat.le_add_right _ _
    · rw [hbody] at hr
      unfold Spec.SharedScheme.prepareVerification at hr
      obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      have h := runProgram_trace_length _ _ other run hrun
      show run.2.trace.length ≤ _
      omega
  oracle := by
    intro q other
    dsimp only [components]
    cases q <;> (
      simp only [Spec.SharedScheme.publicOracle]
      rw [PMF.map_comp]
      exact runProgram_mention_bound bound _ hone _ other)
  oracle_size := by
    intro q other r hr
    dsimp only [components] at hr
    cases q <;> (
      simp only [Spec.SharedScheme.publicOracle] at hr
      obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      have h := runProgram_trace_length _ _ other run hrun
      show run.2.trace.length ≤ _
      omega)

/-- A fresh branch raises the mention event with probability at most its
indicator at the snapshot plus the remaining fuel times twice the per-run
bound at a level dominating the snapshot's length plus the remaining growth. -/
theorem branch_mention_bound [NeZero tau] [DecidableEq F]
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
    (L : Nat) (hL : snapshot.world.other.trace.length + snapshot.remaining * (bound + bound) ≤ L) :
    ((freshBranch (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
      (fun branch => terminalBad (mentionEvent tau) branch.checked.terminal)) true ≤
      indicator (mentionEvent tau snapshot.world.other) +
        snapshot.remaining * (epsilonM lambda tau bound L + epsilonM lambda tau bound L) :=
  GameEventBoundLen.branch_event_bound_len _ _ _ _ _
    (shared_mention_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone)
    (epsilonM_mono lambda tau bound) adversary snapshot L hL

end
end SDitH.Proofs.SharedMentionBound
