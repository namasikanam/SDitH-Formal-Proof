import SDitH.Proofs.SharedMentionBound
import SDitH.Proofs.CutEventBound
import SDitH.Proofs.SlopeConsistency

/-! The digest-collision event charged over the shared game, and the
prefix bounds from key generation. A fresh digest equal to an earlier
fresh digest has per-query mass at most the log length times the inverse
digest count, the same shape as the mention event with count one, so the
shared services satisfy the size-dependent service bound and a fresh
branch is charged as before. Without the event a well-formed world's
table is digest-collision free. From key generation, whose shared world
has an empty log, the cut experiment raises any such event at the saved
snapshot or ended attempt with probability at most the fuel times twice
the per-run bound at the level fuel times twice the budget bound, and the
saved snapshot satisfies the branch bounds' level premise. -/

namespace SDitH.Proofs.SharedCollisionBound

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrace
open Spec.RandomOracleMention Spec.SlopeConsistency
open Spec.SharedScheme Spec.SharedSigning Spec.HashCipherProgram Spec.RandomOracleTrap
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open GameEventBound (terminalBad)
open GameEventBoundLen (ServiceBoundLen)
open CutEventBound (cutBad)
open SharedTargetBound (digestInv)
open SharedGameInvariant (WellFormed)
open scoped Classical ENNReal BigOperators
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}

/-- The digest-collision event on a shared world. -/
def collisionEvent {wit rnd : Nat} (world : Spec.SharedScheme.World lambda s wit rnd) : Bool :=
  prefixBad digestCollision world.trace

/-- The per-run bound at a log length. -/
def epsilonC (lambda bound : Nat) (n : Nat) : ℝ≥0∞ :=
  bound * (((n + bound : Nat) : ℝ≥0∞) * digestInv lambda)

theorem epsilonC_mono (lambda bound : Nat) : Monotone (epsilonC lambda bound) := by
  intro a b hab
  unfold epsilonC
  gcongr

theorem runProgram_collision_bound {A : Type*} {wit rnd : Nat} (bound budget : Nat) (hb : budget ≤ bound)
    (program : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd) :
    ((runProgram budget program world).map (fun r => collisionEvent r.2)) true ≤
      indicator (collisionEvent world) + epsilonC lambda bound world.trace.length := by
  unfold runProgram
  rw [PMF.map_comp]
  have h := HashCipherTrace.run_prefix_bound procedure world.family digestCollision
    (fun n => (n : ℝ≥0∞) * digestInv lambda)
    (fun log input => SlopeConsistency.digest_collision_query_bound log input)
    budget program world.hashTable world.hashHistory world.cipherHistory world.trace
  refine h.trans (add_le_add_right ?_ _)
  refine (SharedMentionBound.sum_le_budget _ budget (((world.trace.length + bound : Nat) : ℝ≥0∞) * digestInv lambda)
    fun i hi => ?_).trans ?_
  · gcongr
    omega
  · unfold epsilonC
    gcongr

/-- Without the event, a well-formed world's table is digest-collision free. -/
theorem collisionFree_of_not_event {wit rnd : Nat} (world : Spec.SharedScheme.World lambda s wit rnd)
    (hw : WellFormed world) (hno : collisionEvent world = false) : DigestCollisionFree world.hashTable :=
  SlopeConsistency.collision_free_of_not_prefix world.trace world.hashTable hw.1 (by simp [collisionEvent] at hno; simp [hno])

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

theorem shared_collision_service_bound [NeZero tau] [DecidableEq F]
    (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) :
    ServiceBoundLen (components S V verifyBudget publicKey sampleWitness) collisionEvent
      (fun world => world.trace.length) bound (epsilonC lambda bound) where
  prepare := by
    intro pk sk msg other
    dsimp only [components]
    unfold Spec.SharedSigning.prepareSigning
    simp only [PMF.map_bind]
    refine ChallengeMixtures.bind_true_le _ _ _ fun salt _ => ?_
    refine ChallengeMixtures.bind_true_le _ _ _ fun root _ => ?_
    rw [PMF.map_comp]
    refine (ForkCutRun.map_true_mono _ _ (fun r => collisionEvent r.2) ?_).trans ?_
    · intro result h
      simp only [Function.comp] at h
      split at h <;> exact h
    · exact runProgram_collision_bound bound _ hcommit _ other
  prepare_size := (SharedMentionBound.shared_mention_service_bound S V verifyBudget publicKey sampleWitness bound
    hcommit hverify hone).prepare_size
  open_ := by
    intro st d other
    simp only [components, openSigning, PMF.pure_map, PMF.pure_apply]
    exact (RandomOracleTrap.ite_le_indicator _).trans le_self_add
  open_size := (SharedMentionBound.shared_mention_service_bound S V verifyBudget publicKey sampleWitness bound
    hcommit hverify hone).open_size
  verify := by
    intro pk msg sig other
    change (((Spec.SharedSigning.prepareVerification S V verifyBudget pk msg sig other)).map
      (fun r => collisionEvent r.2)) true ≤ _
    unfold Spec.SharedSigning.prepareVerification
    rcases hbody : sig.body with _ | body
    · simp only [PMF.pure_map, PMF.pure_apply]
      exact (RandomOracleTrap.ite_le_indicator _).trans le_self_add
    · unfold Spec.SharedScheme.prepareVerification
      rw [PMF.map_comp]
      exact runProgram_collision_bound bound _ hverify _ other
  verify_size := (SharedMentionBound.shared_mention_service_bound S V verifyBudget publicKey sampleWitness bound
    hcommit hverify hone).verify_size
  oracle := by
    intro q other
    dsimp only [components]
    cases q <;> (
      simp only [Spec.SharedScheme.publicOracle]
      rw [PMF.map_comp]
      exact runProgram_collision_bound bound _ hone _ other)
  oracle_size := (SharedMentionBound.shared_mention_service_bound S V verifyBudget publicKey sampleWitness bound
    hcommit hverify hone).oracle_size

section Prefix

variable [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- Key generation's shared world has an empty log. -/
theorem keygen_trace (generated : List Bool × (Fin (selectorCount widths * w) → ZMod 2) ×
      Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hg : generated ∈ (keygen publicKey sampleWitness).support) : generated.2.2.trace = [] := by
  obtain ⟨witness, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hg
  obtain ⟨family, _, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst hres
  rfl

/-- From key generation, the cut experiment raises an event with a
size-dependent service bound at the saved snapshot or ended attempt with
probability at most the fuel times twice the per-run bound at the level
fuel times twice the budget bound. -/
theorem prefix_event_bound (bad : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)) → Bool)
    (growth : Nat) (epsilon : Nat → ℝ≥0∞)
    (hb : ServiceBoundLen (components S V verifyBudget publicKey sampleWitness) bad (fun world => world.trace.length)
      growth epsilon)
    (hmono : Monotone epsilon)
    (hempty : ∀ world : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)),
      world.trace = [] → bad world = false)
    (index fuel : Nat) :
    ((cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map (cutBad bad)) true ≤
      fuel * (epsilon (fuel * (growth + growth)) + epsilon (fuel * (growth + growth))) := by
  simp only [cutExperiment, PMF.map_bind]
  refine ChallengeMixtures.bind_true_le _ _ _ fun generated hgen => ?_
  refine ChallengeMixtures.bind_true_le _ _ _ fun state _ => ?_
  obtain ⟨g, hg, hgen'⟩ := (PMF.mem_support_map_iff _ _ _).mp hgen
  subst hgen'
  have htrace := keygen_trace publicKey sampleWitness g hg
  have h := CutEventBound.cut_event_bound_len _ bad _ growth epsilon hb hmono adversary (fuel * (growth + growth))
    index fuel g.1 (g.1, g.2.1) state (⟨fun _ => none, g.2.2⟩ : World _ _ _) ⟨[], [], []⟩
    (by show g.2.2.trace.length + _ ≤ _; rw [htrace]; simp)
  rwa [show bad (⟨fun _ => none, g.2.2⟩ : World _ _ _).other = false from hempty g.2.2 htrace,
    RandomOracleTrap.indicator_false, zero_add] at h

/-- From key generation, a saved snapshot satisfies the branch bounds' level premise. -/
theorem prefix_size (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound)
    (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot) :
    snapshot.world.other.trace.length + snapshot.remaining * (bound + bound) ≤ fuel * (bound + bound) := by
  obtain ⟨generated, hgen, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
  obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨g, hg, hgen'⟩ := (PMF.mem_support_map_iff _ _ _).mp hgen
  subst hgen'
  have htrace := keygen_trace publicKey sampleWitness g hg
  exact CutEventBound.cut_size _ _ _ bound _
    (SharedMentionBound.shared_mention_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone)
    adversary (fuel * (bound + bound)) index fuel g.1 (g.1, g.2.1) state (⟨fun _ => none, g.2.2⟩ : World _ _ _)
    ⟨[], [], []⟩ c hcut (by show g.2.2.trace.length + _ ≤ _; rw [htrace]; simp) snapshot hsnap

omit [NeZero tau] [DecidableEq F] in
theorem mention_empty (world : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (h : world.trace = []) : SharedMentionBound.mentionEvent tau world = false := by
  simp [SharedMentionBound.mentionEvent, h, prefixBad]

omit [NeZero tau] [DecidableEq F] in
theorem collision_empty (world : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (h : world.trace = []) : collisionEvent world = false := by
  simp [collisionEvent, h, prefixBad]

/-- The prefix's mention event from key generation. -/
theorem prefix_mention_bound (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound)
    (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (index fuel : Nat) :
    ((cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (cutBad (SharedMentionBound.mentionEvent tau))) true ≤
      fuel * (SharedMentionBound.epsilonM lambda tau bound (fuel * (bound + bound)) +
        SharedMentionBound.epsilonM lambda tau bound (fuel * (bound + bound))) :=
  prefix_event_bound S V verifyBudget publicKey sampleWitness adversary _ bound _
    (SharedMentionBound.shared_mention_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone)
    (SharedMentionBound.epsilonM_mono lambda tau bound) mention_empty index fuel

/-- The prefix's collision event from key generation. -/
theorem prefix_collision_bound (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound)
    (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (index fuel : Nat) :
    ((cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (cutBad collisionEvent)) true ≤
      fuel * (epsilonC lambda bound (fuel * (bound + bound)) + epsilonC lambda bound (fuel * (bound + bound))) :=
  prefix_event_bound S V verifyBudget publicKey sampleWitness adversary _ bound _
    (shared_collision_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone)
    (epsilonC_mono lambda bound) collision_empty index fuel

end Prefix

end
end SDitH.Proofs.SharedCollisionBound
