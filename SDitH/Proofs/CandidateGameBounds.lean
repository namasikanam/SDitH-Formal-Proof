import SDitH.Spec.CandidateScheme
import SDitH.Proofs.SharedCollisionBound
import SDitH.Proofs.ForkEventUnion

/-! Game invariants and event bounds for the candidate components. The
candidate services preserve any predicate preserved by program runs, so
the well-formedness and cut invariants hold at snapshots and branch
attempts; the fixed-target, mention and collision events satisfy the
same service bounds as for the literal components, since the candidate
verification is one program run and the candidate opening service is
pure; the prefix bounds from key generation and the snapshot's level
premise follow. -/

namespace SDitH.Proofs.CandidateGameBounds

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrace
open Spec.RandomOracleMention Spec.ProductOracle Spec.BAVCChainInputs Spec.SlopeConsistency
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.HashCipherProgram Spec.RandomOracleTrap
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open GameEventBound (ServiceBound terminalBad)
open GameEventBoundLen (ServiceBoundLen)
open CutEventBound (cutBad)
open SharedGameInvariant (WellFormed CutAt Preserves)
open SharedTargetBound (targetEvent digestInv)
open SharedMentionBound (mentionEvent epsilonM)
open SharedCollisionBound (collisionEvent epsilonC)
open scoped Classical ENNReal
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- A predicate preserved by every program run is preserved by the candidate services. -/
theorem candidate_preserves
    (Q : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)) → Prop)
    (hrun : ∀ {A : Type} (budget : Nat)
      (program : Program (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda) A)
      world result, result ∈ (runProgram budget program world).support → Q world → Q result.2) :
    Preserves (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) Q where
  prepare := by
    intro pk sk msg other r hr hQ
    obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
    obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hroot
    have hQ' := hrun _ _ other run hrun' hQ
    rw [← hres]
    cases run.1 <;> exact hQ'
  open_ := by
    intro st d other r hr hQ
    simp only [Spec.CandidateScheme.components, Spec.CandidateScheme.openSigning, PMF.mem_support_pure_iff] at hr
    subst hr
    exact hQ
  verify := by
    intro pk msg sig other r hr hQ
    change r ∈ (Spec.CandidateScheme.prepareVerification S V verifyBudget pk msg sig other).support at hr
    unfold Spec.CandidateScheme.prepareVerification at hr
    rcases hbody : sig.body with _ | body
    · rw [hbody] at hr
      simp only [PMF.mem_support_pure_iff] at hr
      subst hr
      exact hQ
    · rw [hbody] at hr
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact hrun _ _ other run hrun' hQ
  oracle := by
    intro q other r hr hQ
    cases q with
    | hash input =>
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact hrun _ _ other run hrun' hQ
    | mask input =>
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact hrun _ _ other run hrun' hQ
    | cipher request =>
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact hrun _ _ other run hrun' hQ

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Spec.CandidateScheme.Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- At a saved snapshot of the candidate game, the world is well formed, and
both branches' attempt worlds are well formed and cut at the snapshot's table. -/
theorem fork_cutAt (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      adversary snapshot).support)
    (left right) (hres : result = some (left, right)) :
    WellFormed snapshot.world.other ∧
      (∀ a, left.checked.terminal = .attempt a → WellFormed a.world.other ∧ CutAt snapshot.world.other.hashTable a.world.other) ∧
      ∀ b, right.checked.terminal = .attempt b → WellFormed b.world.other ∧ CutAt snapshot.world.other.hashTable b.world.other := by
  have hpW := candidate_preserves S V verifyBudget publicKey sampleWitness WellFormed
    (fun budget program world result hr hQ => SharedGameInvariant.runProgram_wellFormed budget program world result hr hQ)
  obtain ⟨generated, hgen, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
  obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  have hinit : WellFormed generated.2.2.other := by
    obtain ⟨g, hg, hgen'⟩ := (PMF.mem_support_map_iff _ _ _).mp hgen
    subst hgen'
    exact SharedGameInvariant.keygen_wellFormed publicKey sampleWitness g hg
  have hsnapW := (SharedGameInvariant.cut_preserves _ WellFormed hpW adversary index fuel _ _ state _ _ c hcut hinit).1
    snapshot hsnap
  have hpC := candidate_preserves S V verifyBudget publicKey sampleWitness (CutAt snapshot.world.other.hashTable)
    (fun budget program world result hr hQ => SharedGameInvariant.runProgram_cutAt _ budget program world result hr hQ)
  have hforkW := SharedGameInvariant.fork_preserves _ WellFormed hpW adversary snapshot hsnapW result hr left right hres
  have hforkC := SharedGameInvariant.fork_preserves _ (CutAt snapshot.world.other.hashTable) hpC adversary snapshot
    (SharedGameInvariant.wellFormed_cutAt _ hsnapW) result hr left right hres
  exact ⟨hsnapW, fun a ha => ⟨hforkW.1 a ha, hforkC.1 a ha⟩, fun b hb => ⟨hforkW.2 b hb, hforkC.2 b hb⟩⟩

theorem snapshot_wellFormed (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot) : WellFormed snapshot.world.other := by
  have hpW := candidate_preserves S V verifyBudget publicKey sampleWitness WellFormed
    (fun budget program world result hr hQ => SharedGameInvariant.runProgram_wellFormed budget program world result hr hQ)
  obtain ⟨generated, hgen, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
  obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  have hinit : WellFormed generated.2.2.other := by
    obtain ⟨g, hg, hgen'⟩ := (PMF.mem_support_map_iff _ _ _).mp hgen
    subst hgen'
    exact SharedGameInvariant.keygen_wellFormed publicKey sampleWitness g hg
  exact (SharedGameInvariant.cut_preserves _ WellFormed hpW adversary index fuel _ _ state _ _ c hcut hinit).1 snapshot hsnap

section Bounds

variable (bound : Nat)

/-- A size-dependent service bound for the candidate components, from a
per-run bound and the log growth. -/
theorem candidate_service_bound_len (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound)
    (bad : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)) → Bool)
    (epsilon : Nat → ℝ≥0∞)
    (hrunBound : ∀ {A : Type} (budget : Nat) (_hb : budget ≤ bound)
      (program : Program (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda) A)
      world, ((runProgram budget program world).map (fun r => bad r.2)) true ≤ indicator (bad world) + epsilon world.trace.length) :
    ServiceBoundLen (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) bad
      (fun world => world.trace.length) bound epsilon where
  prepare := by
    intro pk sk msg other
    dsimp only [Spec.CandidateScheme.components]
    unfold Spec.SharedSigning.prepareSigning
    simp only [PMF.map_bind]
    refine ChallengeMixtures.bind_true_le _ _ _ fun salt _ => ?_
    refine ChallengeMixtures.bind_true_le _ _ _ fun root _ => ?_
    rw [PMF.map_comp]
    refine (ForkCutRun.map_true_mono _ _ (fun r => bad r.2) ?_).trans ?_
    · intro result h
      simp only [Function.comp] at h
      split at h <;> exact h
    · exact hrunBound _ hcommit _ other
  prepare_size := by
    intro pk sk msg other r hr
    obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
    obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hroot
    have h := SharedMentionBound.runProgram_trace_length _ _ other run hrun
    rw [← hres]
    split <;> (show run.2.trace.length ≤ _; omega)
  open_ := by
    intro st d other
    simp only [Spec.CandidateScheme.components, Spec.CandidateScheme.openSigning, PMF.pure_map, PMF.pure_apply]
    exact (RandomOracleTrap.ite_le_indicator _).trans le_self_add
  open_size := by
    intro st d other r hr
    simp only [Spec.CandidateScheme.components, Spec.CandidateScheme.openSigning, PMF.mem_support_pure_iff] at hr
    subst hr
    exact Nat.le_add_right _ _
  verify := by
    intro pk msg sig other
    change (((Spec.CandidateScheme.prepareVerification S V verifyBudget pk msg sig other)).map (fun r => bad r.2)) true ≤ _
    unfold Spec.CandidateScheme.prepareVerification
    rcases hbody : sig.body with _ | body
    · simp only [PMF.pure_map, PMF.pure_apply]
      exact (RandomOracleTrap.ite_le_indicator _).trans le_self_add
    · rw [PMF.map_comp]
      exact hrunBound _ hverify _ other
  verify_size := by
    intro pk msg sig other r hr
    change r ∈ (Spec.CandidateScheme.prepareVerification S V verifyBudget pk msg sig other).support at hr
    unfold Spec.CandidateScheme.prepareVerification at hr
    rcases hbody : sig.body with _ | body
    · rw [hbody] at hr
      simp only [PMF.mem_support_pure_iff] at hr
      subst hr
      exact Nat.le_add_right _ _
    · rw [hbody] at hr
      obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      have h := SharedMentionBound.runProgram_trace_length _ _ other run hrun
      show run.2.trace.length ≤ _
      omega
  oracle := by
    intro q other
    dsimp only [Spec.CandidateScheme.components]
    cases q <;> (
      simp only [Spec.SharedScheme.publicOracle]
      rw [PMF.map_comp]
      exact hrunBound _ hone _ other)
  oracle_size := by
    intro q other r hr
    dsimp only [Spec.CandidateScheme.components] at hr
    cases q <;> (
      simp only [Spec.SharedScheme.publicOracle] at hr
      obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      have h := SharedMentionBound.runProgram_trace_length _ _ other run hrun
      show run.2.trace.length ≤ _
      omega)

/-- The mention event's service bound. -/
theorem mention_service_bound (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) :
    ServiceBoundLen (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) (mentionEvent tau)
      (fun world => world.trace.length) bound (epsilonM lambda tau bound) :=
  candidate_service_bound_len S V verifyBudget publicKey sampleWitness bound hcommit hverify hone _ _
    (fun budget hb program world => SharedMentionBound.runProgram_mention_bound bound budget hb program world)

/-- The collision event's service bound. -/
theorem collision_service_bound (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) :
    ServiceBoundLen (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) collisionEvent
      (fun world => world.trace.length) bound (epsilonC lambda bound) :=
  candidate_service_bound_len S V verifyBudget publicKey sampleWitness bound hcommit hverify hone _ _
    (fun budget hb program world => SharedCollisionBound.runProgram_collision_bound bound budget hb program world)

/-- The fixed-target event's service bound, as a size-dependent bound with a
constant function. -/
theorem target_service_bound (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (P : List Bool → Option (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (target : Spec.BAVC.Digest lambda) :
    ServiceBoundLen (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) (targetEvent P target)
      (fun world => world.trace.length) bound (fun _ => bound * digestInv lambda) :=
  candidate_service_bound_len S V verifyBudget publicKey sampleWitness bound hcommit hverify hone _ _
    (fun budget hb program world => (SharedTargetBound.runProgram_target_bound P target budget program world).trans
      (SharedTargetBound.budget_le P target world budget bound hb))

/-- The prefix bound of the cut experiment from key generation. -/
theorem prefix_event_bound
    (bad : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)) → Bool)
    (growth : Nat) (epsilon : Nat → ℝ≥0∞)
    (hb : ServiceBoundLen (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) bad
      (fun world => world.trace.length) growth epsilon)
    (hmono : Monotone epsilon)
    (hempty : ∀ world : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)),
      world.trace = [] → bad world = false)
    (index fuel : Nat) :
    ((cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (cutBad bad)) true ≤
      fuel * (epsilon (fuel * (growth + growth)) + epsilon (fuel * (growth + growth))) := by
  simp only [cutExperiment, PMF.map_bind]
  refine ChallengeMixtures.bind_true_le _ _ _ fun generated hgen => ?_
  refine ChallengeMixtures.bind_true_le _ _ _ fun state _ => ?_
  obtain ⟨g, hg, hgen'⟩ := (PMF.mem_support_map_iff _ _ _).mp hgen
  subst hgen'
  have htrace := SharedCollisionBound.keygen_trace publicKey sampleWitness g hg
  have h := CutEventBound.cut_event_bound_len _ bad _ growth epsilon hb hmono adversary (fuel * (growth + growth))
    index fuel g.1 (g.1, g.2.1) state (⟨fun _ => none, g.2.2⟩ : World _ _ _) ⟨[], [], []⟩
    (by show g.2.2.trace.length + _ ≤ _; rw [htrace]; simp)
  rwa [show bad (⟨fun _ => none, g.2.2⟩ : World _ _ _).other = false from hempty g.2.2 htrace,
    RandomOracleTrap.indicator_false, zero_add] at h

/-- From key generation, a saved snapshot satisfies the branch bounds' level premise. -/
theorem prefix_size (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot) :
    snapshot.world.other.trace.length + snapshot.remaining * (bound + bound) ≤ fuel * (bound + bound) := by
  obtain ⟨generated, hgen, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
  obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨g, hg, hgen'⟩ := (PMF.mem_support_map_iff _ _ _).mp hgen
  subst hgen'
  have htrace := SharedCollisionBound.keygen_trace publicKey sampleWitness g hg
  exact CutEventBound.cut_size _ (mentionEvent tau) (fun world => world.trace.length) bound (epsilonM lambda tau bound)
    (mention_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone)
    adversary (fuel * (bound + bound)) index fuel g.1 (g.1, g.2.1) state (⟨fun _ => none, g.2.2⟩ : World _ _ _)
    ⟨[], [], []⟩ c hcut (by show g.2.2.trace.length + _ ≤ _; rw [htrace]; simp) snapshot hsnap

theorem prefix_mention_bound (index fuel : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) :
    ((cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (cutBad (mentionEvent tau))) true ≤
      fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) :=
  prefix_event_bound S V verifyBudget publicKey sampleWitness adversary _ bound _
    (mention_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone)
    (SharedMentionBound.epsilonM_mono lambda tau bound) SharedCollisionBound.mention_empty index fuel

theorem prefix_collision_bound (index fuel : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) :
    ((cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (cutBad collisionEvent)) true ≤
      fuel * (epsilonC lambda bound (fuel * (bound + bound)) + epsilonC lambda bound (fuel * (bound + bound))) :=
  prefix_event_bound S V verifyBudget publicKey sampleWitness adversary _ bound _
    (collision_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone)
    (SharedCollisionBound.epsilonC_mono lambda bound) SharedCollisionBound.collision_empty index fuel

end Bounds

end
end SDitH.Proofs.CandidateGameBounds
