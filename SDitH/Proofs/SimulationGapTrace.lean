import SDitH.Proofs.TraceGrowth

/-! The simulation gap with the input-present term discharged. The counted
invariant gains a trace-length budget (the commitment budget times the
count), carried by queries, programmed inputs, the public oracle, both
signings and key generation. At worlds satisfying it the input-present
event is bounded uniformly by the mention steps over the prefix budget
from the trace budget, the row-stored term's bound and the support
budget over the digest count, so the simulation gap takes that explicit
value for the input-present term. -/

namespace SDitH.Proofs.SimulationGapTrace

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open CandidateReduction ForgeryReduction SimulatedSolver
open RunHybrid RunHybridGen CutHybrid CutHybridGen EventHybrid TableSupport SimulatedWith SignCompare
open DigestFirstVsSimulated SignComparePost SimulationGap SimulationGapInv SimulationGapGen SharedGameInvariant
open InputPresentBound InputPresentUniform TraceLength TraceGrowth PrefixMentionBound CommitSplitRun
open scoped Classical ENNReal BigOperators

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The counted invariant with a trace-length budget: the table supported
by the count, the shared world well formed, and the trace at most the
commitment budget times the count. -/
def InvT (tau kappa : Nat) (n : Nat)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : Prop :=
  Supported world.hashTable n ∧ WellFormed world.other ∧ world.other.trace.length ≤ commitBudget tau kappa * n

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem invT_mono (n m : Nat) (world) (hnm : n ≤ m)
    (h : InvT (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) tau kappa n world) : InvT tau kappa m world :=
  ⟨supported_mono h.1 hnm, h.2.1, h.2.2.trans (Nat.mul_le_mul_left _ hnm)⟩

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem invT_query (world) (input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (n : Nat)
    (r : Spec.BAVC.Digest lambda × (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) →
      Option (Spec.BAVC.Digest lambda)))
    (h : InvT (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) tau kappa n world)
    (hr : r ∈ (Spec.RandomOracle.query world.hashTable input).support) : InvT tau kappa (n + 1) { world with hashTable := r.2 } :=
  ⟨supported_query h.1 input r hr, h.2.1, h.2.2.trans (Nat.mul_le_mul_left _ (Nat.le_succ n))⟩

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem invT_update (world) (input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (n : Nat)
    (d : Spec.BAVC.Digest lambda)
    (h : InvT (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) tau kappa n world) :
    InvT tau kappa (n + 1) { world with hashTable := Function.update world.hashTable input (some d) } :=
  ⟨supported_update h.1 input d, h.2.1, h.2.2.trans (Nat.mul_le_mul_left _ (Nat.le_succ n))⟩

/-- The public oracle advances the invariant with its one trace entry. -/
theorem invT_pub (query : Query lambda) (world) (n : Nat) (r)
    (h : InvT (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) tau kappa n world)
    (hr : r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).publicOracle query world).support) :
    InvT tau kappa (n + 1) r.2 := by
  refine ⟨(inv_pub S V verifyBudget publicKey sampleWitness query world n r ⟨h.1, h.2.1⟩ hr).1,
    (inv_pub S V verifyBudget publicKey sampleWitness query world n r ⟨h.1, h.2.1⟩ hr).2, ?_⟩
  have h1 := publicOracle_trace_le S V verifyBudget publicKey sampleWitness query world r hr
  have h2 := one_le_commitBudget (tau := tau) (kappa := kappa)
  have h3 := h.2.2
  calc r.2.other.trace.length ≤ world.other.trace.length + 1 := h1
    _ ≤ commitBudget tau kappa * n + commitBudget tau kappa := by omega
    _ = commitBudget tau kappa * (n + 1) := by ring

/-- The honest signing advances the invariant with at most the commitment
budget of trace entries. -/
theorem invT_honest (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) (world) (n : Nat) (r)
    (h : InvT (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) tau kappa n world)
    (hr : r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message
      world).support) : InvT tau kappa (n + 1) r.2 := by
  refine ⟨(inv_honest S V verifyBudget publicKey sampleWitness sk message world n r ⟨h.1, h.2.1⟩ hr).1,
    (inv_honest S V verifyBudget publicKey sampleWitness sk message world n r ⟨h.1, h.2.1⟩ hr).2, ?_⟩
  have h1 := honest_sign_trace_le S V verifyBudget publicKey sampleWitness sk message world r hr
  have h3 := h.2.2
  calc r.2.other.trace.length ≤ world.other.trace.length + commitBudget tau kappa := h1
    _ ≤ commitBudget tau kappa * n + commitBudget tau kappa := by omega
    _ = commitBudget tau kappa * (n + 1) := by ring

/-- The simulated signing advances the invariant with at most the commitment
budget of trace entries. -/
theorem invT_simulated (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) (world) (n : Nat) (r)
    (h : InvT (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) tau kappa n world)
    (hr : r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message world).support) :
    InvT tau kappa (n + 1) r.2 := by
  refine ⟨(inv_simulated S V verifyBudget publicKey sampleWitness sk message world n r ⟨h.1, h.2.1⟩ hr).1,
    (inv_simulated S V verifyBudget publicKey sampleWitness sk message world n r ⟨h.1, h.2.1⟩ hr).2, ?_⟩
  have h1 := simulatedSign_trace_le S sk.1 message world r hr
  have h3 := h.2.2
  calc r.2.other.trace.length ≤ world.other.trace.length + commitBudget tau kappa := h1
    _ ≤ commitBudget tau kappa * n + commitBudget tau kappa := by omega
    _ = commitBudget tau kappa * (n + 1) := by ring

/-- The generated keys satisfy the invariant at zero. -/
theorem invT_keygen :
    ∀ generated ∈ (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).keygen.support,
      InvT (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) tau kappa 0
        generated.2.2 := by
  intro generated hg
  obtain ⟨g, hg', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hg
  refine ⟨supported_empty 0, keygen_wellFormed publicKey sampleWitness g hg', ?_⟩
  obtain ⟨witness, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hg'
  obtain ⟨family, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  simp

/-- The input-present term at the budget: the mention steps over the prefix
budget from the trace budget, the row-stored term's bound and the support
budget over the digest count. -/
def εP (εRow : ℝ≥0∞) (fuel : Nat) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (prefixBudget tau kappa),
      mentionStep lambda tau (commitBudget tau kappa * (2 * (fuel + 1) + 1) + i) +
    εRow + ((2 * (fuel + 1) + 1 : Nat) : ℝ≥0∞) * (Fintype.card (Spec.BAVC.Digest lambda) : ℝ≥0∞)⁻¹

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The simulation gap with the input-present term discharged uniformly:
the mention steps over the prefix budget from the trace budget, the
row-stored term's bound and the support budget over the digest count. -/
theorem hgap_of_uniform_trace (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S)
    (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) (εRow εR εS : ℝ≥0∞) (fuel : Nat)
    (hrow : ∀ (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvT tau kappa (2 * (fuel + 1) + 1) world → (rowTerm S htau world) true ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvT tau kappa (2 * (fuel + 1) + 1) world → (retryEvent S publicKey witness message world) true ≤ εR)
    (hswap : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvT tau kappa (2 * (fuel + 1) + 1) world →
      ∀ (h : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
        Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
          (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool)
      (c : Bool),
      ((simulatedSignWith S publicKey witness message world).bind h) c ≤
        ((simulatedSignWith S publicKey fake message world).bind h) c + εS)
    (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true +
        3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) εRow fuel + εR + εS) := by
  have hsign : ∀ sk, GoodKey S publicKey sk → ∀ (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvT tau kappa (2 * (fuel + 1) + 1) world →
      ∀ (h : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
        Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
          (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool)
      (c : Bool),
      (((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message world).bind h) c ≤
        (((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message world).bind h) c +
          (εP (lambda := lambda) (tau := tau) (kappa := kappa) εRow fuel + εR + εS) := by
    intro sk hsk message world hw h c
    obtain ⟨hpk, hsol⟩ := hsk
    rcases sk with ⟨pk', witness⟩
    dsimp only at hpk hsol
    subst hpk
    refine (honest_le_simulated_post S V verifyBudget _ sampleWitness hpc witness hsol message world h εS
      (fun fake c' => hswap witness fake message world hw h c') c).trans ?_
    refine add_le_add_right (add_le_add (add_le_add ?_ (hretry witness message world hw)) le_rfl) _
    refine (inputPresent_uniform S hl htau _ witness message world hw.2.1 hw.1 hw.2.2).trans ?_
    exact add_le_add_left (add_le_add_right (hrow world hw) _) _
  unfold randomEventExperiment simEventExperiment
  refine bind_le_bind_add_const' _ _ _ _ true (fun index _ => ?_)
  have hev := eventExp_le_gen (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (agree S V verifyBudget publicKey sampleWitness)
    (GoodKey S publicKey) (εP (lambda := lambda) (tau := tau) (kappa := kappa) εRow fuel + εR + εS) (fuel + 1) (InvT tau kappa) invT_mono invT_query hsign
    (invT_honest S V verifyBudget publicKey sampleWitness) (invT_simulated S V verifyBudget publicKey sampleWitness)
    (invT_pub S V verifyBudget publicKey sampleWitness) invT_update
    (keygen_good S V verifyBudget publicKey sampleWitness hsample) (invT_keygen S V verifyBudget publicKey sampleWitness)
    E index.val
  have heq₁ : eventExperiment S V verifyBudget publicKey sampleWitness adversary E index.val (fuel + 1) =
      eventExp (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary E index.val
        (fuel + 1) := by
    unfold eventExperiment eventExp
    first
      | rfl
      | (congr 1; funext c; cases c <;> rfl)
  rw [heq₁]
  refine hev.trans (le_of_eq ?_)
  congr 1 <;> first
    | rfl
    | (unfold eventExp; congr 1; congr 1; funext c; cases c <;> rfl)
    | (unfold eventExp)
    | (push_cast; ring1)


end
end SDitH.Proofs.SimulationGapTrace
