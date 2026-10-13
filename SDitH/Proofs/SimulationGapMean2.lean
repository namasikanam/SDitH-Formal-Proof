import SDitH.Proofs.SimulationGapCipher
import SDitH.Proofs.MeanEventCont
import SDitH.Proofs.CandidateShift
import SDitH.Proofs.CandidateKeepsFamily
import SDitH.Proofs.InvCExtra
import SDitH.Proofs.ForgeryEvents

/-! The simulation gap and the composed forgery bound in mean form over the
restored fork. The per-call witness swap is taken in mean form, with the
world's family resampled before the call, for the simulated scheme's run
and cut continuations only; the events are required to be insensitive to
the second branch's history suffix and to the attempts' embedded
families. The row-stored term and the retry term enter as in the extended
module. -/

namespace SDitH.Proofs.SimulationGapMean2

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier Spec.CandidateSimulator Spec.BLC
open Spec.SharedSigner (commitBudget)
open CommitSplitRun (prefixBudget)
open Spec.BAVC (Digest)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open CandidateReduction ForgeryReduction ExtractionSplit SimulatedSolver CandidateSimulator SimulationGap
open SimulatedWith SignCompare DigestFirstVsSimulated SignComparePost SimulationGapTrace InputPresentBound TraceLength
open PrefixMentionBound (mentionStep)
open RunHybrid EventHybrid CipherResample GameResample ChargeRun ChargeExpect ChargeCut ChargeCutExpect SharedResample
open CandidateResample SimulationGapMean CipherInvariant PayloadConsistent RowBoundExplicit RowStoredPosterior
open HeadCommitSplit SimulationGapCipher
open GamePrune RunWorld ForkRestore ForkRestoreLemmas ForkRestoreEnd EventRestore MeanHybridCont MeanHybridContW
open MeanEventCont CandidatePrune CandidatePrepLaw CandidateShift CandidateKeepsFamily InvCExtra HistoryShiftGame
open ForgeryEvents MeanHybrid
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The per-call constant: the input-present term at a counted budget, the
row-stored term's bound, the retry bound and the swap bound. -/
def εCall (εRow εR εS : ℝ≥0∞) (B : Nat) : ℝ≥0∞ :=
  (∑ i ∈ Finset.range (prefixBudget tau kappa), mentionStep lambda tau (commitBudget tau kappa * B + i) + εRow +
    (B : ℝ≥0∞) * (Fintype.card (Spec.BAVC.Digest lambda) : ℝ≥0∞)⁻¹) + εR + εS

/-- An event insensitive to the second branch's history suffix and to the
attempts' embedded families. -/
def EventOK (E : Snap F lambda s higherCount w widths State →
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool) : Prop :=
  (∀ snapshot left right H, E snapshot (some (left, shiftBranch H right)) = E snapshot (some (left, right))) ∧
  (∀ snapshot left right g, E snapshot (some (setFamilyBranch g left, right)) = E snapshot (some (left, right))) ∧
  (∀ snapshot left right g, E snapshot (some (left, setFamilyBranch g right)) = E snapshot (some (left, right)))

/-- The simulated scheme's keygen is resampled. -/
theorem simulated_keygen_resampled :
    (simulatedScheme S V verifyBudget publicKey sampleWitness).keygen =
      (simulatedScheme S V verifyBudget publicKey sampleWitness).keygen.bind fun g =>
        (resampleW resample g.2.2).map fun w => (g.1, g.2.1, w) := by
  rw [← (agree S V verifyBudget publicKey sampleWitness).keygen]
  exact keygen_resampled S V verifyBudget publicKey sampleWitness

/-- The per-call bound in mean form for an arbitrary continuation of the
signing output, from the input-present, retry and swap bounds. -/
theorem call_mean (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S) (εRow εR εS : ℝ≥0∞) (B : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) B world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) B world → (retryEvent S publicKey witness message world) true ≤ εR)
    (witness : Fin (selectorCount widths * w) → ZMod 2) (hsol : IsSolution S witness) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (hw : InvC (tau := tau) (kappa := kappa) B world)
    (f : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool) (c : Bool)
    (hswap : ∀ fake : Fin (selectorCount widths * w) → ZMod 2,
      mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind f) c) ≤
        mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey fake message w').bind f) c) + εS) :
    mean (resampleW resample world) (fun w' =>
        (((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness) message
          w').bind f) c) ≤
      mean (resampleW resample world) (fun w' =>
        (((simulatedScheme S V verifyBudget publicKey sampleWitness).sign (publicKey, witness) message w').bind f) c) +
        εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR εS B := by
  have hsim : ∀ w' : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))),
      (simulatedScheme S V verifyBudget publicKey sampleWitness).sign (publicKey, witness) message w' =
        (PMF.uniformOfFintype (Fin (selectorCount widths * w) → ZMod 2)).bind fun fake =>
          simulatedSignWith S publicKey fake message w' := fun w' => simulatedSign_eq_with S publicKey message w'
  -- the swap, averaged over the fake witness
  have hswapU : mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind f) c) ≤
      mean (resampleW resample world) (fun w' =>
        (((simulatedScheme S V verifyBudget publicKey sampleWitness).sign (publicKey, witness) message w').bind f) c) + εS := by
    have hR : mean (resampleW resample world) (fun w' =>
        (((simulatedScheme S V verifyBudget publicKey sampleWitness).sign (publicKey, witness) message w').bind f) c) =
        mean (PMF.uniformOfFintype (Fin (selectorCount widths * w) → ZMod 2)) (fun fake =>
          mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey fake message w').bind f) c)) := by
      simp only [hsim, PMF.bind_bind, mean_bind_apply]
      exact mean_comm _ _ _
    rw [hR, ← mean_add_const]
    calc _ = mean (PMF.uniformOfFintype (Fin (selectorCount widths * w) → ZMod 2)) (fun _ =>
          mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind f) c)) :=
          (mean_const _ _).symm
      _ ≤ _ := mean_le_mean _ _ _ fun fake _ => hswap fake
  -- the input-present term
  have hinput : mean (resampleW resample world) (fun w' => (inputPresent S publicKey witness message w') true) ≤
      ∑ i ∈ Finset.range (prefixBudget tau kappa), mentionStep lambda tau (commitBudget tau kappa * B + i) + εRow +
        (B : ℝ≥0∞) * (Fintype.card (Spec.BAVC.Digest lambda) : ℝ≥0∞)⁻¹ := by
    calc _ ≤ mean (resampleW resample world) (fun w' =>
          ∑ i ∈ Finset.range (prefixBudget tau kappa), mentionStep lambda tau (commitBudget tau kappa * B + i) +
            (rowTerm S htau w') true + (B : ℝ≥0∞) * (Fintype.card (Spec.BAVC.Digest lambda) : ℝ≥0∞)⁻¹) :=
          mean_le_mean _ _ _ fun w' hw' => by
            have hw'' := invC_resample B world hw w' hw'
            exact inputPresent_uniform S hl htau publicKey witness message w' hw''.1.2.1 hw''.1.1 hw''.1.2.2
      _ = ∑ i ∈ Finset.range (prefixBudget tau kappa), mentionStep lambda tau (commitBudget tau kappa * B + i) +
            mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) +
            (B : ℝ≥0∞) * (Fintype.card (Spec.BAVC.Digest lambda) : ℝ≥0∞)⁻¹ := by
          simp only [mean_add, mean_const]
      _ ≤ _ := add_le_add (add_le_add le_rfl (hrow world hw)) le_rfl
  -- the retry term
  have hret : mean (resampleW resample world) (fun w' => (retryEvent S publicKey witness message w') true) ≤ εR :=
    mean_le_const _ _ _ fun w' hw' => hretry witness message w' (invC_resample B world hw w' hw')
  calc _ ≤ mean (resampleW resample world) (fun w' =>
          ((simulatedSignWith S publicKey witness message w').bind f) c +
          ((inputPresent S publicKey witness message w') true + (retryEvent S publicKey witness message w') true)) :=
        mean_le_mean _ _ _ fun w' _ =>
          honest_le_simulatedWith_post S V verifyBudget publicKey sampleWitness hpc witness hsol message w' f c
    _ = mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind f) c) +
          (mean (resampleW resample world) (fun w' => (inputPresent S publicKey witness message w') true) +
            mean (resampleW resample world) (fun w' => (retryEvent S publicKey witness message w') true)) := by
        simp only [mean_add]
    _ ≤ (mean (resampleW resample world) (fun w' =>
          (((simulatedScheme S V verifyBudget publicKey sampleWitness).sign (publicKey, witness) message w').bind f) c) + εS) +
          ((∑ i ∈ Finset.range (prefixBudget tau kappa), mentionStep lambda tau (commitBudget tau kappa * B + i) + εRow +
            (B : ℝ≥0∞) * (Fintype.card (Spec.BAVC.Digest lambda) : ℝ≥0∞)⁻¹) + εR) :=
        add_le_add hswapU (add_le_add hinput hret)
    _ = _ := by
        unfold εCall
        ring

/-- The per-call bound for the run's continuations in mean form. -/
theorem signRunW_mean (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S) (εRow εR εS : ℝ≥0∞) (B : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) B world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) B world → (retryEvent S publicKey witness message world) true ≤ εR)
    (hswapRunW : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) B world →
      ∀ (fuel' : Nat) (pk : List Bool)
        (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (h : Terminal (List Bool) (Signature (Spec.BAVC.Digest lambda)
            (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) ×
          Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool)
        (c : Bool),
      mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind fun r =>
          (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c) ≤
        mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey fake message w').bind fun r =>
          (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c) + εS) :
    SignRunWMean (C := Bool) resample (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (GoodKey S publicKey)
      (εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR εS B) B (InvC (tau := tau) (kappa := kappa)) := by
  intro sk hsk message world hw fuel' pk next trace h c
  obtain ⟨hpk, hsol⟩ := hsk
  rcases sk with ⟨pk', witness⟩
  dsimp only at hpk hsol
  rw [hpk]
  exact call_mean S V verifyBudget publicKey sampleWitness hl htau hpc εRow εR εS B hrow hretry witness hsol message world hw
    (fun r => (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1)
      r.2 trace).bind h) c
    (fun fake => hswapRunW witness fake message world hw fuel' pk next trace h c)

/-- The per-call bound for the cut run's continuations in mean form. -/
theorem signCut_mean (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S) (εRow εR εS : ℝ≥0∞) (B : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) B world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) B world → (retryEvent S publicKey witness message world) true ≤ εR)
    (hswapCut : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) B world →
      ∀ (index fuel' : Nat) (pk : List Bool)
        (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (h : Cut (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
          (Signature (Spec.BAVC.Digest lambda)
            (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State → PMF Bool)
        (c : Bool),
      mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) ≤
        mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey fake message w').bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) + εS) :
    SignCutMean (C := Bool) resample (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (GoodKey S publicKey)
      (εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR εS B) B (InvC (tau := tau) (kappa := kappa)) := by
  intro sk hsk message world hw index fuel' pk next trace h c
  obtain ⟨hpk, hsol⟩ := hsk
  rcases sk with ⟨pk', witness⟩
  dsimp only at hpk hsol
  rw [hpk]
  exact call_mean S V verifyBudget publicKey sampleWitness hl htau hpc εRow εR εS B hrow hretry witness hsol message world hw
    (fun r => (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
      (next r.1) r.2 trace).bind h) c
    (fun fake => hswapCut witness fake message world hw index fuel' pk next trace h c)

/-- The simulation gap for one event in mean form over the restored fork,
at the budget three times the fuel plus two. -/
theorem hgap_mean (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S)
    (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) (hvc : verifyBudget ≤ commitBudget tau kappa)
    (εRow εR εS : ℝ≥0∞) (fuel : Nat)
    (hrow : ∀ world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (hswapRunW : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
      ∀ (fuel' : Nat) (pk : List Bool)
        (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (h : Terminal (List Bool) (Signature (Spec.BAVC.Digest lambda)
            (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) ×
          Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool)
        (c : Bool),
      mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind fun r =>
          (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c) ≤
        mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey fake message w').bind fun r =>
          (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c) + εS)
    (hswapCut : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
      ∀ (index fuel' : Nat) (pk : List Bool)
        (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (h : Cut (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
          (Signature (Spec.BAVC.Digest lambda)
            (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State → PMF Bool)
        (c : Bool),
      mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) ≤
        mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey fake message w').bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) + εS)
    (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hE : EventOK E) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true +
        3 * ((fuel : ℝ≥0∞) + 1) * εCall (lambda := lambda) (tau := tau) (kappa := kappa) εRow εR εS (3 * (fuel + 1) + 2) := by
  have hsignRunW := signRunW_mean S V verifyBudget publicKey sampleWitness adversary hl htau hpc εRow εR εS (3 * (fuel + 1) + 2)
    hrow hretry hswapRunW
  have hsignCut := signCut_mean S V verifyBudget publicKey sampleWitness adversary hl htau hpc εRow εR εS (3 * (fuel + 1) + 2)
    hrow hretry hswapCut
  unfold randomEventExperiment simEventExperiment
  refine bind_le_bind_add_const' _ _ _ _ true (fun index _ => ?_)
  have heq₁ : eventExperiment S V verifyBudget publicKey sampleWitness adversary E index.val (fuel + 1) =
      eventExp (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary E index.val
        (fuel + 1) := by
    unfold eventExperiment eventExp
    first
      | rfl
      | (congr 1; funext c; cases c <;> rfl)
  rw [heq₁, eventExp_eq_E _ adversary E (keygen_resampled S V verifyBudget publicKey sampleWitness)
    (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
    (honest_keepsFamily S V verifyBudget publicKey sampleWitness) (publicOracle_keepsFamily S V verifyBudget publicKey sampleWitness)
    (prepareVerification_keepsFamily S V verifyBudget publicKey sampleWitness)
    (honest_grows S V verifyBudget publicKey sampleWitness) (publicOracle_grows S V verifyBudget publicKey sampleWitness)
    (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
    (honest_shiftLaw S V verifyBudget publicKey sampleWitness) (publicOracle_shiftLaw S V verifyBudget publicKey sampleWitness)
    (prepareVerification_shiftLaw S V verifyBudget publicKey sampleWitness) hE.1 hE.2.1 hE.2.2]
  refine (eventExpE_le_mean (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (agree S V verifyBudget publicKey sampleWitness)
    (GoodKey S publicKey) _ _ (InvC (tau := tau) (kappa := kappa)) invC_mono invC_resample invC_query
    (invC_honest S V verifyBudget publicKey sampleWitness) (invC_simulated S V verifyBudget publicKey sampleWitness)
    (invC_pub S V verifyBudget publicKey sampleWitness) (invC_prep S V verifyBudget publicKey sampleWitness hvc) invC_update
    invC_restore (honest_postLaw S V verifyBudget publicKey sampleWitness) (simulated_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness) E (keygen_resampled S V verifyBudget publicKey sampleWitness)
    (keygen_good S V verifyBudget publicKey sampleWitness hsample) (invC_keygen S V verifyBudget publicKey sampleWitness)
    hsignCut hsignRunW hE.2.1 index.val (fuel + 1) (by omega)).trans ?_
  rw [← eventExp_eq_E _ adversary E (simulated_keygen_resampled S V verifyBudget publicKey sampleWitness)
    (simulated_postLaw S V verifyBudget publicKey sampleWitness)
    (fun q => publicOracle_postLaw S V verifyBudget publicKey sampleWitness q)
    (fun pk m sig => prepareVerification_postLaw S V verifyBudget publicKey sampleWitness pk m sig)
    (simulated_keepsFamily S V verifyBudget publicKey sampleWitness)
    (fun q => publicOracle_keepsFamily S V verifyBudget publicKey sampleWitness q)
    (fun pk m sig => prepareVerification_keepsFamily S V verifyBudget publicKey sampleWitness pk m sig)
    (simulated_grows S V verifyBudget publicKey sampleWitness)
    (fun q => publicOracle_grows S V verifyBudget publicKey sampleWitness q)
    (fun pk m sig => prepareVerification_grows S V verifyBudget publicKey sampleWitness pk m sig)
    (simulated_shiftLaw S V verifyBudget publicKey sampleWitness)
    (fun q => publicOracle_shiftLaw S V verifyBudget publicKey sampleWitness q)
    (fun pk m sig => prepareVerification_shiftLaw S V verifyBudget publicKey sampleWitness pk m sig) hE.1 hE.2.1 hE.2.2]
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · first
      | rfl
      | (unfold eventExp; congr 1; congr 1; funext c; cases c <;> rfl)
  · push_cast
    ring

/-- The composed simulation term: three times the fuel plus one, times the
per-call constant at the budget three times the fuel plus two with the
explicit row-stored bound. -/
def εSim (c cKey cOut q : Nat) (εR εS : ℝ≥0∞) (fuel : Nat) : ℝ≥0∞ :=
  3 * ((fuel : ℝ≥0∞) + 1) * εCall (lambda := lambda) (tau := tau) (kappa := kappa)
    (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (3 * (fuel + 1) + 2)) q
      (commitBudget tau kappa * (3 * (fuel + 1) + 2))) εR εS (3 * (fuel + 1) + 2)

/-- The composed forgery bound with the simulation gap in mean form over
the restored fork: the per-call witness swap in mean form for the simulated
scheme's run and cut continuations, the retry bound, and the eight events'
insensitivity to the second branch's history suffix and to the attempts'
embedded families. -/
theorem forgery_le_mean (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat)
    (hSencode : S.encode = fun hidden => psi S.signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hhigher : 1 ≤ higherCount) (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR εS : ℝ≥0∞)
    (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ b, Fintype.card {r : Bits lambda // S.signer.layout.output r = b} ≤ cOut)
    (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (hswapRunW : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
      ∀ (fuel' : Nat) (pk : List Bool)
        (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (h : Terminal (List Bool) (Signature (Spec.BAVC.Digest lambda)
            (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) ×
          Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool)
        (c : Bool),
      mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind fun r =>
          (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c) ≤
        mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey fake message w').bind fun r =>
          (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c) + εS)
    (hswapCut : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
      ∀ (index fuel' : Nat) (pk : List Bool)
        (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (h : Cut (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
          (Signature (Spec.BAVC.Digest lambda)
            (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State → PMF Bool)
        (c : Bool),
      mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey witness message w').bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) ≤
        mean (resampleW resample world) (fun w' => ((simulatedSignWith S publicKey fake message w').bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c) + εS)
    (hok1 : EventOK (maskAfter (F := F) (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) (higherCount := higherCount)
      (w := w) (widths := widths) (State := State)))
    (hok2 : EventOK (fun (_ : Snap F lambda s higherCount w widths State) => notSeparated V))
    (hok3 : EventOK (higherCount := higherCount) (w := w) (widths := widths) (State := State) (seedCollision V))
    (hok4 : EventOK (fun (_ : Snap F lambda s higherCount w widths State) => slopeWin S V))
    (hok5 : EventOK (fun (_ : Snap F lambda s higherCount w widths State) => zeroChallenge V encode))
    (hok6 : EventOK (higherCount := higherCount) (w := w) (widths := widths) (State := State) (schwartzZippel S V encode))
    (hok7 : EventOK (higherCount := higherCount) (w := w) (widths := widths) (State := State) (batchingBad S V))
    (hok8 : EventOK (higherCount := higherCount) (w := w) (widths := widths) (State := State) (rsdSolved S V)) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true +
            εSim (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εS fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => notSeparated V)
            fuel) true + εSim (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εS fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (seedCollision V) fuel)
            true + εSim (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εS fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => slopeWin S V)
            fuel) true + εSim (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εS fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (fun _ => zeroChallenge V encode) fuel) true +
            εSim (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εS fuel) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (schwartzZippel S V encode) fuel) true +
            εSim (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εS fuel) +
         (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (batchingBad S V) fuel)
            true + εSim (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εS fuel) +
          (solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel +
            εSim (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εS fuel)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  have hgap := hgap_mean S V verifyBudget publicKey sampleWitness adversary hlambda (Nat.pos_iff_ne_zero.mp htau)
    (payload_consistent S hSencode hhigher) hsample hvc _ εR εS fuel
    (fun world hw => rowTerm_mean_le_explicit S (Nat.pos_iff_ne_zero.mp htau) world _ hw.1 (invC_game _ world hw).1
      hin hl hL c hfiber cKey hkey cOut hout _ (invC_game _ world hw).2 q hq)
    hretry hswapRunW hswapCut
  exact forgery_le_simulated_events S V verifyBudget publicKey sampleWitness adversary
    (simulatedScheme S V verifyBudget publicKey sampleWitness) hlambda htau encode hmid hencoding hlinesEnc hencode bound
    hcommit hverify hone fuel (εSim (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR εS fuel)
    (hgap _ hok1) (hgap _ hok2) (hgap _ hok3) (hgap _ hok4) (hgap _ hok5) (hgap _ hok6) (hgap _ hok7) (hgap _ hok8)

end
end SDitH.Proofs.SimulationGapMean2
