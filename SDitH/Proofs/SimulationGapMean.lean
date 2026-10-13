import SDitH.Proofs.CandidateResample
import SDitH.Proofs.ChargeCutExpect
import SDitH.Proofs.ForgeryBoundTrace

/-! The simulation gap with the cipher-dependent terms in mean form. The
per-world charge is the prefix's mention steps, the row-stored term, the
support term, the retry bound and the witness-swap slack of the world;
the per-signature comparison gives the honest signing within the charge
of the simulated signing under any continuation; the charged replay
hybrids give the event experiments within the cut experiment's and the
fork charges; and the expected charges from the resampled key are
bounded by the fuel times the mean charge over a resampled world, which
is the input-present term's explicit part plus the means of the
row-stored term and of the swap slack over the resampled family. -/

namespace SDitH.Proofs.SimulationGapMean

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier Spec.CandidateSimulator Spec.BLC
open Spec.SharedSigner (commitBudget)
open CommitSplitRun (prefixBudget)
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open CandidateReduction ForgeryReduction ExtractionSplit SimulatedSolver CandidateSimulator SimulationGap
open SimulatedWith SignCompare DigestFirstVsSimulated SignComparePost SimulationGapTrace InputPresentBound TraceLength
open PrefixMentionBound (mentionStep)
open RunHybrid EventHybrid CipherResample GameResample ChargeRun ChargeExpect ChargeCut ChargeCutExpect SharedResample
open CandidateResample
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The per-world charge of a signing query. -/
def chargeOf (htau : tau ≠ 0) (εR : ℝ≥0∞)
    (σ : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞)
    (fuel : Nat)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (prefixBudget tau kappa),
      mentionStep lambda tau (commitBudget tau kappa * (2 * (fuel + 1) + 1) + i) +
    (rowTerm S htau world) true +
    ((2 * (fuel + 1) + 1 : Nat) : ℝ≥0∞) * (Fintype.card (Spec.BAVC.Digest lambda) : ℝ≥0∞)⁻¹ + εR + σ world

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The counted invariant ignores the family, so resampling keeps it. -/
theorem invT_resample (n : Nat)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (h : InvT (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) tau kappa n world) :
    ∀ w' ∈ (resampleW resample world).support, InvT tau kappa n w' := by
  intro w' hw
  unfold resampleW at hw
  rw [PMF.support_map] at hw
  obtain ⟨o, ho, rfl⟩ := hw
  unfold resample at ho
  rw [PMF.support_map] at ho
  obtain ⟨f, -, rfl⟩ := ho
  exact h

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The simulation gap with the row-stored and witness-swap terms in mean
form over the resampled family. -/
theorem hgap_of_mean (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S)
    (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) (εRow εR εS : ℝ≥0∞) (fuel : Nat)
    (σ : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞)
    (hrow : ∀ (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvT tau kappa (2 * (fuel + 1) + 1) world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
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
        ((simulatedSignWith S publicKey fake message world).bind h) c + σ world)
    (hswapMean : ∀ (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvT tau kappa (2 * (fuel + 1) + 1) world → mean (resampleW resample world) σ ≤ εS)
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
          chargeOf S htau εR σ fuel world := by
    intro sk hsk message world hw h c
    obtain ⟨hpk, hsol⟩ := hsk
    rcases sk with ⟨pk', witness⟩
    dsimp only at hpk hsol
    subst hpk
    refine (honest_le_simulated_post S V verifyBudget _ sampleWitness hpc witness hsol message world h (σ world)
      (fun fake c' => hswap witness fake message world hw h c') c).trans ?_
    unfold chargeOf
    refine add_le_add_right (add_le_add (add_le_add ?_ (hretry witness message world hw)) le_rfl) _
    exact inputPresent_uniform S hl htau _ witness message world hw.2.1 hw.1 hw.2.2
  have heps : ∀ (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvT tau kappa (2 * (fuel + 1) + 1) world →
      mean (resampleW resample world) (chargeOf S htau εR σ fuel) ≤
        εP (lambda := lambda) (tau := tau) (kappa := kappa) εRow fuel + εR + εS := by
    intro world hw
    unfold chargeOf εP
    simp only [mean_add, mean_const]
    exact add_le_add (add_le_add_left (add_le_add_left (add_le_add_right (hrow world hw) _) _) _) (hswapMean world hw)
  unfold randomEventExperiment simEventExperiment
  refine bind_le_bind_add_const' _ _ _ _ true (fun index _ => ?_)
  have hev := eventExp_le_charge (InvT tau kappa) invT_mono invT_query
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (agree S V verifyBudget publicKey sampleWitness)
    (GoodKey S publicKey) (chargeOf S htau εR σ fuel) (2 * (fuel + 1) + 1)
    (invT_honest S V verifyBudget publicKey sampleWitness) (invT_pub S V verifyBudget publicKey sampleWitness) invT_update
    hsign (invT_simulated S V verifyBudget publicKey sampleWitness)
    (keygen_good S V verifyBudget publicKey sampleWitness hsample) (invT_keygen S V verifyBudget publicKey sampleWitness)
    E index.val (fuel + 1) (by omega)
  have hexp := chargeExperiment_le resample
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
    (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (chargeOf S htau εR σ fuel) _ (2 * (fuel + 1) + 1) (InvT tau kappa) invT_mono invT_resample invT_query
    (invT_honest S V verifyBudget publicKey sampleWitness) (invT_pub S V verifyBudget publicKey sampleWitness) heps
    (keygen_resampled S V verifyBudget publicKey sampleWitness) (invT_keygen S V verifyBudget publicKey sampleWitness)
    index.val (fuel + 1) (by omega)
  have hfork := chargeFork_le resample resample_idem
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary
    (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (simulated_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (chargeOf S htau εR σ fuel) _ (2 * (fuel + 1) + 1) (InvT tau kappa) invT_mono invT_resample invT_query
    (invT_honest S V verifyBudget publicKey sampleWitness) (invT_pub S V verifyBudget publicKey sampleWitness)
    (invT_simulated S V verifyBudget publicKey sampleWitness) (invT_pub S V verifyBudget publicKey sampleWitness)
    invT_update heps (keygen_resampled S V verifyBudget publicKey sampleWitness)
    (invT_keygen S V verifyBudget publicKey sampleWitness) index.val (fuel + 1) (by omega)
  have heq₁ : eventExperiment S V verifyBudget publicKey sampleWitness adversary E index.val (fuel + 1) =
      eventExp (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary E index.val
        (fuel + 1) := by
    unfold eventExperiment eventExp
    first
      | rfl
      | (congr 1; funext c; cases c <;> rfl)
  rw [heq₁]
  refine (hev.trans (add_le_add_right (add_le_add hexp hfork) _)).trans (le_of_eq ?_)
  congr 1 <;> first
    | rfl
    | (unfold eventExp; congr 1; congr 1; funext c; cases c <;> rfl)
    | (unfold eventExp)
    | (push_cast; ring1)

end
end SDitH.Proofs.SimulationGapMean
