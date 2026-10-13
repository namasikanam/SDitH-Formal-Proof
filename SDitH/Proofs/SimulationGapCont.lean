import SDitH.Proofs.SimulationGapCipher
import SDitH.Proofs.ChargeCutCont

/-! The simulation gap and the composed bound with the per-call swap stated
for the game's own continuations. The per-call witness swap over every
continuation of the signing output is not satisfiable, since the output
carries the hidden path; here it is taken only for the continuations the
replay hybrids use: the simulated scheme's run or cut run from the output,
then the final evaluation. The composed statements are otherwise those of
the extended-invariant module. -/

namespace SDitH.Proofs.SimulationGapCont

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
open HeadCommitSplit SimulationGapCipher ChargeCutCont
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
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The simulation gap in mean form under the extended invariant. -/
theorem hgap_of_cipher_cont (hl : 0 < lambda) (htau : tau ≠ 0) (hpc : PayloadConsistent S)
    (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) (εRow εR εS : ℝ≥0∞) (fuel : Nat)
    (σ : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞)
    (hrow : ∀ (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world →
      mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤ εRow)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world → (retryEvent S publicKey witness message world) true ≤ εR)
    (hswapRun : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world →
      ∀ (fuel' : Nat) (pk : List Bool)
        (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (h : Terminal (List Bool) (Signature (Spec.BAVC.Digest lambda)
            (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) → PMF Bool)
        (c : Bool),
      ((simulatedSignWith S publicKey witness message world).bind fun r =>
          (run (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c ≤
        ((simulatedSignWith S publicKey fake message world).bind fun r =>
          (run (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c + σ world)
    (hswapCut : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world →
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
      ((simulatedSignWith S publicKey witness message world).bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c ≤
        ((simulatedSignWith S publicKey fake message world).bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c + σ world)
    (hswapMean : ∀ (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world → mean (resampleW resample world) σ ≤ εS)
    (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true +
        3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) εRow fuel + εR + εS) := by
  have hsignRun : SignRun (C := Bool) (InvC (tau := tau) (kappa := kappa))
      (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (GoodKey S publicKey)
      (chargeOf S htau εR σ fuel) (2 * (fuel + 1) + 1) := by
    intro sk hsk message world hw fuel' pk next trace h c
    obtain ⟨hpk, hsol⟩ := hsk
    rcases sk with ⟨pk', witness⟩
    dsimp only at hpk hsol
    rw [hpk]
    refine (honest_le_simulated_post S V verifyBudget _ sampleWitness hpc witness hsol message world
      (fun r => (run (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness)
        (next r.1) r.2 trace).bind h) (σ world)
      (fun fake c' => hswapRun witness fake message world hw fuel' pk next trace h c') c).trans ?_
    unfold chargeOf
    refine add_le_add_right (add_le_add (add_le_add ?_ (hretry witness message world hw)) le_rfl) _
    exact inputPresent_uniform S hl htau _ witness message world hw.1.2.1 hw.1.1 hw.1.2.2
  have hsignCut : SignCut (C := Bool) (InvC (tau := tau) (kappa := kappa))
      (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (GoodKey S publicKey)
      (chargeOf S htau εR σ fuel) (2 * (fuel + 1) + 1) := by
    intro sk hsk message world hw index fuel' pk next trace h c
    obtain ⟨hpk, hsol⟩ := hsk
    rcases sk with ⟨pk', witness⟩
    dsimp only at hpk hsol
    rw [hpk]
    refine (honest_le_simulated_post S V verifyBudget _ sampleWitness hpc witness hsol message world
      (fun r => (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
        (next r.1) r.2 trace).bind h) (σ world)
      (fun fake c' => hswapCut witness fake message world hw index fuel' pk next trace h c') c).trans ?_
    unfold chargeOf
    refine add_le_add_right (add_le_add (add_le_add ?_ (hretry witness message world hw)) le_rfl) _
    exact inputPresent_uniform S hl htau _ witness message world hw.1.2.1 hw.1.1 hw.1.2.2
  have heps : ∀ (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world →
      mean (resampleW resample world) (chargeOf S htau εR σ fuel) ≤
        εP (lambda := lambda) (tau := tau) (kappa := kappa) εRow fuel + εR + εS := by
    intro world hw
    unfold chargeOf εP
    simp only [mean_add, mean_const]
    exact add_le_add (add_le_add_left (add_le_add_left (add_le_add_right (hrow world hw) _) _) _) (hswapMean world hw)
  unfold randomEventExperiment simEventExperiment
  refine bind_le_bind_add_const' _ _ _ _ true (fun index _ => ?_)
  have hev := ChargeCutCont.eventExp_le_charge (InvC (tau := tau) (kappa := kappa)) invC_mono invC_query
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (agree S V verifyBudget publicKey sampleWitness)
    (GoodKey S publicKey) (chargeOf S htau εR σ fuel) (2 * (fuel + 1) + 1)
    (invC_honest S V verifyBudget publicKey sampleWitness) (invC_pub S V verifyBudget publicKey sampleWitness) invC_update
    hsignRun hsignCut (invC_simulated S V verifyBudget publicKey sampleWitness)
    (keygen_good S V verifyBudget publicKey sampleWitness hsample) (invC_keygen S V verifyBudget publicKey sampleWitness)
    E index.val (fuel + 1) (by omega)
  have hexp := chargeExperiment_le resample
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
    (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (chargeOf S htau εR σ fuel) _ (2 * (fuel + 1) + 1) (InvC (tau := tau) (kappa := kappa)) invC_mono invC_resample invC_query
    (invC_honest S V verifyBudget publicKey sampleWitness) (invC_pub S V verifyBudget publicKey sampleWitness) heps
    (keygen_resampled S V verifyBudget publicKey sampleWitness) (invC_keygen S V verifyBudget publicKey sampleWitness)
    index.val (fuel + 1) (by omega)
  have hfork := chargeFork_le resample resample_idem
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary
    (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (simulated_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (chargeOf S htau εR σ fuel) _ (2 * (fuel + 1) + 1) (InvC (tau := tau) (kappa := kappa)) invC_mono invC_resample invC_query
    (invC_honest S V verifyBudget publicKey sampleWitness) (invC_pub S V verifyBudget publicKey sampleWitness)
    (invC_simulated S V verifyBudget publicKey sampleWitness) (invC_pub S V verifyBudget publicKey sampleWitness)
    invC_update heps (keygen_resampled S V verifyBudget publicKey sampleWitness)
    (invC_keygen S V verifyBudget publicKey sampleWitness) index.val (fuel + 1) (by omega)
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


/-- The composed forgery bound with the row-stored term explicit and the
cipher-history hypothesis discharged by the extended invariant. -/
theorem forgery_le_cipher_cont (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
    (εR εS : ℝ≥0∞)
    (σ : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞)
    (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ b, Fintype.card {r : Bits lambda // S.signer.layout.output r = b} ≤ cOut)
    (q : Nat) (hq : commitBudget tau kappa * (2 * (fuel + 1) + 1) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world → (retryEvent S publicKey witness message world) true ≤ εR)
    (hswapRun : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world →
      ∀ (fuel' : Nat) (pk : List Bool)
        (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
        (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
        (h : Terminal (List Bool) (Signature (Spec.BAVC.Digest lambda)
            (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
          (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
          (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) → PMF Bool)
        (c : Bool),
      ((simulatedSignWith S publicKey witness message world).bind fun r =>
          (run (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c ≤
        ((simulatedSignWith S publicKey fake message world).bind fun r =>
          (run (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
            trace).bind h) c + σ world)
    (hswapCut : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world →
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
      ((simulatedSignWith S publicKey witness message world).bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c ≤
        ((simulatedSignWith S publicKey fake message world).bind fun r =>
          (cut (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
            r.2 trace).bind h) c + σ world)
    (hswapMean : ∀ (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (2 * (fuel + 1) + 1) world → mean (resampleW resample world) σ ≤ εS) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true +
            (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (2 * (fuel + 1) + 1)) q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => notSeparated V)
            fuel) true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (2 * (fuel + 1) + 1)) q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (seedCollision V) fuel)
            true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (2 * (fuel + 1) + 1)) q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => slopeWin S V)
            fuel) true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (2 * (fuel + 1) + 1)) q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (fun _ => zeroChallenge V encode) fuel) true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (2 * (fuel + 1) + 1)) q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (schwartzZippel S V encode) fuel) true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (2 * (fuel + 1) + 1)) q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (batchingBad S V) fuel)
            true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (2 * (fuel + 1) + 1)) q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
          (solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (2 * (fuel + 1) + 1)) q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS)))) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_simulator S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc
    hencode bound hcommit hverify hone fuel
    (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa)
      (rowBound lambda tau kappa c cKey cOut (commitBudget tau kappa * (2 * (fuel + 1) + 1)) q
        (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))
    (fun E => hgap_of_cipher_cont S V verifyBudget publicKey sampleWitness adversary hlambda (Nat.pos_iff_ne_zero.mp htau)
      (payload_consistent S hSencode hhigher) hsample _ εR εS fuel σ
      (fun world hw => rowTerm_mean_le_explicit S (Nat.pos_iff_ne_zero.mp htau) world _ hw.1 (invC_game _ world hw).1
        hin hl hL c hfiber cKey hkey cOut hout _ (invC_game _ world hw).2 q hq)
      hretry hswapRun hswapCut hswapMean E)

end
end SDitH.Proofs.SimulationGapCont
