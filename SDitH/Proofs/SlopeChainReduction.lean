import SDitH.Proofs.SlopeCoverFork
import SDitH.Proofs.ForgeryEvents

/-! The composed forgery bound's skeleton with the mask trap, the witnessed
pair and the unseen match in place of the slope event: the union event,
the fork-to-union step, the random-index step, the forgery skeleton, the
extraction split and the per-event simulation gaps (the three new events
stay in the real experiment, where they are bounded directly). -/

namespace SDitH.Proofs.SlopeChainReduction

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SignatureQuerySelection Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier
open Spec.PIOPArithmetic (selectorCount)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open CandidateReduction ForgeryReduction ExtractionSplit SimulatedSolver ForgeryEvents SlopeCoverFork
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

/-- The union of the named events (with the trap, the witnessed pair and
the unseen match) and the extraction event. -/
def unionEventS (encode : (Fin tau → Fin (2 ^ kappa)) → F) (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths)) : Bool :=
  maskAfter snapshot result || notSeparated V result || seedCollision V snapshot result ||
    (slopeTrap S V snapshot || witnessedFork snapshot result || unseenFork V snapshot result) ||
    zeroChallenge V encode result || schwartzZippel S V encode snapshot result || extracts S V snapshot result

/-- The fork experiment's success is at most the union event plus the
charged-event bound. -/
theorem fork_le_union_S (hlayout : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (index fuel : Nat) :
    (forkExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel) true ≤
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEventS S V encode) index fuel) true +
      (fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) +
      fuel * (epsilonC lambda bound (fuel * (bound + bound)) + epsilonC lambda bound (fuel * (bound + bound))) +
      (2 : ℝ≥0∞) * (fuel * (bound * digestInv lambda + bound * digestInv lambda) +
        fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))))) := by
  have hmono : (CandidateForkOutcome.goodForkExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true ≤
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEventS S V encode) index fuel) true := by
    unfold CandidateForkOutcome.goodForkExperiment eventExperiment
    refine bind_true_mono _ _ _ fun c hc => ?_
    cases c with
    | ended terminal => exact le_rfl
    | saved snapshot =>
      refine map_true_mono_support _ _ _ fun result hr hgood => ?_
      exact good_implies_events_D S V verifyBudget publicKey sampleWitness adversary hlayout hl hL hlambda htau encode hmid
        hencoding hlinesEnc hencode index fuel _ hc snapshot rfl result hr hgood
  exact (CandidateForkOutcome.forkExperiment_split S V verifyBudget publicKey sampleWitness adversary index fuel).trans
    (add_le_add hmono (CandidateForkOutcome.forkBad_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit
      hverify hone index fuel))

/-- The random-index fork experiment is at most the random-index union event
plus the charged-event bound. -/
theorem random_fork_le_union_S (hlayout : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) :
    (randomForkExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel) true ≤
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEventS S V encode) fuel) true +
      ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
          epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
      (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) + epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
      (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
        (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
          epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) := by
  rw [randomForkExperiment_eq]
  unfold randomEventExperiment
  refine bind_true_le_add_const _ _ _ _ fun index _ => ?_
  have h := fork_le_union_S S V verifyBudget publicKey sampleWitness adversary hlayout hl hL hlambda htau encode hmid hencoding
    hlinesEnc hencode bound hcommit hverify hone index.val (fuel + 1)
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The forgery skeleton with the three events in place of the slope event. -/
theorem forgery_le_events_S (hlayout : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        ((randomEventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => notSeparated V) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot _ => slopeTrap S V snapshot)
            fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => witnessedFork snapshot)
            fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => unseenFork V snapshot)
            fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (schwartzZippel S V encode) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (extracts S V) fuel) true +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  have hfork := SignatureForgeryFork.forgery_to_fork (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)
    adversary fuel
  have hunion := random_fork_le_union_S S V verifyBudget publicKey sampleWitness adversary hlayout hl hL hlambda htau encode hmid
    hencoding hlinesEnc hencode bound hcommit hverify hone fuel
  have hsplit : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEventS S V encode) fuel) true ≤
      ((randomEventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => notSeparated V) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true +
      ((randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot _ => slopeTrap S V snapshot)
        fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => witnessedFork snapshot)
        fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => unseenFork V snapshot)
        fuel) true)) +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (schwartzZippel S V encode) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (extracts S V) fuel) true := by
    unfold unionEventS
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add ?_ ?_
    · refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
      refine add_le_add_left ?_ _
      exact randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel
    · refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
      refine add_le_add_left ?_ _
      exact randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel
  refine hfork.trans (mul_le_mul_right ?_ _)
  refine add_le_add_left ?_ _
  refine hunion.trans (add_le_add_left ?_ _)
  refine hsplit.trans (le_of_eq ?_)
  ring

/-- The forgery bound with the extraction event split into the batching event
and the solution event. -/
theorem forgery_le_events_split_S (hlayout : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        ((randomEventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => notSeparated V) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot _ => slopeTrap S V snapshot)
            fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => witnessedFork snapshot)
            fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => unseenFork V snapshot)
            fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (schwartzZippel S V encode) fuel) true +
         ((randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (batchingBad S V) fuel) true +
          (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (rsdSolved S V) fuel) true) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  refine (forgery_le_events_S S V verifyBudget publicKey sampleWitness adversary hlayout hl hL hlambda htau encode hmid hencoding
    hlinesEnc hencode bound hcommit hverify hone fuel).trans (mul_le_mul_right ?_ _)
  refine add_le_add_left (add_le_add_left (add_le_add_right ?_ _) _) _
  refine (randomEventExperiment_mono S V verifyBudget publicKey sampleWitness adversary (extracts S V)
    (fun snapshot result => batchingBad S V snapshot result || rsdSolved S V snapshot result)
    (fun snapshot result h => extracts_split S V snapshot result h) fuel).trans ?_
  exact randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel

variable (sim : Scheme (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
    (Signature (Spec.BAVC.Digest lambda) (Option (Bod F lambda tau kappa s higherCount w widths)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
    (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))

/-- The forgery reduction with the simulation gap taken for the seven
transferred events, the three new events staying in the real experiment. -/
theorem forgery_le_simulated_events_S (hlayout : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) (epsSim : ℝ≥0∞)
    (hgap1 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter fuel) true ≤
      (simEventExperiment adversary sim maskAfter fuel) true + epsSim)
    (hgap2 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => notSeparated V) fuel) true ≤
      (simEventExperiment adversary sim (fun _ => notSeparated V) fuel) true + epsSim)
    (hgap3 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true ≤
      (simEventExperiment adversary sim (seedCollision V) fuel) true + epsSim)
    (hgap5 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) fuel) true ≤
      (simEventExperiment adversary sim (fun _ => zeroChallenge V encode) fuel) true + epsSim)
    (hgap6 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (schwartzZippel S V encode) fuel) true ≤
      (simEventExperiment adversary sim (schwartzZippel S V encode) fuel) true + epsSim)
    (hgap7 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (batchingBad S V) fuel) true ≤
      (simEventExperiment adversary sim (batchingBad S V) fuel) true + epsSim)
    (hgap8 : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (rsdSolved S V) fuel) true ≤
      (simEventExperiment adversary sim (rsdSolved S V) fuel) true + epsSim) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary sim maskAfter fuel) true + epsSim) +
         ((simEventExperiment adversary sim (fun _ => notSeparated V) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (seedCollision V) fuel) true + epsSim) +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot _ => slopeTrap S V snapshot)
            fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => witnessedFork snapshot)
            fuel) true +
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => unseenFork V snapshot)
            fuel) true +
         ((simEventExperiment adversary sim (fun _ => zeroChallenge V encode) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (schwartzZippel S V encode) fuel) true + epsSim) +
         (((simEventExperiment adversary sim (batchingBad S V) fuel) true + epsSim) +
          (solverSuccess S V adversary sim htau fuel + epsSim)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  refine (forgery_le_events_split_S S V verifyBudget publicKey sampleWitness adversary hlayout hl hL hlambda htau encode hmid
    hencoding hlinesEnc hencode bound hcommit hverify hone fuel).trans (mul_le_mul_right ?_ _)
  refine add_le_add_left (add_le_add_left ?_ _) _
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hgap1 hgap2) hgap3)
    le_rfl) le_rfl) le_rfl) hgap5) hgap6)
    (add_le_add hgap7 (hgap8.trans (add_le_add_left (solverSuccess_ge S V adversary sim htau fuel) _)))

end
end SDitH.Proofs.SlopeChainReduction
