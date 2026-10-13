import SDitH.Proofs.CandidateReduction
import SDitH.Proofs.SignatureForgeryFork

/-! The forgery advantage of the candidate scheme bounded by the named
events, the extraction probability and the charged-event bound, through
the uniform-index fork experiment: the fork experiment at a random index
is at most the random-index event experiments plus the charged-event
bound, and the forgery-to-fork inequality composes it with the forgery
advantage. This is the composed skeleton; each named event's random-index
probability, the batching step and the signing simulator remain open. -/

namespace SDitH.Proofs.ForgeryReduction

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SignatureQuerySelection Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier
open Spec.PIOPArithmetic (selectorCount)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open CandidateReduction
open scoped Classical ENNReal
noncomputable section

section Generic

variable {A : Type*}

theorem bind_true_le_add_const (p : PMF A) (f g : A → PMF Bool) (c : ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a true ≤ g a true + c) :
    (p.bind f) true ≤ (p.bind g) true + c := by
  simp only [PMF.bind_apply]
  calc ∑' a, p a * f a true ≤ ∑' a, p a * (g a true + c) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ p.support
        · exact mul_le_mul_right (h a ha) _
        · rw [PMF.mem_support_iff, not_not] at ha
          rw [ha]
          simp
    _ = _ := by simp_rw [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Generic

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

/-- The union of the named events and the extraction event. -/
def unionEvent (encode : (Fin tau → Fin (2 ^ kappa)) → F) (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths)) : Bool :=
  maskAfter snapshot result || notSeparated V result || seedCollision V snapshot result || slopeWin S V result ||
    zeroChallenge V encode result || schwartzZippel S V encode snapshot result || extracts S V snapshot result

/-- The fork experiment's success is at most the union event plus the
charged-event bound. -/
theorem fork_le_union (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEvent S V encode) index fuel) true +
      (fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) +
      fuel * (epsilonC lambda bound (fuel * (bound + bound)) + epsilonC lambda bound (fuel * (bound + bound))) +
      (2 : ℝ≥0∞) * (fuel * (bound * digestInv lambda + bound * digestInv lambda) +
        fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))))) := by
  have hmono : (CandidateForkOutcome.goodForkExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true ≤
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEvent S V encode) index fuel) true := by
    unfold CandidateForkOutcome.goodForkExperiment eventExperiment
    refine bind_true_mono _ _ _ fun c hc => ?_
    cases c with
    | ended terminal => exact le_rfl
    | saved snapshot =>
      refine map_true_mono_support _ _ _ fun result hr hgood => ?_
      exact good_implies_events S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding
        hlinesEnc hencode index fuel _ hc snapshot rfl result hr hgood
  exact (CandidateForkOutcome.forkExperiment_split S V verifyBudget publicKey sampleWitness adversary index fuel).trans
    (add_le_add hmono (CandidateForkOutcome.forkBad_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit
      hverify hone index fuel))

/-- An event's probability at a uniformly random index. -/
def randomEventExperiment (E : Snap F lambda s higherCount w widths State →
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (fuel : Nat) : PMF Bool :=
  (PMF.uniformOfFintype (Fin (fuel + 1))).bind fun index =>
    eventExperiment S V verifyBudget publicKey sampleWitness adversary E index.val (fuel + 1)

theorem randomEventExperiment_or_le (E₁ E₂) (fuel : Nat) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot result =>
        E₁ snapshot result || E₂ snapshot result) fuel) true ≤
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E₁ fuel) true +
        (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E₂ fuel) true := by
  unfold randomEventExperiment
  exact ForkGoodOutcome.bind_true_le_add _ _ _ _ fun index _ =>
    eventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary E₁ E₂ index.val (fuel + 1)

theorem randomForkExperiment_eq (fuel : Nat) :
    randomForkExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel =
      (PMF.uniformOfFintype (Fin (fuel + 1))).bind fun index =>
        forkExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index.val
          (fuel + 1) := by
  unfold randomForkExperiment randomCutExperiment forkExperiment
  rw [PMF.bind_bind]

/-- The random-index fork experiment is at most the random-index union event
plus the charged-event bound. -/
theorem random_fork_le_union (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEvent S V encode) fuel) true +
      ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
          epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
      (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) + epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
      (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
        (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
          epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) := by
  rw [randomForkExperiment_eq]
  unfold randomEventExperiment
  refine bind_true_le_add_const _ _ _ _ fun index _ => ?_
  have h := fork_le_union S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc
    hencode bound hcommit hverify hone index.val (fuel + 1)
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The composed skeleton: the forgery advantage against the candidate
scheme, less the fresh-hash guessing term, squared, is at most the squared
action budget times the random-index named events, the extraction
probability, the charged-event bound and the guessing term. -/
theorem forgery_le_events (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
         (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => slopeWin S V) fuel) true +
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
  have hunion := random_fork_le_union S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding
    hlinesEnc hencode bound hcommit hverify hone fuel
  have hsplit : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEvent S V encode) fuel) true ≤
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => notSeparated V) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => slopeWin S V) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (schwartzZippel S V encode) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (extracts S V) fuel) true := by
    unfold unionEvent
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    exact randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel
  refine hfork.trans (mul_le_mul_right ?_ _)
  refine add_le_add_left ?_ _
  exact hunion.trans (add_le_add_left hsplit _)

end
end SDitH.Proofs.ForgeryReduction
