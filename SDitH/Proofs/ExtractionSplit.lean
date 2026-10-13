import SDitH.Proofs.ForgeryReduction

/-! The extraction event split into the batching event and the solution
event. On extraction the extracted lines' prover polynomial has a zero
constant term, which by the exact constant-term identity is the batched
mux syndrome residual plus the batched unitary checks of the extracted
witness at the signature's batching challenges. Either that witness is a
solution (zero residual and unitary selectors) or the batching event
occurred (a nonzero residual or a failing selector whose batches cancel).
The forgery bound is restated with the two events in place of the
extraction event; the solution event is the term that a witness-free
solver must inherit, and the batching event is to be bounded by the
freshness of the lines digest. -/

namespace SDitH.Proofs.ExtractionSplit

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SignatureQuerySelection Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier
open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Spec.UnitaryPolynomial Spec.UniformChallenges
open Spec.PIOPArithmetic (selectorCount)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open CandidateReduction ForgeryReduction
open PIOPExtraction (extractedWitness witnessLine randomnessLine)
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

/-- The extracted witness is a solution: zero mux syndrome residual and
unitary selectors. -/
def IsSolution (bits : Fin (selectorCount widths * w) → ZMod 2) : Prop :=
  muxSyndromeResidual widths S.hsize S.H' S.y bits = 0 ∧
    ∀ i (j : Fin widths.length), AtMostOne (selectorAt widths (formatWitness widths bits i) j)

/-- Extraction with a solution. -/
def rsdSolved (snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a _ bodyA bodyB =>
    decide (∃ u, (∀ e c', slopesOf S V a bodyA bodyB e c' = u c') ∧ difference S V snapshot a bodyA bodyB u = 0 ∧
      IsSolution S (extractedWitness bodyA.2.1 u))

/-- Extraction without a solution: the batching event. -/
def batchingBad (snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a _ bodyA bodyB =>
    decide (∃ u, (∀ e c', slopesOf S V a bodyA bodyB e c' = u c') ∧ difference S V snapshot a bodyA bodyB u = 0 ∧
      ¬ IsSolution S (extractedWitness bodyA.2.1 u))

omit [NeZero tau] in
/-- Extraction is the batching event or a solution. -/
theorem extracts_split (snapshot : Snap F lambda s higherCount w widths State) (result)
    (h : extracts S V snapshot result = true) :
    (batchingBad S V snapshot result || rsdSolved S V snapshot result) = true := by
  rcases result with _ | ⟨l, r⟩
  · exact absurd h (by simp [extracts, onAttempts])
  unfold extracts onAttempts at h
  unfold batchingBad rsdSolved onAttempts
  dsimp only at h ⊢
  split at h
  · rename_i a b _ _
    split at h
    · rename_i bodyA bodyB _ _
      obtain ⟨u, hu, hdiff⟩ := decide_eq_true_eq.mp h
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      by_cases hsol : IsSolution S (extractedWitness bodyA.2.1 u)
      · exact Or.inr ⟨u, hu, hdiff, hsol⟩
      · exact Or.inl ⟨u, hu, hdiff, hsol⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [NeZero tau] in
/-- The solution event names an explicit solution of the public instance. -/
theorem rsdSolved_solution (snapshot : Snap F lambda s higherCount w widths State) (result)
    (h : rsdSolved S V snapshot result = true) :
    ∃ left right a b bodyA bodyB u, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.signature.body = some bodyA ∧ b.signature.body = some bodyB ∧
      (∀ e c', slopesOf S V a bodyA bodyB e c' = u c') ∧
      IsSolution S (extractedWitness bodyA.2.1 u) := by
  rcases result with _ | ⟨l, r⟩
  · exact absurd h (by simp [rsdSolved, onAttempts])
  unfold rsdSolved onAttempts at h
  dsimp only at h
  split at h
  · rename_i a b ha hb
    split at h
    · rename_i bodyA bodyB hbodyA hbodyB
      obtain ⟨u, hu, _, hsol⟩ := decide_eq_true_eq.mp h
      exact ⟨l, r, a, b, bodyA, bodyB, u, rfl, ha, hb, hbodyA, hbodyB, hu, hsol⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [NeZero tau] in
/-- The batching event is an exact cancellation of the batched residual and
the batched unitary checks of a non-solution at the signature's batching
challenges. -/
theorem batchingBad_cancellation (snapshot : Snap F lambda s higherCount w widths State) (result)
    (h : batchingBad S V snapshot result = true) :
    ∃ left right a b bodyA bodyB u, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.signature.body = some bodyA ∧ b.signature.body = some bodyB ∧
      (∀ e c', slopesOf S V a bodyA bodyB e c' = u c') ∧
      ¬ IsSolution S (extractedWitness bodyA.2.1 u) ∧
      batchLinearMap S.signer.xi (S.expandBatching snapshot.input.payload.1).1
          (muxSyndromeResidual widths S.hsize S.H' S.y (extractedWitness bodyA.2.1 u)) +
        linearBatch (fun i => unitaryLayers S.signer.xi widths
          (mapSelectors (algebraMap (ZMod 2) F) widths (formatWitness widths (extractedWitness bodyA.2.1 u) i)) 0)
          (S.expandBatching snapshot.input.payload.1).2 = 0 := by
  rcases result with _ | ⟨l, r⟩
  · exact absurd h (by simp [batchingBad, onAttempts])
  unfold batchingBad onAttempts at h
  dsimp only at h
  split at h
  · rename_i a b ha hb
    split at h
    · rename_i bodyA bodyB hbodyA hbodyB
      obtain ⟨u, hu, hdiff, hsol⟩ := decide_eq_true_eq.mp h
      refine ⟨l, r, a, b, bodyA, bodyB, u, rfl, ha, hb, hbodyA, hbodyB, hu, hsol, ?_⟩
      have heq := sub_eq_zero.mp hdiff
      have hzero : (Spec.PIOPComposition.proverRun widths S.hsize S.signer.xi (S.expandBatching snapshot.input.payload.1).1
          (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
          (witnessLine S.signer.xi S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1 u)
          (randomnessLine S.signer.xi S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough u)).eval 0
          = 0 := by
        rw [heq]
        exact CoefficientCompression.coefficientPolynomial_zero _
      rw [PIOPComposition.constant_eq_batches widths S.hsize S.signer.xi _ _ S.H' S.y (extractedWitness bodyA.2.1 u) _
        (fun j => PIOPExtraction.witnessLine_constant S.signer.xi S.signer.p bodyA.1 (fullOf V a bodyA bodyB)
          S.signer.randomCount S.signer.enough bodyA.2.1 u j) _] at hzero
      exact hzero
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem randomEventExperiment_mono (E₁ E₂) (himp : ∀ snapshot result, E₁ snapshot result = true → E₂ snapshot result = true)
    (fuel : Nat) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E₁ fuel) true ≤
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E₂ fuel) true := by
  unfold randomEventExperiment eventExperiment
  refine bind_true_mono _ _ _ fun index _ => ?_
  refine bind_true_mono _ _ _ fun c _ => ?_
  cases c with
  | ended terminal => exact le_rfl
  | saved snapshot => exact ForkCutRun.map_true_mono _ _ _ fun result h => himp snapshot result h

/-- The forgery bound with the extraction event split into the batching event
and the solution event. -/
theorem forgery_le_events_split (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
  refine (forgery_le_events S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc
    hencode bound hcommit hverify hone fuel).trans (mul_le_mul_right ?_ _)
  refine add_le_add_left (add_le_add_left (add_le_add_right ?_ _) _) _
  refine (randomEventExperiment_mono S V verifyBudget publicKey sampleWitness adversary (extracts S V)
    (fun snapshot result => batchingBad S V snapshot result || rsdSolved S V snapshot result)
    (fun snapshot result h => extracts_split S V snapshot result h) fuel).trans ?_
  exact randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel

end
end SDitH.Proofs.ExtractionSplit
