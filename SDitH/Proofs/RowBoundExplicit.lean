import SDitH.Proofs.StaleTermBound
import SDitH.Proofs.ForgeryBoundMean

/-! The row-stored term explicit. The row-stored term's mean over the
resampled family is at most an explicit bound in the number of starting
cipher entries, the budget, the fiber bounds of the layout's key and
output maps and the remaining block count; so the composed forgery bound
holds with the row-stored term discharged, under the layout's input
injectivity, the fiber bounds, the cipher-input bounds, and the named
hypothesis that every invariant world's cipher history is matched by some
family and bounded in length. -/

namespace SDitH.Proofs.RowBoundExplicit

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier Spec.CandidateSimulator Spec.BLC
open Spec.SharedSigner (commitBudget)
open Spec.BAVC (Digest)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open CandidateReduction ForgeryReduction ExtractionSplit SimulatedSolver CandidateSimulator SimulationGap
open SimulatedWith SignCompare DigestFirstVsSimulated SimulationGapTrace PayloadConsistent InputPresentBound
open SimulationGapMean CipherResample GameResample ChargeExpect ForgeryBoundMean
open RowStoredPosterior StaleTermBound TreeStepFresh HeadCommitSplit
open scoped Classical ENNReal

noncomputable section

/-- The explicit row-stored bound. -/
def rowBound (lambda tau kappa c cKey cOut h₀ q L : Nat) : ℝ≥0∞ :=
  ((cKey * h₀ : Nat) : ℝ≥0∞) * (Fintype.card (Bits lambda) : ℝ≥0∞)⁻¹ +
    ((tau * 2 ^ kappa - 1 : Nat) : ℝ≥0∞) *
      (2 * (((c * h₀ : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞))) +
    ((cOut * (L + beforeBudget tau kappa + tau) : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

omit [DecidableEq F] in
/-- The row-stored term's mean over the resampled family at an invariant
world is at most the explicit bound. -/
theorem rowTerm_mean_le_explicit (htau : tau ≠ 0)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (B : Nat) (hw : InvT tau kappa B world)
    (hpos : ∃ family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda),
      Spec.IdealCipher.Matches family world.other.cipherHistory)
    (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ b, Fintype.card {r : Bits lambda // S.signer.layout.output r = b} ≤ cOut)
    (h₀ : Nat) (hH : world.other.cipherHistory.length ≤ h₀) (q : Nat) (hq : h₀ + beforeBudget tau kappa ≤ q) :
    mean (resampleW resample world) (fun w' => (rowTerm S htau w') true) ≤
      rowBound lambda tau kappa c cKey cOut h₀ q (commitBudget tau kappa * B) := by
  have hq' : h₀ + 2 * (tau * 2 ^ kappa - 1) ≤ q := by
    have := List.length_pos_of_ne_nil (allPairs_ne_nil (kappa := kappa) htau)
    unfold beforeBudget at hq
    omega
  have hK : (keysOf world.other.cipherHistory).card ≤ h₀ := (keysOf_card_le _).trans hH
  refine (rowTerm_mean_le S htau world hpos hw.2.1 _ hw.2.2 h₀ hH cOut hout q hq).trans ?_
  unfold rowBound
  refine add_le_add ((staleTerm_le S htau world hpos hin hl hL c hfiber cKey hkey h₀ hH q hq').trans ?_) le_rfl
  refine add_le_add (mul_le_mul' ((Nat.cast_le (α := ℝ≥0∞)).mpr (Nat.mul_le_mul_left cKey hK)) le_rfl) ?_
  refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
  exact ENNReal.div_le_div_right ((Nat.cast_le (α := ℝ≥0∞)).mpr (Nat.mul_le_mul_left c hK)) _

variable (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The composed forgery bound with the row-stored term explicit. -/
theorem forgery_le_row (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
    (h₀ q : Nat) (hq : h₀ + beforeBudget tau kappa ≤ q)
    (hgame : ∀ (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvT tau kappa (2 * (fuel + 1) + 1) world →
      (∃ family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda), Spec.IdealCipher.Matches family world.other.cipherHistory) ∧
        world.other.cipherHistory.length ≤ h₀)
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
      InvT tau kappa (2 * (fuel + 1) + 1) world → mean (resampleW resample world) σ ≤ εS) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true +
            (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut h₀ q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => notSeparated V)
            fuel) true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut h₀ q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (seedCollision V) fuel)
            true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut h₀ q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => slopeWin S V)
            fuel) true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut h₀ q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (fun _ => zeroChallenge V encode) fuel) true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut h₀ q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (schwartzZippel S V encode) fuel) true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut h₀ q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
         (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (batchingBad S V) fuel)
            true + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut h₀ q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS))) +
          (solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel + (3 * ((fuel : ℝ≥0∞) + 1) * (εP (lambda := lambda) (tau := tau) (kappa := kappa) (rowBound lambda tau kappa c cKey cOut h₀ q (commitBudget tau kappa * (2 * (fuel + 1) + 1))) fuel + εR + εS)))) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_mean S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc hencode
    bound hcommit hverify hone fuel hSencode hhigher hsample _ εR εS σ
    (fun world hw => rowTerm_mean_le_explicit S (Nat.pos_iff_ne_zero.mp htau) world _ hw (hgame world hw).1 hin hl hL
      c hfiber cKey hkey cOut hout h₀ (hgame world hw).2 q hq)
    hretry hswap hswapMean

end
end SDitH.Proofs.RowBoundExplicit
