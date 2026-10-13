import SDitH.Proofs.SwapClose

/-! The closeness slack split into two named targets for any bad event of
the call: the bad term, the probability over the uniform salt, root and
digest, the resampled world and the signing call that the bad event
holds, and the off-bad pruned equality, the exact agreement of the two
signings on the calls without it. Together they give the pruned closeness
with the bad term as slack. The candidate bad event is the pre-call hit:
the world before the call already records an entry at a key of the
signature's hidden path. -/

namespace SDitH.Proofs.SwapCloseSplit

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
open ForgeryEvents MeanHybrid SimulationGapMean2 SwapDischarge MeanHybridCompat MeanCutCompat EventCutCompat ForkPruneCompat
open GamePruneGen GamePrune RunWorld CutWorld SignBridge PruneLawRun HiddenEntries HiddenTuple
open Spec.IdealCipher (Entry)
open Spec.RandomOracleTrap (indicator)
open scoped Classical ENNReal
open TouchBound SimulationGapCompat ForgeryFinal PruneCompatClosure EventRequirements

open SwapClose

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (publicKey : List Bool)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- An indicator is at most one. -/
theorem indicator_le_one (b : Bool) : indicator b ≤ 1 := by
  cases b <;> simp [indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A value at most one is at most its off-event part plus the event. -/
theorem le_off_add_event (b : Bool) (x : ℝ≥0∞) (hx : x ≤ 1) : x ≤ indicator (!b) * x + indicator b := by
  cases b <;> simp [indicator, hx]

/-- The pre-call hit: the world before the call records an entry at a key
of the signature's hidden path. -/
def hitPre (salt root : Bits lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (r : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : Bool :=
  touchesG (outKeys S.signer salt root (sigHidden S) r) world

variable (bad : Bits lambda → Bits lambda → Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → Bool)

/-- The bad term: over the uniform salt, root and digest, the resampled
world and the signing call, the probability of the bad event is at most
the bound. -/
def BadTerm (B : Nat) (ε : ℝ≥0∞) : Prop :=
  ∀ (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
    InvC (tau := tau) (kappa := kappa) B world →
    (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        mean (resampleW resample world) fun w' => mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w') fun r => indicator (bad salt root world r)) ≤ ε

/-- The pruned mean restricted to the calls without the bad event. -/
def prunedMeanOff (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt root : Bits lambda)
    (digest : Spec.BAVC.Digest lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (Ψ : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞) : ℝ≥0∞ :=
  mean (resampleW resample world) fun w' =>
    mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w') fun r =>
      indicator (!bad salt root world r) *
        mean (resampleW resample (pruneW (outKeys S.signer salt root (sigHidden S) r) r.2)) fun w'' => Ψ (r.1, w'')

/-- The off-bad pruned equality of the two signings. -/
def PrunedEqualOff (B : Nat) : Prop :=
  ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt root : Bits lambda)
    (digest : Spec.BAVC.Digest lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))), InvC (tau := tau) (kappa := kappa) B world →
    ∀ Ψ, prunedMeanOff S publicKey bad witness message salt root digest world Ψ =
      prunedMeanOff S publicKey bad fake message salt root digest world Ψ

/-- The off-bad pruned closeness of the two signings: over the uniform
salt, root and digest, within a slack. -/
def PrunedCloseOff (B : Nat) (ε : ℝ≥0∞) : Prop :=
  ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
    InvC (tau := tau) (kappa := kappa) B world → ∀ Ψ, (∀ x, Ψ x ≤ 1) →
    (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMeanOff S publicKey bad witness message salt root digest world Ψ) ≤
    (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMeanOff S publicKey bad fake message salt root digest world Ψ) + ε

/-- The off-bad equality is the off-bad closeness with no slack. -/
theorem prunedCloseOff_of_equalOff (B : Nat) (h : PrunedEqualOff S publicKey bad B) : PrunedCloseOff S publicKey bad B 0 :=
  fun witness fake message world hw Ψ _ => by
    have hfun : ∀ (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda),
        prunedMeanOff S publicKey bad witness message salt root digest world Ψ =
          prunedMeanOff S publicKey bad fake message salt root digest world Ψ :=
      fun salt root digest => h witness fake message salt root digest world hw Ψ
    simp only [hfun, add_zero, le_refl]

/-- The pruned mean of a functional bounded by one is at most its off-bad
part plus the bad probability. -/
theorem prunedMean_le_off (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt root : Bits lambda)
    (digest : Spec.BAVC.Digest lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (Ψ : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞) (hΨ : ∀ x, Ψ x ≤ 1) :
    prunedMean S publicKey (sigHidden S) wsign message salt root digest world Ψ ≤
      prunedMeanOff S publicKey bad wsign message salt root digest world Ψ +
        mean (resampleW resample world) (fun w' =>
          mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) w') fun r =>
            indicator (bad salt root world r)) := by
  unfold prunedMean prunedMeanOff
  rw [← mean_add]
  refine mean_le_mean _ _ _ fun w' _ => ?_
  rw [← mean_add]
  refine mean_le_mean _ _ _ fun r _ => ?_
  exact le_off_add_event _ _ (mean_le_const _ _ _ fun x _ => hΨ _)

/-- The off-bad part is at most the pruned mean. -/
theorem off_le_prunedMean (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt root : Bits lambda)
    (digest : Spec.BAVC.Digest lambda) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (Ψ : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞) :
    prunedMeanOff S publicKey bad wsign message salt root digest world Ψ ≤
      prunedMean S publicKey (sigHidden S) wsign message salt root digest world Ψ := by
  unfold prunedMean prunedMeanOff
  refine mean_le_mean _ _ _ fun w' _ => mean_le_mean _ _ _ fun r _ => ?_
  calc _ ≤ 1 * mean (resampleW resample (pruneW (outKeys S.signer salt root (sigHidden S) r) r.2)) (fun w'' => Ψ (r.1, w'')) :=
        mul_le_mul' (indicator_le_one _) le_rfl
    _ = _ := one_mul _

/-- The pruned closeness from the bad term and the off-bad equality. -/
theorem prunedClose_of_split (B : Nat) (ε : ℝ≥0∞) (hbad : BadTerm S publicKey bad B ε) (hoff : PrunedEqualOff S publicKey bad B) :
    PrunedClose S publicKey B ε := by
  intro witness fake message world hw Ψ hΨ
  have hfun : ∀ (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda),
      prunedMeanOff S publicKey bad witness message salt root digest world Ψ =
        prunedMeanOff S publicKey bad fake message salt root digest world Ψ :=
    fun salt root digest => hoff witness fake message salt root digest world hw Ψ
  calc _ ≤ (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMeanOff S publicKey bad witness message salt root digest world Ψ + mean (resampleW resample world) (fun w' => mean (commitOracle S.signer salt witness root (simPost S publicKey message salt digest) w') fun r => indicator (bad salt root world r))) :=
        mean_le_mean _ _ _ fun salt _ => mean_le_mean _ _ _ fun root _ => mean_le_mean _ _ _ fun digest _ =>
          prunedMean_le_off S publicKey bad witness message salt root digest world Ψ hΨ
    _ = (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMeanOff S publicKey bad fake message salt root digest world Ψ) +
        (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        mean (resampleW resample world) (fun w' => mean (commitOracle S.signer salt witness root (simPost S publicKey message salt digest) w') fun r => indicator (bad salt root world r))) := by
        simp only [mean_add, hfun]
    _ ≤ _ := add_le_add (mean_le_mean _ _ _ fun salt _ => mean_le_mean _ _ _ fun root _ => mean_le_mean _ _ _ fun digest _ =>
          off_le_prunedMean S publicKey bad fake message salt root digest world Ψ) (hbad witness message world hw)

/-- The pruned closeness from the bad term and the off-bad closeness, with
the two slacks added. -/
theorem prunedClose_of_split' (B : Nat) (ε₁ ε₂ : ℝ≥0∞) (hbad : BadTerm S publicKey bad B ε₁)
    (hoff : PrunedCloseOff S publicKey bad B ε₂) : PrunedClose S publicKey B (ε₁ + ε₂) := by
  intro witness fake message world hw Ψ hΨ
  calc _ ≤ (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMeanOff S publicKey bad witness message salt root digest world Ψ + mean (resampleW resample world) (fun w' => mean (commitOracle S.signer salt witness root (simPost S publicKey message salt digest) w') fun r => indicator (bad salt root world r))) :=
        mean_le_mean _ _ _ fun salt _ => mean_le_mean _ _ _ fun root _ => mean_le_mean _ _ _ fun digest _ =>
          prunedMean_le_off S publicKey bad witness message salt root digest world Ψ hΨ
    _ = (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMeanOff S publicKey bad witness message salt root digest world Ψ) +
        (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        mean (resampleW resample world) (fun w' => mean (commitOracle S.signer salt witness root (simPost S publicKey message salt digest) w') fun r => indicator (bad salt root world r))) := by
        simp only [mean_add]
    _ ≤ ((mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMeanOff S publicKey bad fake message salt root digest world Ψ) + ε₂) + ε₁ :=
        add_le_add (hoff witness fake message world hw Ψ hΨ) (hbad witness message world hw)
    _ = (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
        prunedMeanOff S publicKey bad fake message salt root digest world Ψ) + (ε₁ + ε₂) := by ring
    _ ≤ _ := add_le_add (mean_le_mean _ _ _ fun salt _ => mean_le_mean _ _ _ fun root _ => mean_le_mean _ _ _ fun digest _ =>
          off_le_prunedMean S publicKey bad fake message salt root digest world Ψ) le_rfl

end
end SDitH.Proofs.SwapCloseSplit
