import SDitH.Proofs.SwapCloseSplit
import SDitH.Proofs.PhaseViewLeafAll
import SDitH.Proofs.TailRun
import SDitH.Proofs.PrefixOrMention

/-! The signing's data after the phase. The inner mean of the off-hit
pruned mean at a family is the sum, over the hidden tuples, of the
tuple's hit factor times the mean, over the phase view pruned at the
tuple's keys, of the tuple's data: the tail from the commitments and the
tree's seeds, the post-processing, the tuple's indicator and the
functional over the world resampled from the pruned history. The tail is
hash-only, so the family and the cipher history enter only through the
pruned history. -/

namespace SDitH.Proofs.SigningData

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

open SwapClose SwapCloseSplit PhaseViewLeaf CommitPhaseLeaf CommitRunLeaf CommitRunExchange TailRun PrefixOrMention HiddenTuple
open RunBind RunHistoryShift CommitPhaseExchange SharedPrune
open NodeTouchBound (sum_mean)
open HiddenSlice (mean_congr_support)
open Spec.SharedSigner (commitProgram commitBudget)
open Spec.SlopeConsistencyGame (Out)
open Spec.HashCipherTrace (runFixed Result)
open Spec.HashCipherProgram (procedure Program)
open Spec.IdealCipher (Family)

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (publicKey message : List Bool) (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda)
  (wsign : Fin (selectorCount widths * w) → ZMod 2)
  (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
  (Ψ : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞)

/-- The trivial family, for runs and resamplings that ignore the family. -/
def trivialFamily : Family (Bits lambda) (Bits lambda) := fun _ => Equiv.refl _

/-- The keys of a hidden tuple's paths under a family. -/
def tupleKeys (h : Fin tau → Fin (2 ^ kappa)) (g : Family (Bits lambda) (Bits lambda)) : List (Bits lambda) :=
  hiddenKeysAll S.signer.layout g S.signer.variant salt root h

/-- The data after the phase for a tuple: the tail from the commitments and
the seeds, the post-processing, the tuple's indicator and the functional
over the world resampled from the pruned history. -/
def tailData (h : Fin tau → Fin (2 ^ kappa)) (nodes : Nat → Spec.BAVC.Seed lambda) (commits : Fin tau × Fin (2 ^ kappa) → Spec.BAVC.Digest lambda)
    (table : List Bool → Option (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (hashes : List (List Bool × Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (trace : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))))
    (pruned : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) : ℝ≥0∞ :=
  mean (runFixed procedure trivialFamily (tau + 4) (commitTail S.signer salt wsign nodes commits) table hashes [] trace) fun out' =>
    mean (simPost S publicKey message salt digest out'.state world.hashTable) fun q =>
      indicator (decide (sigHidden S q.1 = h)) *
        mean (resampleW resample ⟨q.2, ⟨trivialFamily, out'.hashTable, out'.hashHistory, pruned, out'.trace⟩⟩) fun w'' => Ψ (q.1, w'')

/-- The inner mean of the off-hit pruned mean at a family. -/
def inner (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) (setFamily world g)) fun r =>
    indicator (!hitPre S salt root world r) *
      mean (resampleW resample (pruneW (outKeys S.signer salt root (sigHidden S) r) r.2)) fun w'' => Ψ (r.1, w'')

/-- The tuple-sliced data at a family: the hit factor times the mean over
the phase view pruned at the tuple's keys of the tuple's data at the
tree's seeds. -/
def sliced (h : Fin tau → Fin (2 ^ kappa)) (nodes : Nat → Spec.BAVC.Seed lambda) (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  indicator (!touchesG (tupleKeys S salt root h g) world) *
    mean (phaseView S.signer salt g root (tupleKeys S salt root h g) world.other) fun o =>
      tailData S publicKey message salt digest wsign world Ψ h nodes (commitsOf o.state) o.hashTable o.hashHistory o.trace
        o.cipherHistory

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem mean_const_mul {α : Type*} (p : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    mean p (fun a => c * f a) = c * mean p f := by
  unfold mean
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => by ring

/-- The oracle as the phase run continued by the tail, then the
post-processing. -/
theorem commitOracle_eq (g : Family (Bits lambda) (Bits lambda)) :
    commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) (setFamily world g) =
      ((phaseRun S.signer salt g root world.other).bind
        (continueRun g (tau + 4) (commitTail S.signer salt wsign (baseTree S.signer salt g root)))).bind fun out =>
        (simPost S publicKey message salt digest out.state world.hashTable).map fun q =>
          (q.1, ⟨q.2, ⟨g, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩⟩) := by
  unfold commitOracle Spec.SharedScheme.runProgram phaseRun baseTree
  simp only [setFamily]
  rw [commitRun_eq, commitRest_run, PMF.bind_map]
  rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A sum of constants times means is the mean of the sum. -/
theorem sum_const_mul_mean {α γ : Type*} [Fintype γ] (P : PMF α) (c : γ → ℝ≥0∞) (f : γ → α → ℝ≥0∞) :
    ∑ t : γ, c t * mean P (f t) = mean P (fun o => ∑ t : γ, c t * f t o) := by
  simp only [← mean_const_mul]
  exact sum_mean P (fun t o => c t * f t o) Finset.univ

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A sum over the tuples selecting one tuple. -/
theorem sum_select {γ : Type*} [Fintype γ] [DecidableEq γ] (sel : γ) (c M : γ → ℝ≥0∞) :
    ∑ h : γ, c h * indicator (decide (sel = h)) * M h = c sel * M sel := by
  have h : ∀ h : γ, c h * indicator (decide (sel = h)) * M h = if h = sel then c h * M h else 0 := by
    intro h
    by_cases hh : sel = h
    · subst hh; simp [indicator]
    · have hh' : h ≠ sel := fun h' => hh h'.symm
      simp [indicator, hh, hh']
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The inner mean is the sum over the tuples of the sliced data at the
expansion's tree. -/
theorem inner_eq_sum (g : Family (Bits lambda) (Bits lambda)) :
    inner S publicKey message salt root digest wsign world Ψ g =
      ∑ h : Fin tau → Fin (2 ^ kappa), sliced S publicKey message salt root digest wsign world Ψ h (baseTree S.signer salt g root) g := by
  unfold inner sliced
  rw [commitOracle_eq]
  simp only [mean_bind, mean_map, phaseView]
  rw [sum_const_mul_mean]
  refine mean_congr_support _ _ _ fun o ho => ?_
  obtain ⟨c, hc⟩ := runFixed_bounded_done g _ _ (commitPhase_bounded S.signer salt _) _ _ _ _ o ho
  rw [continueRun_done g _ _ o c hc, runFixed_history_shift]
  simp only [mean_map, appendHistory, viewOf, hc, commitsOf]
  unfold tailData
  rw [commitTail_family S.signer salt wsign trivialFamily g, sum_const_mul_mean]
  refine mean_congr_support _ _ _ fun b hb => ?_
  have hb0 : b.cipherHistory = [] := commitTail_history S.signer salt wsign trivialFamily _ _ _ _ _ _ _ b hb
  simp only [hb0, List.nil_append]
  rw [sum_const_mul_mean]
  refine congrArg _ (funext fun q => ?_)
  simp only [← mul_assoc]
  have hsel := sum_select (sigHidden S q.1) (fun x => indicator (!touchesG (tupleKeys S salt root x g) world))
    (fun x => mean (resampleW resample ⟨q.2, ⟨trivialFamily, b.hashTable, b.hashHistory,
      pruneAt (tupleKeys S salt root x g) o.cipherHistory, b.trace⟩⟩) fun w'' => Ψ (q.1, w''))
  simp only at hsel
  rw [hsel]
  simp only [hitPre, outKeys, tupleKeys, pruneW, pruneShared]
  congr 1

end
end SDitH.Proofs.SigningData
