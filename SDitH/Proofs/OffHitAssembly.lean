import SDitH.Proofs.OffHitChain
import SDitH.Proofs.TupleOfDigest

/-! The off-hit chain assembled at fixed draws. Only the digest's tuple and
the default tuple carry mass, so the fake side's lower bound is summed
over at most two tuples; with the data-level closeness hypothesis on the
mixing families, the honest distinct mass of the inner mean is bounded by
the fake one plus a slack of twice the mixture's loss and the closeness,
all scaled by the number of blocks less the bad targets to the number of
executions. -/

namespace SDitH.Proofs.OffHitAssembly

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

open SigningData LeafJointBound LeafBlockBound LeafMixture LeafExchangeDistinct PhaseViewLeafAll HonestLeafBound
open HiddenKeysAllExchange TreeHistoryExchange TreeExchange NodeExchange PosteriorNodeBound TreeDistinct TreeStepFresh
open SharedPrune HiddenLeafNode
open Spec.SlopeConsistencyGame (Out)
open Spec.HashCipherTrace (runFixed Result)
open Spec.HashCipherProgram (procedure Program)
open Spec.IdealCipher (Family)
open Spec.SeedTree (leafAddress node)

open SlicedInvariance LeafMixtureGen HitTerm TouchTotal TouchAssembly RootPosteriorBound TreeDistinct
open Spec.SlopeConsistencyGame (Out)
open Spec.HashCipherTrace (runFixed Result)
open Spec.HashCipherProgram (procedure Program)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)

open OffHitSetup
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)

open OffHitChain TupleOfDigest
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open Spec.SeedTree (leafAddress node)

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (publicKey message : List Bool) (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda)
  (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
  (Ψ : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞)

/-- The tuples carrying mass: the digest's and the default. -/
def tuples : Finset (Fin tau → Fin (2 ^ kappa)) := {hiddenOfDigest S digest, defaultTuple}

omit [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem card_tuples_le : (tuples S digest).card ≤ 2 := Finset.card_le_two

/-- The sliced data vanishes outside the two tuples. -/
theorem sliced_eq_zero_of_not_mem (wsign : Fin (selectorCount widths * w) → ZMod 2) (h : Fin tau → Fin (2 ^ kappa))
    (hh : h ∉ tuples S digest) (nodes : Nat → Spec.BAVC.Seed lambda) (g : Family (Bits lambda) (Bits lambda)) :
    sliced S publicKey message salt root digest wsign world Ψ h nodes g = 0 := by
  have hne : ∀ q : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Spec.BAVC.Digest lambda)),
      sigHidden S q.1 = hiddenOfDigest S digest ∨ sigHidden S q.1 = defaultTuple → sigHidden S q.1 ≠ h := by
    intro q hq heq
    apply hh
    unfold tuples
    rcases hq with h1 | h1
    · rw [← heq, h1]; exact Finset.mem_insert_self _ _
    · rw [← heq, h1]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  unfold sliced tailData
  refine mul_eq_zero_of_right _ ((mean_le_const _ _ 0 fun o _ => mean_le_const _ _ 0 fun out' _ =>
    mean_le_const _ _ 0 fun q hq => ?_).antisymm (zero_le _))
  have h0 := hne q (sigHidden_simPost S publicKey message salt digest out'.state world.hashTable q hq)
  simp [h0, indicator]

/-- The mixing family vanishes outside the two tuples. -/
theorem Fct_eq_zero_of_not_mem (wsign : Fin (selectorCount widths * w) → ZMod 2) (h : Fin tau → Fin (2 ^ kappa))
    (hh : h ∉ tuples S digest) (x : Fin tau → Bits lambda) (g : Family (Bits lambda) (Bits lambda)) :
    Fct S publicKey message salt root digest world Ψ wsign h x g = 0 :=
  sliced_eq_zero_of_not_mem S publicKey message salt root digest world Ψ wsign h hh _ g

omit [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A sum over the tuples vanishing outside the two tuples is the sum over
the two. -/
theorem sum_tuples (f : (Fin tau → Fin (2 ^ kappa)) → ℝ≥0∞) (hf : ∀ h, h ∉ tuples S digest → f h = 0) :
    ∑ h : Fin tau → Fin (2 ^ kappa), f h = ∑ h ∈ tuples S digest, f h :=
  (Finset.sum_subset (Finset.subset_univ _) fun h _ hh => hf h hh).symm

/-- The data-level closeness: on the distinct trees, the honest mixing
family's sum over the tuples and the block tuples is within the number of
block tuples times the slack of the fake one. -/
def DataClose (B : Nat) (δ : ℝ≥0∞) : Prop :=
  ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
    InvC (tau := tau) (kappa := kappa) B world → ∀ (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda)
    (Ψ : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞), (∀ x, Ψ x ≤ 1) →
    ∀ g : Family (Bits lambda) (Bits lambda), Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory →
    (∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda,
      Fct S publicKey message salt root digest world Ψ witness h x g) ≤
    (∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda,
      Fct S publicKey message salt root digest world Ψ fake h x g) + (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * δ

variable (witness fake : Fin (selectorCount widths * w) → ZMod 2)
  (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
  (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g world.other.cipherHistory)
  (hΨ : ∀ x, Ψ x ≤ 1)

include hL2 hin hl hL hfiber hpos hΨ in
/-- The honest side with the data-level closeness: the distinct mass of the
honest inner mean, scaled, is at most the fake mixing family's sum plus the
closeness. -/
theorem honest_side (δ : ℝ≥0∞)
    (hdata : ∀ g : Family (Bits lambda) (Bits lambda),
      Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory →
      (∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda,
        Fct S publicKey message salt root digest world Ψ witness h x g) ≤
      (∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda,
        Fct S publicKey message salt root digest world Ψ fake h x g) + (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * δ) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          SigningData.inner S publicKey message salt root digest witness world Ψ g) ≤
      (∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
        (fun g => distInd S.signer salt world.other root g * Fct S publicKey message salt root digest world Ψ fake h x g)) +
      (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * δ * mean (posterior world.other.cipherHistory) (distInd S.signer salt world.other root) := by
  refine (honest_upper S publicKey message salt root digest witness world Ψ hL2 hin hl hL c hfiber hpos hΨ).trans ?_
  -- the double sums as means of the double sums
  have hswap : ∀ wsign : Fin (selectorCount widths * w) → ZMod 2,
      (∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
        (fun g => distInd S.signer salt world.other root g * Fct S publicKey message salt root digest world Ψ wsign h x g)) =
      mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
        ∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda, Fct S publicKey message salt root digest world Ψ wsign h x g) := by
    intro wsign
    rw [← sum_mean_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← sum_mean_mul]
  rw [hswap, hswap, ← mean_const_mul, ← mean_add]
  refine mean_le_mean _ _ _ fun g _ => ?_
  by_cases hd : Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory
  · simp only [distInd, hd, decide_true, RandomOracleTrap.indicator_true, one_mul, mul_one]
    exact hdata g hd
  · simp only [distInd, hd, decide_false, RandomOracleTrap.indicator_false, zero_mul, mul_zero, add_zero, le_refl]

include hL2 hin hl hL hfiber hpos hΨ in
/-- The fake side over the two tuples: the fake mixing family's sum plus the
distinct mass scaled by the tuples' count is at most the distinct mass
times the block tuples' count times that count plus the fake distinct mass
of the inner mean, scaled. -/
theorem fake_side :
    (∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
        (fun g => distInd S.signer salt world.other root g * Fct S publicKey message salt root digest world Ψ fake h x g)) +
      ((tuples S digest).card : ℝ≥0∞) *
        (((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
          mean (posterior world.other.cipherHistory) (distInd S.signer salt world.other root)) ≤
    ((tuples S digest).card : ℝ≥0∞) *
        ((Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * mean (posterior world.other.cipherHistory) (distInd S.signer salt world.other root)) +
      ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          SigningData.inner S publicKey message salt root digest fake world Ψ g) := by
  set N' : ℝ≥0∞ :=
    ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) with hN'
  set M : ℝ≥0∞ := (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) with hM
  set dI := distInd S.signer salt world.other root with hdI
  -- per tuple, the plain mixture lower bound
  have hper : ∀ h : Fin tau → Fin (2 ^ kappa),
      (∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
        (fun g => dI g * Fct S publicKey message salt root digest world Ψ fake h x g)) +
        N' ^ tau * mean (posterior world.other.cipherHistory) dI ≤
      M * mean (posterior world.other.cipherHistory) dI +
        N' ^ tau * mean (posterior world.other.cipherHistory) (fun g => dI g *
          sliced S publicKey message salt root digest fake world Ψ h (baseTree S.signer salt g root) g) := by
    intro h
    have := mixture_lower S.signer salt world.other root h hL2 hin hl hL hpos c hfiber
      (Fct S publicKey message salt root digest world Ψ fake h)
      (fun x g => sliced_le_one S publicKey message salt root digest fake world Ψ hΨ h _ g)
      (fun x e v' g hd hbad => Fct_inv S publicKey message salt root digest world Ψ hL2 hin hl hL fake h x e v' g hd hbad)
    simpa only [Fct_blocks S publicKey message salt root digest world Ψ hL2] using this
  -- restrict the tuple sums to the two tuples
  have hzero : ∀ h, h ∉ tuples S digest → (∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
      (fun g => dI g * Fct S publicKey message salt root digest world Ψ fake h x g)) = 0 := by
    intro h hh
    simp [Fct_eq_zero_of_not_mem S publicKey message salt root digest world Ψ fake h hh, mean_const]
  have hzero' : ∀ h, h ∉ tuples S digest → mean (posterior world.other.cipherHistory) (fun g => dI g *
      sliced S publicKey message salt root digest fake world Ψ h (baseTree S.signer salt g root) g) = 0 := by
    intro h hh
    simp [sliced_eq_zero_of_not_mem S publicKey message salt root digest world Ψ fake h hh, mean_const]
  calc _ = ∑ h ∈ tuples S digest, ((∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
          (fun g => dI g * Fct S publicKey message salt root digest world Ψ fake h x g)) +
        N' ^ tau * mean (posterior world.other.cipherHistory) dI) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, sum_tuples S digest _ hzero]
    _ ≤ ∑ h ∈ tuples S digest, (M * mean (posterior world.other.cipherHistory) dI +
        N' ^ tau * mean (posterior world.other.cipherHistory) (fun g => dI g *
          sliced S publicKey message salt root digest fake world Ψ h (baseTree S.signer salt g root) g)) :=
        Finset.sum_le_sum fun h _ => hper h
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← sum_tuples S digest _ hzero',
          sum_mean_mul]
        congr 2
        refine congrArg _ (funext fun g => ?_)
        rw [← inner_eq_sum]

end
end SDitH.Proofs.OffHitAssembly
