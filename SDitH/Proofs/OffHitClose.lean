import SDitH.Proofs.OffHitAssembly

/-! The off-hit closeness. At fixed draws the assembled chain is cancelled
and divided by the scaling, the scaling is bounded uniformly through the
counted invariant, the distinct-tree failure is added, and the result is
averaged over the salt, the root and the digest. The slack is the hit
bound plus twice the mixture's loss and the data-level closeness, over
the uniform scaling to the number of executions. -/

namespace SDitH.Proofs.OffHitClose

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

open OffHitAssembly
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths) (publicKey : List Bool)

/-- The scaling at the counted invariant's budget: the number of blocks less
the bad targets. -/
def scaleAt (c B : Nat) : Nat :=
  Fintype.card (Bits lambda) - (c * (commitBudget tau kappa * B + 1 + 2 * (tau * 2 ^ kappa)) + 1)

/-- The off-hit slack: the hit bound plus twice the mixture's loss and the
data-level closeness over the uniform scaling to the number of
executions. -/
def εOff (c cKey B : Nat) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * B) +
    (2 * ((Fintype.card (Bits lambda) ^ tau - scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B ^ tau : ℕ) : ℝ≥0∞) +
        ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ) /
      ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The number of block tuples is the number of blocks to the number of
executions. -/
theorem card_tuples_eq : Fintype.card (Fin tau → Bits lambda) = Fintype.card (Bits lambda) ^ tau := by
  rw [Fintype.card_fun, Fintype.card_fin]

variable (message : List Bool) (witness fake : Fin (selectorCount widths * w) → ZMod 2)
  (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
  (Ψ : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞)
  (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
  (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey) (B : Nat)
  (hNb : c * (commitBudget tau kappa * B + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
  (hw : InvC (tau := tau) (kappa := kappa) B world) (hΨ : ∀ x, Ψ x ≤ 1) (δ : ℝ≥0∞)
  (hdata : DataClose S publicKey B δ)

include hL2 hin hl hL hfiber hw hΨ hdata in
/-- The chain cancelled: the honest distinct mass of the inner mean, scaled,
is at most the fake one, scaled, plus the slack's numerator. -/
theorem fixed_cancel (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda) :
    ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          SigningData.inner S publicKey message salt root digest witness world Ψ g) ≤
      ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          SigningData.inner S publicKey message salt root digest fake world Ψ g) +
      (2 * ((Fintype.card (Bits lambda) ^ tau -
          (Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1)) ^ tau : ℕ) : ℝ≥0∞) +
        ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ) := by
  have hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g world.other.cipherHistory := ⟨_, hw.2.1⟩
  set Nn : ℕ := Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) with hNn
  set P := posterior world.other.cipherHistory
  set dI := distInd S.signer salt world.other root
  set A := mean P (fun g => dI g * SigningData.inner S publicKey message salt root digest witness world Ψ g)
  set Bf := mean P (fun g => dI g * SigningData.inner S publicKey message salt root digest fake world Ψ g)
  set D := mean P dI
  set kk : ℕ := (tuples S digest).card
  have hD : D ≤ 1 := mean_le_const _ _ 1 fun g _ => distInd_le_one S.signer salt world.other root g
  have hDtop : (kk : ℝ≥0∞) * ((Nn : ℝ≥0∞) ^ tau * D) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
      (ne_top_of_le_ne_top ENNReal.one_ne_top hD))
  have hNle : Nn ^ tau ≤ Fintype.card (Bits lambda) ^ tau := Nat.pow_le_pow_left (Nat.sub_le _ _) tau
  have hkk : kk ≤ 2 := card_tuples_le S digest
  have hM : (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) = ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) := by
    rw [card_tuples_eq]
  -- the two sides
  have hH := honest_side S publicKey message salt root digest world Ψ witness fake hL2 hin hl hL c hfiber hpos hΨ δ
    (fun g hd => hdata witness fake message world hw salt root digest Ψ hΨ g hd)
  have hF := fake_side S publicKey message salt root digest world Ψ fake hL2 hin hl hL c hfiber hpos hΨ
  -- the combined additive inequality
  have hcomb : (Nn : ℝ≥0∞) ^ tau * A + (kk : ℝ≥0∞) * ((Nn : ℝ≥0∞) ^ tau * D) ≤
      (kk : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * D) + (Nn : ℝ≥0∞) ^ tau * Bf +
        ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ * D := by
    rw [← hM]
    calc (Nn : ℝ≥0∞) ^ tau * A + (kk : ℝ≥0∞) * ((Nn : ℝ≥0∞) ^ tau * D)
        ≤ ((∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda, mean P
            (fun g => dI g * Fct S publicKey message salt root digest world Ψ fake h x g)) +
          (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * δ * D) + (kk : ℝ≥0∞) * ((Nn : ℝ≥0∞) ^ tau * D) :=
          add_le_add hH le_rfl
      _ = ((∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda, mean P
            (fun g => dI g * Fct S publicKey message salt root digest world Ψ fake h x g)) +
          (kk : ℝ≥0∞) * ((Nn : ℝ≥0∞) ^ tau * D)) + (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * δ * D := by ring
      _ ≤ ((kk : ℝ≥0∞) * ((Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * D) + (Nn : ℝ≥0∞) ^ tau * Bf) +
          (Fintype.card (Fin tau → Bits lambda) : ℝ≥0∞) * δ * D := add_le_add hF le_rfl
  -- split the block tuples' count
  have hsplit : (kk : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * D) =
      (kk : ℝ≥0∞) * ((Nn : ℝ≥0∞) ^ tau * D) +
        (kk : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau - Nn ^ tau : ℕ) : ℝ≥0∞) * D) := by
    rw [show ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) =
        (Nn : ℝ≥0∞) ^ tau + ((Fintype.card (Bits lambda) ^ tau - Nn ^ tau : ℕ) : ℝ≥0∞) from by
      rw [← Nat.cast_pow, ← Nat.cast_add, Nat.add_sub_cancel' hNle]]
    ring
  rw [hsplit] at hcomb
  have hcancel : (Nn : ℝ≥0∞) ^ tau * A ≤
      (kk : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau - Nn ^ tau : ℕ) : ℝ≥0∞) * D) + (Nn : ℝ≥0∞) ^ tau * Bf +
        ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ * D := by
    refine ENNReal.le_of_add_le_add_left hDtop ?_
    calc (kk : ℝ≥0∞) * ((Nn : ℝ≥0∞) ^ tau * D) + (Nn : ℝ≥0∞) ^ tau * A
        = (Nn : ℝ≥0∞) ^ tau * A + (kk : ℝ≥0∞) * ((Nn : ℝ≥0∞) ^ tau * D) := add_comm _ _
      _ ≤ _ := hcomb
      _ = (kk : ℝ≥0∞) * ((Nn : ℝ≥0∞) ^ tau * D) +
          ((kk : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau - Nn ^ tau : ℕ) : ℝ≥0∞) * D) + (Nn : ℝ≥0∞) ^ tau * Bf +
            ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ * D) := by ring
  -- bound the tuples' count and the distinct mass
  refine hcancel.trans ?_
  have h2 : (kk : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau - Nn ^ tau : ℕ) : ℝ≥0∞) * D) ≤
      2 * ((Fintype.card (Bits lambda) ^ tau - Nn ^ tau : ℕ) : ℝ≥0∞) :=
    calc _ ≤ (2 : ℝ≥0∞) * (((Fintype.card (Bits lambda) ^ tau - Nn ^ tau : ℕ) : ℝ≥0∞) * 1) :=
          mul_le_mul' (by exact_mod_cast hkk) (mul_le_mul' le_rfl hD)
      _ = _ := by rw [mul_one]
  have h3 : ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ * D ≤ ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ :=
    calc _ ≤ ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ * 1 := mul_le_mul' le_rfl hD
      _ = _ := mul_one _
  calc _ ≤ 2 * ((Fintype.card (Bits lambda) ^ tau - Nn ^ tau : ℕ) : ℝ≥0∞) + (Nn : ℝ≥0∞) ^ tau * Bf +
        ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ := add_le_add (add_le_add h2 le_rfl) h3
    _ = _ := by ring

include hL2 hin hl hL hfiber hNb hw hΨ hdata in
/-- The chain divided by the scaling, with the scaling bounded uniformly
through the counted invariant. -/
theorem fixed_div (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda) :
    mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
        SigningData.inner S publicKey message salt root digest witness world Ψ g) ≤
      mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
        SigningData.inner S publicKey message salt root digest fake world Ψ g) +
      (2 * ((Fintype.card (Bits lambda) ^ tau - scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B ^ tau : ℕ) : ℝ≥0∞) +
          ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ) /
        ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau := by
  set Nn : ℕ := Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) with hNn
  have hlen : world.other.cipherHistory.length ≤ commitBudget tau kappa * B := hw.2.2
  have hcard : (keysOf world.other.cipherHistory).card ≤ commitBudget tau kappa * B := (card_keysOf_le _).trans hlen
  have hsc : scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B ≤ Nn := by
    unfold scaleAt
    exact Nat.sub_le_sub_left (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _) _
  have hsc0 : 0 < scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B := by
    unfold scaleAt; omega
  have hNn0 : (Nn : ℝ≥0∞) ^ tau ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hNntop : (Nn : ℝ≥0∞) ^ tau ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  set A := mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
    SigningData.inner S publicKey message salt root digest witness world Ψ g)
  set Bf := mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
    SigningData.inner S publicKey message salt root digest fake world Ψ g)
  set C : ℝ≥0∞ := 2 * ((Fintype.card (Bits lambda) ^ tau - Nn ^ tau : ℕ) : ℝ≥0∞) + ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ
  have hdiv : A ≤ Bf + C / (Nn : ℝ≥0∞) ^ tau := by
    rw [← ENNReal.mul_le_mul_iff_right hNn0 hNntop, mul_add, ENNReal.mul_div_cancel hNn0 hNntop]
    exact fixed_cancel S publicKey message witness fake world Ψ hL2 hin hl hL c hfiber B hw hΨ δ hdata salt root digest
  refine hdiv.trans (add_le_add le_rfl ?_)
  refine ENNReal.div_le_div ?_ ?_
  · refine add_le_add (mul_le_mul' le_rfl (Nat.cast_le.mpr (Nat.sub_le_sub_left (Nat.pow_le_pow_left hsc tau) _))) le_rfl
  · exact pow_le_pow_left' (Nat.cast_le.mpr hsc) tau

include hL2 hin hl hL hfiber hNb hw hΨ hdata in
/-- The chain at fixed draws for the inner means: the honest inner mean is
at most the fake one plus the distinct-tree failure and the uniform
slack. -/
theorem fixed_total (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda) :
    mean (posterior world.other.cipherHistory) (SigningData.inner S publicKey message salt root digest witness world Ψ) ≤
      mean (posterior world.other.cipherHistory) (SigningData.inner S publicKey message salt root digest fake world Ψ) +
      (mean (posterior world.other.cipherHistory) (fun g => 1 - distInd S.signer salt world.other root g) +
        (2 * ((Fintype.card (Bits lambda) ^ tau - scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B ^ tau : ℕ) : ℝ≥0∞) +
            ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ) /
          ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau) := by
  have h1 : mean (posterior world.other.cipherHistory) (SigningData.inner S publicKey message salt root digest witness world Ψ) ≤
      mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
        SigningData.inner S publicKey message salt root digest witness world Ψ g) +
      mean (posterior world.other.cipherHistory) (fun g => 1 - distInd S.signer salt world.other root g) := by
    rw [← mean_add]
    refine mean_le_mean _ _ _ fun g _ => ?_
    unfold distInd
    by_cases hd : Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory
    · simp [hd, indicator]
    · simp only [hd, decide_false, RandomOracleTrap.indicator_false, zero_mul, tsub_zero, zero_add]
      exact inner_le_one S publicKey message salt root digest witness world Ψ hΨ g
  have h2 : mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
      SigningData.inner S publicKey message salt root digest fake world Ψ g) ≤
      mean (posterior world.other.cipherHistory) (SigningData.inner S publicKey message salt root digest fake world Ψ) :=
    mean_le_mean _ _ _ fun g _ => mul_le_of_le_one_left (zero_le _) (distInd_le_one S.signer salt world.other root g)
  calc _ ≤ _ := h1
    _ ≤ (mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          SigningData.inner S publicKey message salt root digest fake world Ψ g) +
        (2 * ((Fintype.card (Bits lambda) ^ tau - scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B ^ tau : ℕ) : ℝ≥0∞) +
            ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ) /
          ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau) +
        mean (posterior world.other.cipherHistory) (fun g => 1 - distInd S.signer salt world.other root g) :=
        add_le_add (fixed_div S publicKey message witness fake world Ψ hL2 hin hl hL c hfiber B hNb hw hΨ δ hdata salt root digest) le_rfl
    _ ≤ _ := by
        rw [add_assoc, add_comm (_ / _) _, ← add_assoc, ← add_assoc]
        exact add_le_add (add_le_add h2 le_rfl) le_rfl

omit witness fake world Ψ hw hΨ in
include hL2 hin hl hL hfiber hfiberR hNb hdata in
/-- The off-hit closeness for the pre-call hit, with the off-hit slack. -/
theorem prunedCloseOff_of_dataClose :
    PrunedCloseOff S publicKey (hitPre S) B (εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey B δ) := by
  intro witness fake message world hw Ψ hΨ
  simp only [prunedMeanOff_eq_posterior]
  have hbad : (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
      mean (posterior world.other.cipherHistory) fun g => 1 - distInd S.signer salt world.other root g) ≤
      εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * B) :=
    mean_le_const _ _ _ fun salt _ => badTree_mean_le S salt world hL2 hin hl hL c hfiber cKey hfiberR B hw
  calc _ ≤ mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
        mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
          mean (posterior world.other.cipherHistory) (SigningData.inner S publicKey message salt root digest fake world Ψ) +
          (mean (posterior world.other.cipherHistory) (fun g => 1 - distInd S.signer salt world.other root g) +
            (2 * ((Fintype.card (Bits lambda) ^ tau - scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B ^ tau : ℕ) : ℝ≥0∞) +
                ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ) /
              ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau) :=
        mean_le_mean _ _ _ fun salt _ => mean_le_mean _ _ _ fun root _ => mean_le_mean _ _ _ fun digest _ =>
          fixed_total S publicKey message witness fake world Ψ hL2 hin hl hL c hfiber B hNb hw hΨ δ hdata salt root digest
    _ = (mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
          mean (PMF.uniformOfFintype (Spec.BAVC.Digest lambda)) fun digest =>
            mean (posterior world.other.cipherHistory) (SigningData.inner S publicKey message salt root digest fake world Ψ)) +
        ((mean (PMF.uniformOfFintype (Bits lambda)) fun salt => mean (PMF.uniformOfFintype (Bits lambda)) fun root =>
          mean (posterior world.other.cipherHistory) fun g => 1 - distInd S.signer salt world.other root g) +
          (2 * ((Fintype.card (Bits lambda) ^ tau - scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B ^ tau : ℕ) : ℝ≥0∞) +
              ((Fintype.card (Bits lambda) ^ tau : ℕ) : ℝ≥0∞) * δ) /
            ((scaleAt (lambda := lambda) (tau := tau) (kappa := kappa) c B : ℕ) : ℝ≥0∞) ^ tau) := by
        simp only [mean_add, mean_const]
    _ ≤ _ := by
        unfold εOff
        exact add_le_add le_rfl (add_le_add hbad le_rfl)

omit witness fake world Ψ hw hΨ in
include hL2 hin hl hL hfiber hfiberR hNb hdata in
/-- The pruned closeness from the data-level closeness: the hit bound for the
pre-call hit plus the off-hit slack. -/
theorem prunedClose_of_dataClose :
    PrunedClose S publicKey B (εHit (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * B) +
      εOff (lambda := lambda) (tau := tau) (kappa := kappa) c cKey B δ) :=
  prunedClose_of_split' S publicKey (hitPre S) B _ _ (badTerm_hitPre S publicKey hL2 hin hl hL c hfiber cKey hfiberR B)
    (prunedCloseOff_of_dataClose S publicKey hL2 hin hl hL c hfiber cKey hfiberR B hNb δ hdata)

end
end SDitH.Proofs.OffHitClose
