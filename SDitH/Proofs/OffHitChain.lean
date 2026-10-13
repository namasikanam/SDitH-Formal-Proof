import SDitH.Proofs.OffHitSetup

/-! The off-hit chain at fixed draws. With the hidden blocks replaced by a
tuple, the honest signing's sliced data is compared with the fake
signing's through their uniform mixtures: the honest mass at the own
blocks is bounded above through the mixture, the data-level closeness
moves to the fake mixture, and the fake mixture is bounded below relative
to the tuple probability. The chain is stated additively, with the
number of blocks less the bad targets to the number of executions as the
scaling, the distinct-tree mass and the hit mass as the slack. -/

namespace SDitH.Proofs.OffHitChain

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

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (publicKey message : List Bool) (salt root : Bits lambda) (digest : Spec.BAVC.Digest lambda)
  (witness fake : Fin (selectorCount widths * w) → ZMod 2)
  (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
  (Ψ : Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → ℝ≥0∞)

/-- The sliced data with the tuple's leaves replaced: the mixing family. -/
def Fct (wsign : Fin (selectorCount widths * w) → ZMod 2) (h : Fin tau → Fin (2 ^ kappa)) (x : Fin tau → Bits lambda)
    (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  sliced S publicKey message salt root digest wsign world Ψ h (treeWith S h (baseTree S.signer salt g root) x) g

/-- The tuple probability with the tuple's leaves replaced: the bound family. -/
def Bnd (wsign : Fin (selectorCount widths * w) → ZMod 2) (h : Fin tau → Fin (2 ^ kappa)) (x : Fin tau → Bits lambda)
    (g : Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  slicedOne S publicKey message salt root digest wsign world h (treeWith S h (baseTree S.signer salt g root) x) g

variable (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
  (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g world.other.cipherHistory)
  (hΨ : ∀ x, Ψ x ≤ 1)

include hin hl hL hL2 in
/-- The mixing family is invariant under the exchange. -/
theorem Fct_inv (wsign : Fin (selectorCount widths * w) → ZMod 2) (h : Fin tau → Fin (2 ^ kappa)) (x : Fin tau → Bits lambda)
    (e : Fin tau) (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hd : Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory)
    (hbad : ¬ Bad S.signer.layout (tau * 2 ^ kappa) S.signer.variant salt root (leaf h e)
      (node (treeExpand S.signer.layout g S.signer.variant salt) root (leaf h e / 2)) world.other.cipherHistory v' g) :
    Fct S publicKey message salt root digest world Ψ wsign h x (exchanged S.signer.layout g S.signer.variant salt root (leaf h e) v') =
      Fct S publicKey message salt root digest world Ψ wsign h x g :=
  sliced_exchanged S publicKey message salt root digest wsign world Ψ h hin hl hL hL2 x e g hd v' hbad

include hin hl hL hL2 in
theorem Bnd_inv (wsign : Fin (selectorCount widths * w) → ZMod 2) (h : Fin tau → Fin (2 ^ kappa)) (x : Fin tau → Bits lambda)
    (e : Fin tau) (v' : Bits lambda) (g : Family (Bits lambda) (Bits lambda))
    (hd : Distinct S.signer.layout g S.signer.variant salt root (tau * 2 ^ kappa) world.other.cipherHistory)
    (hbad : ¬ Bad S.signer.layout (tau * 2 ^ kappa) S.signer.variant salt root (leaf h e)
      (node (treeExpand S.signer.layout g S.signer.variant salt) root (leaf h e / 2)) world.other.cipherHistory v' g) :
    Bnd S publicKey message salt root digest world wsign h x (exchanged S.signer.layout g S.signer.variant salt root (leaf h e) v') =
      Bnd S publicKey message salt root digest world wsign h x g :=
  sliced_exchanged S publicKey message salt root digest wsign world (fun _ => 1) h hin hl hL hL2 x e g hd v' hbad

include hL2 in
/-- At the own blocks the mixing family is the sliced data at the expansion's
tree. -/
theorem Fct_blocks (wsign : Fin (selectorCount widths * w) → ZMod 2) (h : Fin tau → Fin (2 ^ kappa))
    (g : Family (Bits lambda) (Bits lambda)) :
    Fct S publicKey message salt root digest world Ψ wsign h (blocks S.signer salt root h g) g =
      sliced S publicKey message salt root digest wsign world Ψ h (baseTree S.signer salt g root) g :=
  (sliced_blocks S publicKey message salt root digest wsign world Ψ h hL2 g).symm

include hL2 hin hl hL hfiber hpos hΨ in
/-- The honest upper bound: the distinct mass of the inner mean, scaled, is
at most the sum of the mixing family's masses over the tuples. -/
theorem honest_upper :
    ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          SigningData.inner S publicKey message salt root digest witness world Ψ g) ≤
      ∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
        (fun g => distInd S.signer salt world.other root g * Fct S publicKey message salt root digest world Ψ witness h x g) := by
  calc _ = ∑ h : Fin tau → Fin (2 ^ kappa),
        ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
          mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
            Fct S publicKey message salt root digest world Ψ witness h (blocks S.signer salt root h g) g) := by
        simp only [inner_eq_sum, Fct_blocks S publicKey message salt root digest world Ψ hL2]
        rw [← Finset.mul_sum, sum_mean_mul]
    _ ≤ _ := Finset.sum_le_sum fun h _ =>
        mixture_upper S.signer salt world.other root h hL2 hin hl hL hpos c hfiber
          (Fct S publicKey message salt root digest world Ψ witness h)
          (fun x g => sliced_le_one S publicKey message salt root digest witness world Ψ hΨ h _ g)
          (fun x e v' g hd hbad => Fct_inv S publicKey message salt root digest world Ψ hL2 hin hl hL witness h x e v' g hd hbad)

include hL2 hin hl hL hfiber hpos hΨ in
/-- The fake lower bound relative to the tuple probability, summed over the
tuples. -/
theorem fake_lower :
    (∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
        (fun g => distInd S.signer salt world.other root g * Fct S publicKey message salt root digest world Ψ fake h x g)) +
      ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          SigningData.inner S publicKey message salt root digest fake world (fun _ => 1) g) ≤
    (∑ h : Fin tau → Fin (2 ^ kappa), ∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
        (fun g => distInd S.signer salt world.other root g * Bnd S publicKey message salt root digest world fake h x g)) +
      ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          SigningData.inner S publicKey message salt root digest fake world Ψ g) := by
  have hper : ∀ h : Fin tau → Fin (2 ^ kappa),
      (∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
        (fun g => distInd S.signer salt world.other root g * Fct S publicKey message salt root digest world Ψ fake h x g)) +
      ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          slicedOne S publicKey message salt root digest fake world h (baseTree S.signer salt g root) g) ≤
      (∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
        (fun g => distInd S.signer salt world.other root g * Bnd S publicKey message salt root digest world fake h x g)) +
      ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
        mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
          sliced S publicKey message salt root digest fake world Ψ h (baseTree S.signer salt g root) g) := by
    intro h
    have := mixture_lower_gen S.signer salt world.other root h hL2 hin hl hL hpos c hfiber
      (Fct S publicKey message salt root digest world Ψ fake h) (Bnd S publicKey message salt root digest world fake h)
      (fun x g => sliced_le_slicedOne S publicKey message salt root digest fake world Ψ hΨ h _ g)
      (fun x g => sliced_le_one S publicKey message salt root digest fake world (fun _ => 1) (fun _ => le_rfl) h _ g)
      (fun x e v' g hd hbad => Fct_inv S publicKey message salt root digest world Ψ hL2 hin hl hL fake h x e v' g hd hbad)
      (fun x e v' g hd hbad => Bnd_inv S publicKey message salt root digest world hL2 hin hl hL fake h x e v' g hd hbad)
    simpa only [Fct_blocks S publicKey message salt root digest world Ψ hL2, Bnd,
      ← sliced_blocks S publicKey message salt root digest fake world (fun _ => 1) _ hL2, slicedOne] using this
  calc _ = ∑ h : Fin tau → Fin (2 ^ kappa), ((∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
          (fun g => distInd S.signer salt world.other root g * Fct S publicKey message salt root digest world Ψ fake h x g)) +
        ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
          mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
            slicedOne S publicKey message salt root digest fake world h (baseTree S.signer salt g root) g)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_mean_mul]
        congr 2
        refine congrArg _ (funext fun g => ?_)
        rw [← sum_slicedOne_eq]
    _ ≤ ∑ h : Fin tau → Fin (2 ^ kappa), ((∑ x : Fin tau → Bits lambda, mean (posterior world.other.cipherHistory)
          (fun g => distInd S.signer salt world.other root g * Bnd S publicKey message salt root digest world fake h x g)) +
        ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ^ tau *
          mean (posterior world.other.cipherHistory) (fun g => distInd S.signer salt world.other root g *
            sliced S publicKey message salt root digest fake world Ψ h (baseTree S.signer salt g root) g)) :=
        Finset.sum_le_sum fun h _ => hper h
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_mean_mul]
        congr 2
        refine congrArg _ (funext fun g => ?_)
        rw [← inner_eq_sum]

end
end SDitH.Proofs.OffHitChain
