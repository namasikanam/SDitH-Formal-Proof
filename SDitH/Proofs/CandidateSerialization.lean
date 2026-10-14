import SDitH.Proofs.FullLayoutFinal

/-! A candidate wire encoding for the verifier's hash chain: one bit per
coordinate in index order for vectors, and the base matrix flattened in
index order. The source leaves the byte encodings undefined, so this is a
named candidate reading, not the submission's codec. Its two injectivity
facts discharge the encoding hypotheses of the composed forgery bound, and
the bound is restated with the candidate encoding in place of them. -/

namespace SDitH.Proofs.CandidateSerialization

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

universe u
open TouchBound SimulationGapCompat ForgeryFinal PruneCompatClosure EventRequirements

open SwapClose ForgeryHide SeedCollisionBound ForgeryColl ForgeryData SlopeChainReduction SlopeTrapBound ForkWitnessedBound
open ForkUnseenBound SlopeCoverFork SharedSlopeBound

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

open OffHitClose ForgeryData LeafTermBound
open ForgerySlope ForgeryRSD NamedSimulatorTerms InstanceHardness SeedTermDischarge FullLayoutFinal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type u}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- One bit per coordinate, in index order. -/
def bitVector {n : Nat} (v : Fin n → ZMod 2) : List Bool := List.ofFn fun i => decide (v i = 1)

/-- The base matrix flattened in index order (row, then execution, then bit). -/
def bitBase {tau kappa s : Nat} (m : Fin s → Fin tau → Fin kappa → ZMod 2) : List Bool :=
  List.ofFn fun p : Fin (s * (tau * kappa)) =>
    decide (m (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm (finProdFinEquiv.symm p).2).1
      (finProdFinEquiv.symm (finProdFinEquiv.symm p).2).2 = 1)

/-- The candidate wire encoding: bit vectors in index order. -/
def candidateSerialization (tau kappa s : Nat) : Spec.ConcreteBLC.Serialization tau kappa s :=
  { vector := fun v => bitVector v
    base := bitBase }

theorem zmod2_eq_of_iff {a b : ZMod 2} (h : (a = 1) ↔ (b = 1)) : a = b := by
  revert a b; decide

theorem length_bitVector {n : Nat} (v : Fin n → ZMod 2) : (bitVector v).length = n := List.length_ofFn

/-- The bit vector determines its coordinates. -/
theorem bitVector_injective {n : Nat} : Function.Injective (bitVector (n := n)) := by
  intro v v' h
  have h' := List.ofFn_inj.mp h
  funext i
  have hi := congrFun h' i
  simp only [decide_eq_decide] at hi
  exact zmod2_eq_of_iff hi

/-- The flattened base determines the matrix. -/
theorem bitBase_injective {tau kappa s : Nat} :
    Function.Injective (bitBase (tau := tau) (kappa := kappa) (s := s)) := by
  intro m m' h
  have h' := List.ofFn_inj.mp h
  funext i e j
  have hi := congrFun h' (finProdFinEquiv (i, finProdFinEquiv (e, j)))
  simp only [Equiv.symm_apply_apply, decide_eq_decide] at hi
  exact zmod2_eq_of_iff hi

/-- The flattening of fixed-length lists is injective. -/
theorem flatten_ofFn_inj {α : Type*} {L : Nat} : ∀ {m : Nat} (f g : Fin m → List α),
    (∀ j, (f j).length = L) → (∀ j, (g j).length = L) →
    (List.ofFn f).flatten = (List.ofFn g).flatten → f = g
  | 0, f, g, _, _, _ => funext fun j => j.elim0
  | m + 1, f, g, hf, hg, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons] at h
    obtain ⟨h0, hrest⟩ := List.append_inj h ((hf 0).trans (hg 0).symm)
    have ih := flatten_ofFn_inj (fun i => f i.succ) (fun i => g i.succ) (fun i => hf _) (fun i => hg _) hrest
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact h0
    · exact congrFun ih i

/-- The candidate encoding's source tail determines the corrections. -/
theorem sourceTail_injective {tau kappa s wit rnd : Nat} :
    Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail (candidateSerialization tau kappa s) corrections) := by
  intro c c' h
  have h' := flatten_ofFn_inj (fun j => bitVector (c j)) (fun j => bitVector (c' j))
    (fun _ => length_bitVector _) (fun _ => length_bitVector _) h
  funext j
  exact bitVector_injective (congrFun h' j)

/-- The candidate encoding's lines payload determines the plain vector and the base. -/
theorem lines_injective {tau kappa s : Nat} :
    ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      (candidateSerialization tau kappa s).vector plain ++ (candidateSerialization tau kappa s).base base =
        (candidateSerialization tau kappa s).vector plain' ++ (candidateSerialization tau kappa s).base base' →
        plain = plain' ∧ base = base' := by
  intro plain plain' base base' h
  obtain ⟨h1, h2⟩ := List.append_inj h ((length_bitVector _).trans (length_bitVector _).symm)
  exact ⟨bitVector_injective h1, bitBase_injective h2⟩

/-- The composed forgery bound at the full layout and the candidate encoding. -/
theorem forgery_le_final_full_enc (εSD : ℕ → ℝ≥0∞) (hhard : InstanceHard.{u} S V verifyBudget publicKey sampleWitness εSD)
    (εMask εSep εZero εSZ εBatch : ℝ≥0∞) (hlambda : 0 < lambda) (hlayoutS : S.signer.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hlayoutV : V.layout = Spec.BAVCCipherProgram.fullLayout lambda)
    (hV : V.encoding = candidateSerialization tau kappa s) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat)
    (hSencode : S.encode = fun hidden => psi S.signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hhigher : 1 ≤ higherCount) (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR : ℝ≥0∞)
    (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
                (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (δ : ℝ≥0∞) (hdata : DataClose S publicKey (3 * (fuel + 1) + 2) δ)
    (hNb : 1 * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : 1 * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (δLeaf : ℝ≥0∞) (hhide : LeafHide S publicKey (3 * (fuel + 1) + 2) δLeaf)
            (hsim : SimulatorTermBounds5 S V verifyBudget publicKey sampleWitness adversary encode fuel εMask εSep εZero εSZ εBatch) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        ((εMask +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         (εSep + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         εCollOf lambda tau kappa 1 fuel +
         ((fuel + 1 : Nat) : ℝ≥0∞) * (εTrap tau s bound + εTrap tau s bound) +
         εWitOf lambda tau kappa fuel +
         unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
         (εZero +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         (εSZ +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
         ((εBatch + (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel)) +
          (εSD fuel +
            (εSimP' (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 1 q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) (εLeafOf (lambda := lambda) (tau := tau) (kappa := kappa) 1 (3 * (fuel + 1) + 2) δLeaf))
              (εHit (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (commitBudget tau kappa * (3 * (fuel + 1) + 2)) +
                εOff (lambda := lambda) (tau := tau) (kappa := kappa) 1 1 (3 * (fuel + 1) + 2) δ) fuel + εCollOf lambda tau kappa 1 fuel))) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_final_full S V verifyBudget publicKey sampleWitness adversary εSD hhard εMask εSep εZero εSZ εBatch hlambda
    hlayoutS hlayoutV htau encode hmid (by rw [hV]; exact sourceTail_injective) (by rw [hV]; exact lines_injective) hencode
    bound hcommit hverify hone fuel hSencode hhigher hsample hvc εR hl hL q hq hretry δ hdata hNb hNR hL2 δLeaf hhide hsim

end
end SDitH.Proofs.CandidateSerialization
