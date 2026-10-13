import SDitH.Proofs.ForgeryFinal

/-! The events' requirements for the named events. Seven of the eight
events read the attempts' signatures and bodies, the embedded worlds' inner
hash tables and the snapshot's input and inner hash table only, so they are
insensitive to the families and cipher histories and compatible with pruning
at the end; the seed-collision event reads the snapshot's family and the
branches' cipher histories, and its bound enters directly. -/

namespace SDitH.Proofs.EventRequirements

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
open GamePruneGen GamePrune RunWorld CutWorld
open Spec.IdealCipher (Entry)
open Spec.RandomOracleTrap (indicator)
open scoped Classical ENNReal
open TouchBound SimulationGapCompat ForgeryFinal PruneCompatClosure GamePruneGen GamePrune ForkPruneCompat

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
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)


omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A constant indicator is compatible with any functional dominating the
touching indicator. -/
theorem pruneCompat_const (K : List (Bits lambda)) (b : Bool)
    (T : Terminal (List Bool) (Signature (Spec.BAVC.Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) ×
      GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1)) → ℝ≥0∞)
    (hT : ∀ r, indicator (touchesG K r.2) ≤ T r) :
    PruneCompat K (fun _ => indicator b) T where
  le_one _ := by unfold indicator; split <;> simp
  touch_le := hT
  forward t world _ := by
    rw [mean_const]
    calc indicator b = mean (resampleW resample (pruneW K world)) (fun _ => indicator b) := (mean_const _ _).symm
      _ ≤ _ := mean_le_mean _ _ _ fun w _ => le_self_add
  reverse t world _ := by
    rw [mean_const, mean_const]
    exact le_self_add

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The event at the end-resampled family is its value when the event does
not read the snapshot world's family. -/
theorem rightEval_eq (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hfam : ∀ snapshot' g res, E { snapshot' with world := setFamily snapshot'.world g } res = E snapshot' res)
    (snapshot' : Snap F lambda s higherCount w widths State) (a a' : Spec.BAVC.Digest lambda) (c c') (w'') :
    rightEval snapshot' E a c c' a' w'' = indicator (E snapshot' (some (⟨a, c⟩, ⟨a', c'⟩))) := by
  unfold rightEval
  simp only [hfam]
  exact mean_const _ _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The events' requirements for an event of the two attempts reading the
snapshot only outside its world's family and history, and the attempts'
worlds only outside their families and histories. -/
theorem eventOKP_of (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hnone : ∀ snapshot', E snapshot' none = false)
    (hsnap : ∀ snapshot' g H res, E { snapshot' with world := adjust snapshot'.world g H } res = E snapshot' res)
    (hleft : ∀ snapshot' (a : Spec.BAVC.Digest lambda) t w₀ f H b₁ b₂ right,
      E snapshot' (some (⟨a, ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩, right)) =
        E snapshot' (some (⟨a, ⟨withWorld t w₀, b₁, b₂⟩⟩, right)))
    (hright : ∀ snapshot' left t w₀ f H b₁ b₂ (a' : Spec.BAVC.Digest lambda),
      E snapshot' (some (left, ⟨a', ⟨withWorld t (adjust w₀ f H), b₁, b₂⟩⟩)) =
        E snapshot' (some (left, ⟨a', ⟨withWorld t w₀, b₁, b₂⟩⟩))) :
    EventOKP E where
  none := hnone
  hist snapshot' H res := hsnap snapshot' snapshot'.world.other.family H res
  leftW := hleft
  rightW := hright
  compat K snapshot' c c' a a' :=
    pruneCompat_congr K _ _ _ _
      (fun r => (rightEval_eq E (fun sn g res => hsnap sn g sn.world.other.cipherHistory res) snapshot' a a' c c' r.2).symm)
      (fun _ => rfl) (pruneCompat_const K _ _ fun _ => le_rfl)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The mask event's requirements. -/
theorem eventOKP_maskAfter :
    EventOKP (maskAfter (F := F) (lambda := lambda) (tau := tau) (kappa := kappa) (s := s) (higherCount := higherCount) (w := w)
      (widths := widths) (State := State)) := by
  refine eventOKP_of _ (fun _ => rfl) (fun sn g H res => ?_) (fun sn a t w₀ f H b₁ b₂ right => ?_)
    (fun sn left t w₀ f H b₁ b₂ a' => ?_)
  · rfl
  · rcases right with ⟨a', ⟨tr, b₁', b₂'⟩⟩
    cases t <;> cases tr <;> rfl
  · rcases left with ⟨a, ⟨tl, b₁', b₂'⟩⟩
    cases tl <;> cases t <;> rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The non-separation event's requirements. -/
theorem eventOKP_notSeparated :
    EventOKP (fun (_ : Snap F lambda s higherCount w widths State) => notSeparated V) := by
  refine eventOKP_of _ (fun _ => rfl) (fun sn g H res => rfl) (fun sn a t w₀ f H b₁ b₂ right => ?_)
    (fun sn left t w₀ f H b₁ b₂ a' => ?_)
  · rcases right with ⟨a', ⟨tr, b₁', b₂'⟩⟩
    cases t <;> cases tr <;> rfl
  · rcases left with ⟨a, ⟨tl, b₁', b₂'⟩⟩
    cases tl <;> cases t <;> rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The slope-game event's requirements. -/
theorem eventOKP_slopeWin :
    EventOKP (fun (_ : Snap F lambda s higherCount w widths State) => slopeWin S V) := by
  refine eventOKP_of _ (fun _ => rfl) (fun sn g H res => rfl) (fun sn a t w₀ f H b₁ b₂ right => ?_)
    (fun sn left t w₀ f H b₁ b₂ a' => ?_)
  · rcases right with ⟨a', ⟨tr, b₁', b₂'⟩⟩
    cases t <;> cases tr <;> rfl
  · rcases left with ⟨a, ⟨tl, b₁', b₂'⟩⟩
    cases tl <;> cases t <;> rfl

omit [Algebra (ZMod 2) F] [NeZero tau] in
/-- The zero-challenge event's requirements. -/
theorem eventOKP_zeroChallenge (encode : (Fin tau → Fin (2 ^ kappa)) → F) :
    EventOKP (fun (_ : Snap F lambda s higherCount w widths State) => zeroChallenge V encode) := by
  refine eventOKP_of _ (fun _ => rfl) (fun sn g H res => rfl) (fun sn a t w₀ f H b₁ b₂ right => ?_)
    (fun sn left t w₀ f H b₁ b₂ a' => ?_)
  · rcases right with ⟨a', ⟨tr, b₁', b₂'⟩⟩
    cases t <;> cases tr <;> rfl
  · rcases left with ⟨a, ⟨tl, b₁', b₂'⟩⟩
    cases tl <;> cases t <;> rfl

omit [NeZero tau] in
/-- The Schwartz–Zippel event's requirements. -/
theorem eventOKP_schwartzZippel (encode : (Fin tau → Fin (2 ^ kappa)) → F) :
    EventOKP (higherCount := higherCount) (w := w) (widths := widths) (State := State) (schwartzZippel S V encode) := by
  refine eventOKP_of _ (fun _ => rfl) (fun sn g H res => ?_) (fun sn a t w₀ f H b₁ b₂ right => ?_)
    (fun sn left t w₀ f H b₁ b₂ a' => ?_)
  · rfl
  · rcases right with ⟨a', ⟨tr, b₁', b₂'⟩⟩
    cases t <;> cases tr <;> rfl
  · rcases left with ⟨a, ⟨tl, b₁', b₂'⟩⟩
    cases tl <;> cases t <;> rfl

omit [NeZero tau] in
/-- The batching event's requirements. -/
theorem eventOKP_batchingBad :
    EventOKP (higherCount := higherCount) (w := w) (widths := widths) (State := State) (batchingBad S V) := by
  refine eventOKP_of _ (fun _ => rfl) (fun sn g H res => ?_) (fun sn a t w₀ f H b₁ b₂ right => ?_)
    (fun sn left t w₀ f H b₁ b₂ a' => ?_)
  · rfl
  · rcases right with ⟨a', ⟨tr, b₁', b₂'⟩⟩
    cases t <;> cases tr <;> rfl
  · rcases left with ⟨a, ⟨tl, b₁', b₂'⟩⟩
    cases tl <;> cases t <;> rfl

omit [NeZero tau] in
/-- The solved-extraction event's requirements. -/
theorem eventOKP_rsdSolved :
    EventOKP (higherCount := higherCount) (w := w) (widths := widths) (State := State) (rsdSolved S V) := by
  refine eventOKP_of _ (fun _ => rfl) (fun sn g H res => ?_) (fun sn a t w₀ f H b₁ b₂ right => ?_)
    (fun sn left t w₀ f H b₁ b₂ a' => ?_)
  · rfl
  · rcases right with ⟨a', ⟨tr, b₁', b₂'⟩⟩
    cases t <;> cases tr <;> rfl
  · rcases left with ⟨a, ⟨tl, b₁', b₂'⟩⟩
    cases tl <;> cases t <;> rfl

/-- The simulation gap for one event, with the touching bounds instantiated,
under the final hypotheses. -/
theorem hgap_final (hlambda : 0 < lambda) (htau : 0 < tau) (fuel : Nat)
    (hSencode : S.encode = fun hidden => psi S.signer.xi (challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hhigher : 1 ≤ higherCount) (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR : ℝ≥0∞)
    (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ b, Fintype.card {r : Bits lambda // S.signer.layout.output r = b} ≤ cOut)
    (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (hequal : PrunedEqual S publicKey (3 * (fuel + 1) + 2))
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (εLeaf : ℝ≥0∞)
    (hleafR : LeafR S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (hleafC : LeafC S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (εColl : ℝ≥0∞)
    (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (hE : EventOKP E) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true +
        (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
          (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
            (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl) := by
  have h := hgap_meanP S V verifyBudget publicKey sampleWitness adversary hlambda (Nat.pos_iff_ne_zero.mp htau)
    (payload_consistent S hSencode hhigher) hsample hvc _ εR _ fuel
    (fun world hw => rowTerm_mean_le_explicit S (Nat.pos_iff_ne_zero.mp htau) world _ hw.1 (invC_game _ world hw).1
      hin hl hL c hfiber cKey hkey cOut hout _ (invC_game _ world hw).2 q hq)
    hretry hequal
    (touchR_mono S V verifyBudget publicKey sampleWitness adversary _ _ _ _
      (touchR_of S V verifyBudget publicKey sampleWitness adversary hL2 hin hl hL c hfiber cKey hkey hvc _ _ hNb hNR εLeaf hleafR)
      (εTouch_mono c cKey _ _ _ εLeaf (by omega)))
    (touchC_of S V verifyBudget publicKey sampleWitness adversary hL2 hin hl hL c hfiber cKey hkey hvc _ _ hNb hNR εLeaf hleafC)
    E hE
  refine h.trans (add_le_add le_rfl ?_)
  unfold εSimP
  exact le_self_add

/-- The composed forgery bound with the events' requirements discharged for
seven events and the seed-collision probability entering directly: the
pruned equality of the two signings, the leaf-term bounds, the retry bound,
the layout's fiber bounds and size conditions, and the seed-collision
bound. -/
theorem forgery_le_final' (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
    (hvc : verifyBudget ≤ commitBudget tau kappa) (εR : ℝ≥0∞)
    (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (cOut : Nat) (hout : ∀ b, Fintype.card {r : Bits lambda // S.signer.layout.output r = b} ≤ cOut)
    (q : Nat) (hq : commitBudget tau kappa * (3 * (fuel + 1) + 2) + beforeBudget tau kappa ≤ q)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      InvC (tau := tau) (kappa := kappa) (3 * (fuel + 1) + 2) world →
        (retryEvent S publicKey witness message world) true ≤ εR)
    (hequal : PrunedEqual S publicKey (3 * (fuel + 1) + 2))
    (hNb : c * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * (3 * (fuel + 1) + 2) + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (hL2 : 2 ≤ tau * 2 ^ kappa) (εLeaf : ℝ≥0∞)
    (hleafR : LeafR S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (hleafC : LeafC S V verifyBudget publicKey sampleWitness adversary εLeaf (3 * (fuel + 1) + 2))
    (εColl : ℝ≥0∞)
    (hcoll : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true ≤ εColl) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) maskAfter fuel) true +
            (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => notSeparated V)
            fuel) true + (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (seedCollision V) fuel)
            true + (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (fun _ => slopeWin S V)
            fuel) true + (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (fun _ => zeroChallenge V encode) fuel) true +
            (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl)) +
         ((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness)
            (schwartzZippel S V encode) fuel) true +
            (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl)) +
         (((simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) (batchingBad S V) fuel)
            true + (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl)) +
          (solverSuccess S V adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel +
            (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
            (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
              (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl))) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) :=
  forgery_le_simulated_events S V verifyBudget publicKey sampleWitness adversary
    (simulatedScheme S V verifyBudget publicKey sampleWitness) hlambda htau encode hmid hencoding hlinesEnc hencode bound hcommit
    hverify hone fuel
    (εSimP (lambda := lambda) (tau := tau) (kappa := kappa) c cKey cOut q εR
      (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * (3 * (fuel + 1) + 2))
        (4 * (3 * (fuel + 1) + 2) + 3) εLeaf) fuel + εColl)
    (hgap_final S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry hequal hNb hNR hL2 εLeaf hleafR hleafC εColl _ eventOKP_maskAfter)
    (hgap_final S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry hequal hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_notSeparated V))
    (hcoll.trans (le_add_self.trans le_add_self))
    (hgap_final S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry hequal hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_slopeWin S V))
    (hgap_final S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry hequal hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_zeroChallenge V encode))
    (hgap_final S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry hequal hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_schwartzZippel S V encode))
    (hgap_final S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry hequal hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_batchingBad S V))
    (hgap_final S V verifyBudget publicKey sampleWitness adversary hlambda htau fuel hSencode hhigher hsample hvc εR hin hl hL c
      hfiber cKey hkey cOut hout q hq hretry hequal hNb hNR hL2 εLeaf hleafR hleafC εColl _ (eventOKP_rsdSolved S V))

end
end SDitH.Proofs.EventRequirements
