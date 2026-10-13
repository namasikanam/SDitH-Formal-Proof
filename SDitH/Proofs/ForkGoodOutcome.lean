import SDitH.Proofs.ForkEventUnion

/-! The fork experiment split by its charged events. A successful fork
without the charged events yields, at every execution where the two
hidden indices differ, the fork-to-slope outcome on the snapshot's
table, unless a branch's mask input was first queried after the fork.
The fork experiment's success is at most the success without the charged
events plus their bound. This is the probabilistic form of the fork's
outcome, with the mask event the only uncharged term. -/

namespace SDitH.Proofs.ForkGoodOutcome

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrap
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateVerifier Spec.HashCipherEvaluation Spec.SlopeConsistency
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open GameEventBound (terminalBad)
open SharedTargetBound (targetEvent digestInv)
open SharedMentionBound (mentionEvent epsilonM)
open SharedCollisionBound (collisionEvent epsilonC)
open ForkEventUnion (branchBad forkBad forkBadExperiment)
open ForkOutcome (BranchEvent SlopeOutcome)
open BranchAccounting (MaskAfterCut)
open scoped Classical ENNReal
noncomputable section

section Generic

variable {A : Type*}

theorem bind_true_le_add (p : PMF A) (f g h : A → PMF Bool)
    (hfgh : ∀ a ∈ p.support, f a true ≤ g a true + h a true) :
    (p.bind f) true ≤ (p.bind g) true + (p.bind h) true := by
  simp only [PMF.bind_apply]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [← mul_add]
    exact mul_le_mul_right (hfgh a ha) _
  · simp only [PMF.mem_support_iff, not_not] at ha
    simp [ha]

theorem map_split_le (p : PMF A) (w b : A → Bool) :
    (p.map w) true ≤ (p.map (fun x => w x && !b x)) true + (p.map b) true := by
  refine (ForkCutRun.map_true_mono _ _ (fun x => (w x && !b x) || b x) ?_).trans (ForkEventUnion.map_or_le _ _ _)
  intro x hx
  cases hb : b x <;> simp [hx, hb]

end Generic

section Shared

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The fork experiment's success without the charged events. -/
def goodForkExperiment (index fuel : Nat) : PMF Bool :=
  (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).bind fun c =>
    match c with
    | .ended _ => PMF.pure false
    | .saved snapshot => (forkAt (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
        fun result => forkWins snapshot.input result && !forkBad (tau := tau) snapshot result

/-- Success is at most success without the charged events plus the charged events. -/
theorem forkExperiment_split (index fuel : Nat) :
    (forkExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel) true ≤
      (goodForkExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true +
        (forkBadExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true := by
  unfold forkExperiment goodForkExperiment forkBadExperiment
  refine bind_true_le_add _ _ _ _ fun c _ => ?_
  cases c with
  | ended terminal =>
    simp only [forkAtCut, PMF.pure_apply]
    exact (RandomOracleTrap.ite_le_indicator false).trans (by rw [RandomOracleTrap.indicator_false]; exact zero_le _)
  | saved snapshot =>
    simp only [forkAtCut]
    exact map_split_le _ _ _

/-- A successful fork without the charged events: at every execution where
the hidden indices differ, the slope outcome on the snapshot's table, or a
branch's mask input first queried after the fork. -/
theorem fork_good_outcome (hlambda : 0 < lambda) (htau : 0 < tau)
    (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (randomCount : Nat)
    (enough : s + (selectorCount widths * w + lambda * (widths.length - 1)) ≤ 8 * randomCount)
    (hmid : V.middle = candidateMiddle xi p V.nodes encode randomCount enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).support)
    (hw : forkWins snapshot.input result = true) (hgood : forkBad (tau := tau) snapshot result = false) :
    ∃ left right a b bodyA bodyB recA recB, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.signature.body = some bodyA ∧ b.signature.body = some bodyB ∧ a.target ≠ b.target ∧
      Evaluates snapshot.world.other.family a.world.other.hashTable a.world.other.cipherHistory
        (verifyProgram V bodyA.1 bodyA.2.1 a.signature.piop bodyA.2.2.1) (Except.ok recA) ∧
      Evaluates snapshot.world.other.family b.world.other.hashTable b.world.other.cipherHistory
        (verifyProgram V bodyB.1 bodyB.2.1 b.signature.piop bodyB.2.2.1) (Except.ok recB) ∧
      recA.lines = snapshot.input.payload.1 ∧ recB.lines = snapshot.input.payload.1 ∧
      ∀ e : Fin tau, V.expand a.signature.piop bodyA.2.2.1.1 e ≠ V.expand b.signature.piop bodyB.2.2.1.1 e →
        SlopeOutcome p randomCount enough V snapshot.world.other.family snapshot.world.other.hashTable
            (a.world.other.cipherHistory ++ b.world.other.cipherHistory) bodyA.1 bodyB.1 bodyA.2.1 bodyB.2.1 e ∨
          MaskAfterCut snapshot.world.other.hashTable a.world.other.hashTable ∨
          MaskAfterCut snapshot.world.other.hashTable b.world.other.hashTable := by
  obtain ⟨left, right, a, b, bodyA, bodyB, recA, recB, hres, ha, hb, hbodyA, hbodyB, hne, hevalA, hevalB, hlinesA,
    hlinesB, houtcome⟩ := ForkOutcome.fork_outcome hlambda htau S V xi p encode randomCount enough hmid hencoding
    hlinesEnc verifyBudget publicKey sampleWitness adversary index fuel c hc snapshot hsnap result hr hw
  have hwell := ForkEventUnion.snapshot_wellFormed S V verifyBudget publicKey sampleWitness adversary index fuel c hc
    snapshot hsnap
  -- Read the charged events from the good hypothesis.
  rw [hres] at hgood
  simp only [forkBad, ha, hb, terminalBad, Bool.or_eq_false_iff] at hgood
  obtain ⟨⟨hmention, hcollision⟩, hbadA, hbadB⟩ := hgood
  simp only [branchBad, Bool.or_eq_false_iff] at hbadA hbadB
  have hfree : DigestCollisionFree snapshot.world.other.hashTable :=
    SharedCollisionBound.collisionFree_of_not_event _ hwell hcollision
  refine ⟨left, right, a, b, bodyA, bodyB, recA, recB, hres, ha, hb, hbodyA, hbodyB, hne, hevalA, hevalB, hlinesA,
    hlinesB, fun e hdiff => ?_⟩
  rcases houtcome e hdiff with hslope | hevA | hevB | hcol
  · exact Or.inl hslope
  · rcases hevA with ht | hm | hmask
    · exact absurd ht (by simp [targetEvent] at hbadA; simp [hbadA.1])
    · exact absurd hm (by simp [mentionEvent] at hbadA; simp [hbadA.2])
    · exact Or.inr (Or.inl hmask)
  · rcases hevB with ht | hm | hmask
    · exact absurd ht (by simp [targetEvent] at hbadB; simp [hbadB.1])
    · exact absurd hm (by simp [mentionEvent] at hbadB; simp [hbadB.2])
    · exact Or.inr (Or.inr hmask)
  · exact absurd hfree hcol

/-- The fork experiment's success is at most its success without the
charged events plus the charged-event bound. -/
theorem forkExperiment_bound (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound)
    (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (index fuel : Nat) :
    (forkExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel) true ≤
      (goodForkExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true +
      (fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) +
      fuel * (epsilonC lambda bound (fuel * (bound + bound)) + epsilonC lambda bound (fuel * (bound + bound))) +
      (2 : ℝ≥0∞) * (fuel * (bound * digestInv lambda + bound * digestInv lambda) +
        fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))))) :=
  (forkExperiment_split S V verifyBudget publicKey sampleWitness adversary index fuel).trans
    (add_le_add_right (ForkEventUnion.forkBad_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit
      hverify hone index fuel) _)

end Shared

end
end SDitH.Proofs.ForkGoodOutcome
