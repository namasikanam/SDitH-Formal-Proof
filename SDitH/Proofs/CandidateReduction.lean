import SDitH.Proofs.ForkExtraction

/-! The event-union skeleton of the composed reduction for the candidate
scheme. The named events of a fork result (a mask input first queried after
the fork, hidden indices not separated at some execution, a recorded seed
collision, the slope-consistency game's winning condition, a zero challenge,
the Schwartz–Zippel event of a nonzero difference polynomial vanishing at
the challenge) and the extraction event (a common slope whose extracted
lines' prover polynomial is the hashed coefficient polynomial) are explicit
Boolean events on the fork result. A winning fork without the charged
events is one of them, so the good-fork probability is at most the sum of
their probabilities; composed with the charged-event bound, the fork
experiment's success is at most that sum plus the charged-event bound.
Extraction forces the prover polynomial's constant term to vanish, which is
the input of the batching step. Each named event's probability remains to
be bounded separately. -/

namespace SDitH.Proofs.CandidateReduction

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.HashCipherEvaluation Spec.CandidateVerifier
open Spec.SlopeConsistency Spec.BLCSeedLines Spec.BLCSeedFold Spec.ConsistencyMatrix Spec.CandidateBAVC
open Spec.PIOPArithmetic (selectorCount)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open BranchAccounting (MaskAfterCut)
open CandidateForkSlope (completion)
open CandidateBAVC (induced)
open SharedSigner (expandEntries)
open PIOPExtraction (witnessLine randomnessLine)
open scoped Classical ENNReal
noncomputable section

section Generic

variable {A : Type*}

theorem bind_true_mono (p : PMF A) (f g : A → PMF Bool) (h : ∀ a ∈ p.support, f a true ≤ g a true) :
    (p.bind f) true ≤ (p.bind g) true := by
  simp only [PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (h a ha) _
  · rw [PMF.mem_support_iff, not_not] at ha
    rw [ha]
    simp

theorem map_true_mono_support (p : PMF A) (h1 h2 : A → Bool) (himp : ∀ a ∈ p.support, h1 a = true → h2 a = true) :
    (p.map h1) true ≤ (p.map h2) true := by
  rw [RandomOracleTrap.map_true_eq, RandomOracleTrap.map_true_eq]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · refine mul_le_mul_right (?_ : Spec.RandomOracleTrap.indicator (h1 a) ≤ Spec.RandomOracleTrap.indicator (h2 a)) _
    cases hb : h1 a
    · simp [Spec.RandomOracleTrap.indicator]
    · rw [himp a ha hb]
  · rw [PMF.mem_support_iff, not_not] at ha
    rw [ha]
    simp

end Generic

abbrev Snap (F : Type) (lambda s higherCount w : Nat) (widths : List Nat) (State : Type*) :=
  Snapshot (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
    (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State

abbrev Bod (F : Type) (lambda tau kappa s higherCount w : Nat) (widths : List Nat) :=
  Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount

abbrev Br (F : Type) (lambda tau kappa s higherCount w : Nat) (widths : List Nat) :=
  Branch (List Bool) (Signature (Spec.BAVC.Digest lambda) (Option (Bod F lambda tau kappa s higherCount w widths)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
    (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)

abbrev Att (F : Type) (lambda tau kappa s higherCount w : Nat) (widths : List Nat) :=
  Attempt (List Bool) (Signature (Spec.BAVC.Digest lambda) (Option (Bod F lambda tau kappa s higherCount w widths)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
    (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)

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

/-- A predicate of the two accepted attempts and their bodies, as an event of
the fork result. -/
def onAttempts (f : Att F lambda tau kappa s higherCount w widths → Att F lambda tau kappa s higherCount w widths →
    Bod F lambda tau kappa s higherCount w widths → Bod F lambda tau kappa s higherCount w widths → Bool) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool
  | none => false
  | some (l, r) =>
    match l.checked.terminal, r.checked.terminal with
    | .attempt a, .attempt b =>
      match a.signature.body, b.signature.body with
      | some bodyA, some bodyB => f a b bodyA bodyB
      | _, _ => false
    | _, _ => false

/-- A branch's mask input first queried after the fork (decision 1). -/
def maskAfter (snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a b _ _ =>
    decide (MaskAfterCut snapshot.world.other.hashTable a.world.other.hashTable ∨
      MaskAfterCut snapshot.world.other.hashTable b.world.other.hashTable)

/-- The hidden indices agree at some execution (decision 2). -/
def notSeparated :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a b bodyA bodyB =>
    decide (∃ e, V.expand a.signature.piop bodyA.2.2.1.1 e = V.expand b.signature.piop bodyB.2.2.1.1 e)

/-- A recorded seed collision with its expansions on the two branches. -/
def seedCollision (snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a b bodyA _ =>
    decide (∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (ls rs : Spec.BAVC.Seed lambda),
      Spec.BAVCBinding.IsSeedCollision
        (induced (tau := tau) (kappa := kappa) snapshot.world.other.family snapshot.world.other.hashTable V.layout V.variant)
        bodyA.1 (Spec.SeedTree.leafOffset e i) ls rs ∧
      expandEntries snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) V.layout
        V.variant bodyA.1 (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) ls ∧
      expandEntries snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) V.layout
        V.variant bodyA.1 (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) rs)

/-- The completed seed array of the first branch. -/
def fullOf (a : Att F lambda tau kappa s higherCount w widths) (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths) :
    Fin tau → Fin (2 ^ kappa) → Spec.BAVC.Seed lambda :=
  completion (V.expand a.signature.piop bodyA.2.2.1.1) bodyA.2.2.1.2 bodyB.2.2.1.2

/-- The slopes of the first branch's transcript with the completed array. -/
def slopesOf (a : Att F lambda tau kappa s higherCount w widths) (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths)
    (e : Fin tau) : Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 :=
  Spec.BLCSeedFold.slope S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1 e

/-- The slope-consistency game's winning condition at some mask. -/
def slopeWin :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a _ bodyA bodyB =>
    decide (∃ M : Spec.SlopeConsistencyGame.Mask s (selectorCount widths * w) (lambda * (widths.length - 1)), ∃ e e',
      slopesOf S V a bodyA bodyB e ≠ slopesOf S V a bodyA bodyB e' ∧
      ∀ a', masked M (slopesOf S V a bodyA bodyB e) a' = masked M (slopesOf S V a bodyA bodyB e') a')

/-- The first branch's challenge is zero. -/
def zeroChallenge (encode : (Fin tau → Fin (2 ^ kappa)) → F) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a _ bodyA _ => decide (encode (V.expand a.signature.piop bodyA.2.2.1.1) = 0)

/-- The difference between the extracted lines' prover polynomial and the hashed
coefficient polynomial. -/
def difference (snapshot : Snap F lambda s higherCount w widths State)
    (a : Att F lambda tau kappa s higherCount w widths) (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths)
    (u : Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2) : Polynomial F :=
  Spec.PIOPComposition.proverRun widths S.hsize S.signer.xi (S.expandBatching snapshot.input.payload.1).1
    (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
    (witnessLine S.signer.xi S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1 u)
    (randomnessLine S.signer.xi S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough u) -
  Spec.CoefficientCompression.coefficientPolynomial snapshot.input.payload.2

/-- A nonzero difference polynomial vanishing at the inverted challenge. -/
def schwartzZippel (encode : (Fin tau → Fin (2 ^ kappa)) → F) (snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a _ bodyA bodyB =>
    decide (∃ u, (∀ e c', slopesOf S V a bodyA bodyB e c' = u c') ∧ difference S V snapshot a bodyA bodyB u ≠ 0 ∧
      (difference S V snapshot a bodyA bodyB u).eval (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ = 0)

/-- Extraction: a common slope whose difference polynomial is zero. -/
def extracts (snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a _ bodyA bodyB =>
    decide (∃ u, (∀ e c', slopesOf S V a bodyA bodyB e c' = u c') ∧ difference S V snapshot a bodyA bodyB u = 0)

/-- The probability of an event of the fork result. -/
def eventExperiment (E : Snap F lambda s higherCount w widths State →
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (index fuel : Nat) : PMF Bool :=
  (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).bind
    fun c => match c with
    | .ended _ => PMF.pure false
    | .saved snapshot => (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
        snapshot).map (E snapshot)

theorem eventExperiment_or_le (E₁ E₂) (index fuel : Nat) :
    (eventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot result =>
        E₁ snapshot result || E₂ snapshot result) index fuel) true ≤
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary E₁ index fuel) true +
        (eventExperiment S V verifyBudget publicKey sampleWitness adversary E₂ index fuel) true := by
  unfold eventExperiment
  refine ForkGoodOutcome.bind_true_le_add _ _ _ _ fun c _ => ?_
  cases c with
  | ended terminal => simp
  | saved snapshot => exact ForkEventUnion.map_or_le _ _ _

/-- A winning fork without the charged events is one of the named events or
an extraction. -/
theorem good_implies_events (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      adversary snapshot).support)
    (hgood : (forkWins snapshot.input result && !CandidateForkOutcome.forkBad (tau := tau) snapshot result) = true) :
    (maskAfter snapshot result || notSeparated V result || seedCollision V snapshot result || slopeWin S V result ||
      zeroChallenge V encode result || schwartzZippel S V encode snapshot result || extracts S V snapshot result) = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hgood
  obtain ⟨left, right, a, b, bodyA, bodyB, hres, ha, hb, hbodyA, hbodyB, _, hext⟩ :=
    ForkExtraction.fork_extracts S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding
      hlinesEnc hencode index fuel c hc snapshot hsnap result hr hgood.1 hgood.2
  subst hres
  simp only [maskAfter, notSeparated, seedCollision, slopeWin, zeroChallenge, schwartzZippel, extracts, onAttempts, ha, hb,
    hbodyA, hbodyB, Bool.or_eq_true, decide_eq_true_eq]
  by_cases hmask : MaskAfterCut snapshot.world.other.hashTable a.world.other.hashTable ∨
      MaskAfterCut snapshot.world.other.hashTable b.world.other.hashTable
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hmask)))))
  by_cases hsep : ∃ e, V.expand a.signature.piop bodyA.2.2.1.1 e = V.expand b.signature.piop bodyB.2.2.1.1 e
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hsep)))))
  obtain ⟨_, _, _, pm, _, _, _, _, _, _, hM⟩ := hext (fun h => hmask (Or.inl h)) (fun h => hmask (Or.inr h))
    (fun e h => hsep ⟨e, h⟩)
  rcases hM with hcol | hwin | ⟨u, hu, hvan⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hcol))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨pm.2, hwin⟩)))
  by_cases hz : encode (V.expand a.signature.piop bodyA.2.2.1.1) = 0
  · exact Or.inl (Or.inl (Or.inr hz))
  by_cases hdiff : difference S V snapshot a bodyA bodyB u = 0
  · exact Or.inr ⟨u, hu, hdiff⟩
  · exact Or.inl (Or.inr ⟨u, hu, hdiff, hvan hz⟩)

/-- The good-fork probability is at most the sum of the named events'
probabilities and the extraction probability. -/
theorem good_fork_le_events (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (index fuel : Nat) :
    (CandidateForkOutcome.goodForkExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true ≤
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => notSeparated V) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => slopeWin S V) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (schwartzZippel S V encode) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (extracts S V) index fuel) true := by
  have hmono : (CandidateForkOutcome.goodForkExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true ≤
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot result =>
        maskAfter snapshot result || notSeparated V result || seedCollision V snapshot result || slopeWin S V result ||
          zeroChallenge V encode result || schwartzZippel S V encode snapshot result || extracts S V snapshot result)
        index fuel) true := by
    unfold CandidateForkOutcome.goodForkExperiment eventExperiment
    refine bind_true_mono _ _ _ fun c hc => ?_
    cases c with
    | ended terminal => exact le_rfl
    | saved snapshot =>
      refine map_true_mono_support _ _ _ fun result hr hgood => ?_
      exact good_implies_events S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding
        hlinesEnc hencode index fuel _ hc snapshot rfl result hr hgood
  refine hmono.trans ?_
  refine (eventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ index fuel).trans ?_
  refine add_le_add_left ?_ _
  refine (eventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ index fuel).trans ?_
  refine add_le_add_left ?_ _
  refine (eventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ index fuel).trans ?_
  refine add_le_add_left ?_ _
  refine (eventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ index fuel).trans ?_
  refine add_le_add_left ?_ _
  refine (eventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ index fuel).trans ?_
  refine add_le_add_left ?_ _
  exact eventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ index fuel

/-- The fork experiment's success is at most the named events, the extraction
probability and the charged-event bound. -/
theorem fork_le_events (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (index fuel : Nat) :
    (forkExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel) true ≤
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => notSeparated V) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => slopeWin S V) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (schwartzZippel S V encode) index fuel) true +
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (extracts S V) index fuel) true +
      (fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) +
      fuel * (epsilonC lambda bound (fuel * (bound + bound)) + epsilonC lambda bound (fuel * (bound + bound))) +
      (2 : ℝ≥0∞) * (fuel * (bound * digestInv lambda + bound * digestInv lambda) +
        fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))))) :=
  (CandidateForkOutcome.forkExperiment_split S V verifyBudget publicKey sampleWitness adversary index fuel).trans
    (add_le_add (good_fork_le_events S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding
      hlinesEnc hencode index fuel)
      (CandidateForkOutcome.forkBad_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit hverify hone
        index fuel))

omit [NeZero tau] in
/-- Extraction forces the extracted lines' prover polynomial to be the hashed
coefficient polynomial, whose constant term is zero: the input of the batching
step. -/
theorem extracts_constant_zero (snapshot : Snap F lambda s higherCount w widths State) (result)
    (h : extracts S V snapshot result = true) :
    ∃ left right a b bodyA bodyB u, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.signature.body = some bodyA ∧ b.signature.body = some bodyB ∧
      (∀ e c', slopesOf S V a bodyA bodyB e c' = u c') ∧
      Spec.PIOPComposition.proverRun widths S.hsize S.signer.xi (S.expandBatching snapshot.input.payload.1).1
        (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
        (witnessLine S.signer.xi S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1 u)
        (randomnessLine S.signer.xi S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough u) =
        Spec.CoefficientCompression.coefficientPolynomial snapshot.input.payload.2 ∧
      (Spec.PIOPComposition.proverRun widths S.hsize S.signer.xi (S.expandBatching snapshot.input.payload.1).1
        (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
        (witnessLine S.signer.xi S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1 u)
        (randomnessLine S.signer.xi S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough u)).eval 0
        = 0 := by
  rcases result with _ | ⟨l, r⟩
  · exact absurd h (by simp [extracts, onAttempts])
  unfold extracts onAttempts at h
  dsimp only at h
  split at h
  · rename_i a b ha hb
    split at h
    · rename_i bodyA bodyB hbodyA hbodyB
      obtain ⟨u, hu, hdiff⟩ := decide_eq_true_eq.mp h
      have heq := sub_eq_zero.mp hdiff
      refine ⟨l, r, a, b, bodyA, bodyB, u, rfl, ha, hb, hbodyA, hbodyB, hu, heq, ?_⟩
      rw [heq]
      exact CoefficientCompression.coefficientPolynomial_zero _
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end
end SDitH.Proofs.CandidateReduction
