import SDitH.Proofs.CandidateGameBounds
import SDitH.Proofs.CandidateBranch
import SDitH.Proofs.ForkGoodOutcome

/-! The fork outcomes for the candidate scheme: attempt provenance from the
candidate verification service, the deterministic outcome of a successful
fork (uniform slope data, a branch event, or a collision), the charged
events and their bound, and the good-fork outcome (uniform slope data or
a mask event) with the success split. These mirror the literal scheme's
statements with the candidate reconstruction. -/

namespace SDitH.Proofs.CandidateForkOutcome

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.CandidateVerifier Spec.SlopeConsistency Spec.RandomOracleTrap
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open GameEventBound (terminalBad)
open CutEventBound (cutBad)
open SharedGameInvariant (WellFormed CutAt)
open SharedTargetBound (targetEvent digestInv)
open SharedMentionBound (mentionEvent epsilonM)
open SharedCollisionBound (collisionEvent epsilonC)
open ForkOutcome (BranchEvent)
open BranchAccounting (MaskAfterCut)
open CandidateBranch (UniformSlope)
open scoped Classical ENNReal
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- A candidate verification service call producing an input is an executed
candidate verification evaluating on the output world. -/
theorem attempt_verification (pk message : List Bool)
    (signature : Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (world world' : World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
    (h : (some input, world') ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification
      pk message signature world).support) :
    ∃ (body : Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
      (recovered : Spec.SignatureComposition.Recomputed F lambda (selectorCount widths * w) (lambda * (widths.length - 1))),
      signature.body = some body ∧
      Evaluates world.other.family world'.other.hashTable world'.other.cipherHistory
        (Spec.CandidateScheme.verifyProgram V body.1 body.2.1 signature.piop body.2.2.1) (Except.ok recovered) ∧
      input.payload.1 = recovered.lines ∧
      input.payload.2 = (Spec.SignatureComposition.verificationInput widths S.hdegree S.hsize S.signer.xi S.expandBatching
        S.H' S.y pk message ⟨body.1, signature.piop, body.2.1, (body.2.2.1.1, ⟨[], fun e => body.2.2.1.2.hiddenCommitments e⟩),
          body.2.2.2⟩ recovered).coefficients ∧
      world'.other.family = world.other.family := by
  obtain ⟨r, hr, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  have hr1 : r.1.map (fun payload => (⟨pk, message, payload⟩ : HashInput (List Bool) (List Bool) (Payload F lambda higherCount))) =
      some input := congrArg Prod.fst hres
  have hr2 : world'.other = r.2 := by
    have := congrArg Prod.snd hres
    simp only at this
    rw [← this]
  change r ∈ (Spec.CandidateScheme.prepareVerification S V verifyBudget pk message signature world.other).support at hr
  unfold Spec.CandidateScheme.prepareVerification at hr
  rcases hbody : signature.body with _ | body
  · rw [hbody] at hr
    simp only [PMF.mem_support_pure_iff] at hr
    subst hr
    simp at hr1
  · rw [hbody] at hr
    obtain ⟨run, hrun, hrr⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst hrr
    simp only at hr1 hr2
    obtain ⟨out, hout, hout'⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
    have hforget : Spec.HashCipherTrace.forget out ∈
        (Spec.HashCipher.runFixed procedure world.other.family verifyBudget
          (Spec.CandidateScheme.verifyProgram V body.1 body.2.1 signature.piop body.2.2.1) world.other.hashTable
          world.other.hashHistory world.other.cipherHistory).support := by
      rw [← HashCipherTrace.runFixed_forget]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨out, hout, rfl⟩
    subst hout'
    simp only at hr1 hr2
    cases hstate : out.state with
    | done v =>
      cases v with
      | ok recovered =>
        rw [hstate] at hr1
        simp only [Option.map_some, Option.some.injEq] at hr1
        refine ⟨body, recovered, rfl, ?_, ?_, ?_, ?_⟩
        · rw [hr2]
          exact ForkOutcome.run_done_evaluates world.other.family _ verifyBudget _ _ _ _ hforget (Except.ok recovered) hstate
        · rw [← hr1]
          rfl
        · rw [← hr1]
        · rw [hr2]
      | error _ =>
        rw [hstate] at hr1
        simp at hr1
    | hash _ _ =>
      rw [hstate] at hr1
      simp at hr1
    | cipher _ _ =>
      rw [hstate] at hr1
      simp at hr1

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The deterministic outcome of a successful candidate fork. -/
theorem fork_outcome (hlambda : 0 < lambda) (htau : 0 < tau)
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
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      adversary snapshot).support)
    (hw : forkWins snapshot.input result = true) :
    ∃ left right a b bodyA bodyB recA recB, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.signature.body = some bodyA ∧ b.signature.body = some bodyB ∧ a.target ≠ b.target ∧
      Evaluates snapshot.world.other.family a.world.other.hashTable a.world.other.cipherHistory
        (Spec.CandidateScheme.verifyProgram V bodyA.1 bodyA.2.1 a.signature.piop bodyA.2.2.1) (Except.ok recA) ∧
      Evaluates snapshot.world.other.family b.world.other.hashTable b.world.other.cipherHistory
        (Spec.CandidateScheme.verifyProgram V bodyB.1 bodyB.2.1 b.signature.piop bodyB.2.2.1) (Except.ok recB) ∧
      recA.lines = snapshot.input.payload.1 ∧ recB.lines = snapshot.input.payload.1 ∧
      snapshot.input.payload.2 = (Spec.SignatureComposition.verificationInput widths S.hdegree S.hsize S.signer.xi
        S.expandBatching S.H' S.y snapshot.publicKey a.message ⟨bodyA.1, a.signature.piop, bodyA.2.1,
          (bodyA.2.2.1.1, ⟨[], fun e => bodyA.2.2.1.2.hiddenCommitments e⟩), bodyA.2.2.2⟩ recA).coefficients ∧
      (UniformSlope p randomCount enough V snapshot.world.other.family snapshot.world.other.hashTable
          (a.world.other.cipherHistory ++ b.world.other.cipherHistory) bodyA.1 bodyB.1 bodyA.2.1 bodyB.2.1
          a.signature.piop b.signature.piop bodyA.2.2.1 bodyB.2.2.1 ∨
        BranchEvent (tau := tau) snapshot.world.other.hashTable snapshot.input.payload.1 a.world.other ∨
        BranchEvent (tau := tau) snapshot.world.other.hashTable snapshot.input.payload.1 b.world.other ∨
        ¬ DigestCollisionFree snapshot.world.other.hashTable) := by
  obtain ⟨left, right, a, b, hres, ha, hb, _, _, hai, hbi, _, _, hne⟩ :=
    SignatureReplayConsistency.successful_fork_attempts _ adversary snapshot result hr hw
  obtain ⟨_, hleftW, hrightW⟩ := CandidateGameBounds.fork_cutAt S V verifyBudget publicKey sampleWitness adversary
    index fuel c hc snapshot hsnap result hr left right hres
  obtain ⟨haW, haC⟩ := hleftW a ha
  obtain ⟨hbW, hbC⟩ := hrightW b hb
  have hpF := CandidateGameBounds.candidate_preserves S V verifyBudget publicKey sampleWitness
    (fun world => world.family = snapshot.world.other.family)
    (fun budget program world result hr hQ => (ForkOutcome.runProgram_family budget program world result hr).trans hQ)
  obtain ⟨hfamA, hfamB⟩ := SharedGameInvariant.fork_preserves _ _ hpF adversary snapshot rfl result hr left right hres
  have hbranch : ∀ branch, branch ∈ (freshBranch (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      adversary snapshot).support →
      ∀ att, branch.checked.terminal = .attempt att → att.world.other.family = snapshot.world.other.family →
      ∃ body recovered, att.signature.body = some body ∧
        Evaluates snapshot.world.other.family att.world.other.hashTable att.world.other.cipherHistory
          (Spec.CandidateScheme.verifyProgram V body.1 body.2.1 att.signature.piop body.2.2.1) (Except.ok recovered) ∧
        att.input.payload.1 = recovered.lines ∧
        att.input.payload.2 = (Spec.SignatureComposition.verificationInput widths S.hdegree S.hsize S.signer.xi
          S.expandBatching S.H' S.y snapshot.publicKey att.message ⟨body.1, att.signature.piop, body.2.1,
            (body.2.2.1.1, ⟨[], fun e => body.2.2.1.2.hiddenCommitments e⟩), body.2.2.2⟩ recovered).coefficients := by
    intro branch hbr att hatt hfam
    obtain ⟨wv, hwv⟩ := ForkOutcome.branch_attempt_source _ adversary snapshot branch hbr att hatt
    obtain ⟨body, recovered, hbody, heval, hlines, hcoeffs, hfam'⟩ :=
      attempt_verification S V verifyBudget publicKey sampleWitness _ _ _ wv att.world att.input hwv
    refine ⟨body, recovered, hbody, ?_, hlines, hcoeffs⟩
    rw [← hfam, hfam']
    exact heval
  cases he : snapshot.world.hashTable snapshot.input with
  | some _ =>
    simp only [forkAt, he, PMF.mem_support_pure_iff] at hr
    subst hr
    cases hres
  | none =>
    rw [forkAt, he] at hr
    obtain ⟨l, hl, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    obtain ⟨rr, hrr, hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
    rw [← hpair] at hres
    cases hres
    obtain ⟨bodyA, recA, hbodyA, hevalA, hlinesA, hcoeffsA⟩ := hbranch _ hl a ha (hfamA a ha)
    obtain ⟨bodyB, recB, hbodyB, hevalB, hlinesB, _⟩ := hbranch _ hrr b hb (hfamB b hb)
    refine ⟨_, _, a, b, bodyA, bodyB, recA, recB, hpair.symm, ha, hb, hbodyA, hbodyB, hne, hevalA, hevalB,
      by rw [← hlinesA, hai], by rw [← hlinesB, hbi], by rw [← hcoeffsA, hai], ?_⟩
    by_cases hfree : DigestCollisionFree snapshot.world.other.hashTable
    swap
    · exact Or.inr (Or.inr (Or.inr hfree))
    have hA := CandidateBranch.branch_visited_or_event hlambda htau xi p encode randomCount enough V hmid bodyA.1 bodyA.2.1
      a.signature.piop bodyA.2.2.1 snapshot.world.other.family a.world.other.hashTable snapshot.world.other.hashTable
      a.world.other.cipherHistory a.world.other.trace haW.2.1 haW.2.2.1 haW.1 haC.1 haC.2 recA hevalA
      snapshot.input.payload.1 (by rw [← hlinesA, hai])
    have hB := CandidateBranch.branch_visited_or_event hlambda htau xi p encode randomCount enough V hmid bodyB.1 bodyB.2.1
      b.signature.piop bodyB.2.2.1 snapshot.world.other.family b.world.other.hashTable snapshot.world.other.hashTable
      b.world.other.cipherHistory b.world.other.trace hbW.2.1 hbW.2.2.1 hbW.1 hbC.1 hbC.2 recB hevalB
      snapshot.input.payload.1 (by rw [← hlinesB, hbi])
    rcases hA with hinA | hevA
    swap
    · exact Or.inr (Or.inl hevA)
    rcases hB with hinB | hevB
    swap
    · exact Or.inr (Or.inr (Or.inl hevB))
    left
    exact CandidateBranch.fork_masked_slope_prefix xi p encode randomCount enough V hmid hencoding hlinesEnc
      bodyA.1 bodyB.1 bodyA.2.1 bodyB.2.1 a.signature.piop b.signature.piop bodyA.2.2.1 bodyB.2.2.1
      snapshot.world.other.family snapshot.world.other.hashTable a.world.other.hashTable b.world.other.hashTable
      haC.2 hbC.2 a.world.other.cipherHistory b.world.other.cipherHistory recA recB hevalA hevalB hinA hinB
      (by rw [← hlinesA, ← hlinesB, hai, hbi]) hfree

section Events

/-- The charged events of a candidate fork at a snapshot. -/
def forkBad (snapshot : Snapshot (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State)
    (result : Option (Branch (List Bool)
        (Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
        (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) ×
      Branch (List Bool)
        (Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
        (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda))) : Bool :=
  (mentionEvent tau snapshot.world.other || collisionEvent snapshot.world.other) ||
    match result with
    | none => false
    | some (l, r) => terminalBad (ForkEventUnion.branchBad (tau := tau) snapshot) l.checked.terminal ||
        terminalBad (ForkEventUnion.branchBad (tau := tau) snapshot) r.checked.terminal

def forkBadExperiment (index fuel : Nat) : PMF Bool :=
  (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).bind
    fun c => match c with
    | .ended _ => PMF.pure false
    | .saved snapshot => (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
        snapshot).map (forkBad (tau := tau) snapshot)

def goodForkExperiment (index fuel : Nat) : PMF Bool :=
  (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).bind
    fun c => match c with
    | .ended _ => PMF.pure false
    | .saved snapshot => (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
        snapshot).map fun result => forkWins snapshot.input result && !forkBad (tau := tau) snapshot result

variable (bound : Nat)

/-- One fresh branch's charged event, at a well-formed snapshot without the prefix mention event. -/
theorem branch_bad_bound (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (fuel : Nat)
    (snapshot : Snapshot (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State)
    (hw : WellFormed snapshot.world.other) (hrem : snapshot.remaining ≤ fuel)
    (hL : snapshot.world.other.trace.length + snapshot.remaining * (bound + bound) ≤ fuel * (bound + bound))
    (hmention : mentionEvent tau snapshot.world.other = false) :
    ((freshBranch (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
      (fun branch => terminalBad (ForkEventUnion.branchBad (tau := tau) snapshot) branch.checked.terminal)) true ≤
      fuel * (bound * digestInv lambda + bound * digestInv lambda) +
        fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) := by
  have hsplit : (fun branch : Branch (List Bool)
        (Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
        (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) =>
      terminalBad (ForkEventUnion.branchBad (tau := tau) snapshot) branch.checked.terminal) =
      fun branch => terminalBad (targetEvent snapshot.world.other.hashTable snapshot.input.payload.1) branch.checked.terminal ||
        terminalBad (mentionEvent tau) branch.checked.terminal := by
    funext branch
    generalize branch.checked.terminal = t
    cases t <;> rfl
  rw [hsplit]
  refine (ForkEventUnion.map_or_le _ _ _).trans (add_le_add ?_ ?_)
  · have h := GameEventBoundLen.branch_event_bound_len _ _ _ _ _
      (CandidateGameBounds.target_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone
        snapshot.world.other.hashTable snapshot.input.payload.1)
      (fun _ _ _ => le_rfl) adversary snapshot (fuel * (bound + bound)) hL
    rw [SharedTargetBound.targetEvent_wellFormed _ hw, RandomOracleTrap.indicator_false, zero_add] at h
    exact h.trans (mul_le_mul_left (Nat.cast_le.mpr hrem) _)
  · have h := GameEventBoundLen.branch_event_bound_len _ _ _ _ _
      (CandidateGameBounds.mention_service_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone)
      (SharedMentionBound.epsilonM_mono lambda tau bound) adversary snapshot (fuel * (bound + bound)) hL
    rw [hmention, RandomOracleTrap.indicator_false, zero_add] at h
    exact h.trans (mul_le_mul_left (Nat.cast_le.mpr hrem) _)

/-- The charged events of the candidate fork experiment. -/
theorem forkBad_bound (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (index fuel : Nat) :
    (forkBadExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true ≤
      fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) +
      fuel * (epsilonC lambda bound (fuel * (bound + bound)) + epsilonC lambda bound (fuel * (bound + bound))) +
      (2 : ℝ≥0∞) * (fuel * (bound * digestInv lambda + bound * digestInv lambda) +
        fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound)))) := by
  set B := fuel * (bound * digestInv lambda + bound * digestInv lambda) +
    fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) with hB
  have hbind : (forkBadExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true ≤
      ((cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
        (cutBad (fun world => mentionEvent tau world || collisionEvent world))) true + (B + B) := by
    unfold forkBadExperiment
    have h := RandomOracleTrap.bind_map_indicator_le
      (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel)
      (fun c => match c with
        | .ended _ => PMF.pure false
        | .saved snapshot => (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
            snapshot).map (forkBad (tau := tau) snapshot))
      id (cutBad (fun world => mentionEvent tau world || collisionEvent world)) (B + B) ?_
    · simpa only [PMF.map_id] using h
    intro c hc
    cases c with
    | ended terminal =>
      simp only [PMF.pure_map, PMF.pure_apply, id]
      exact (RandomOracleTrap.ite_le_indicator false).trans (by rw [RandomOracleTrap.indicator_false]; exact zero_le _)
    | saved snapshot =>
      simp only [PMF.map_id, cutBad]
      have hw := CandidateGameBounds.snapshot_wellFormed S V verifyBudget publicKey sampleWitness adversary index fuel _ hc
        snapshot rfl
      have hrem : snapshot.remaining ≤ fuel := by
        obtain ⟨generated, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
        obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
        exact ForkEventUnion.cut_remaining_le _ adversary index fuel _ _ state _ _ _ hcut snapshot rfl
      have hL := CandidateGameBounds.prefix_size S V verifyBudget publicKey sampleWitness adversary bound hcommit hverify
        hone index fuel _ hc snapshot rfl
      cases hpre : (mentionEvent tau snapshot.world.other || collisionEvent snapshot.world.other) with
      | true =>
        simp only [RandomOracleTrap.indicator_true]
        exact (PMF.coe_le_one _ _).trans le_self_add
      | false =>
        simp only [RandomOracleTrap.indicator_false, zero_add]
        have hmention : mentionEvent tau snapshot.world.other = false := by
          cases h : mentionEvent tau snapshot.world.other
          · rfl
          · rw [h] at hpre; simp at hpre
        have hfork : (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
            (forkBad (tau := tau) snapshot) =
            (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
            (fun result => match result with
              | none => false
              | some (l, r) => terminalBad (ForkEventUnion.branchBad (tau := tau) snapshot) l.checked.terminal ||
                  terminalBad (ForkEventUnion.branchBad (tau := tau) snapshot) r.checked.terminal) := by
          congr 1
          funext result
          simp only [forkBad, hpre, Bool.false_or]
        rw [hfork]
        cases he : snapshot.world.hashTable snapshot.input with
        | some _ =>
          simp only [forkAt, he, PMF.pure_map, PMF.pure_apply]
          exact (RandomOracleTrap.ite_le_indicator _).trans (by simp [indicator])
        | none =>
          rw [forkAt, he]
          refine (RandomOracleTrap.bind_map_indicator_le
            (freshBranch (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary snapshot) _ _
            (fun l => terminalBad (ForkEventUnion.branchBad (tau := tau) snapshot) l.checked.terminal) B ?_).trans ?_
          · intro l _
            rw [PMF.map_comp]
            refine (ForkEventUnion.map_const_or_le _ _ _).trans (add_le_add_right ?_ _)
            exact branch_bad_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit hverify hone fuel
              snapshot hw hrem hL hmention
          · exact add_le_add_left (branch_bad_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit
              hverify hone fuel snapshot hw hrem hL hmention) _
  refine hbind.trans ?_
  have hpre := ForkEventUnion.map_or_le
    (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel)
    (cutBad (mentionEvent tau)) (cutBad collisionEvent)
  have hcut : (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (cutBad (fun world => mentionEvent tau world || collisionEvent world)) =
      (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (fun c => cutBad (mentionEvent tau) c || cutBad collisionEvent c) := by
    congr 1
    funext c
    cases c with
    | saved snapshot => rfl
    | ended terminal => cases terminal <;> rfl
  rw [hcut]
  refine (add_le_add_left hpre _).trans ?_
  have hm := CandidateGameBounds.prefix_mention_bound S V verifyBudget publicKey sampleWitness adversary bound index fuel
    hcommit hverify hone
  have hc := CandidateGameBounds.prefix_collision_bound S V verifyBudget publicKey sampleWitness adversary bound index fuel
    hcommit hverify hone
  calc _ ≤ _ := add_le_add (add_le_add hm hc) le_rfl
    _ = _ := by rw [hB]; ring

/-- Success is at most success without the charged events plus the charged events. -/
theorem forkExperiment_split (index fuel : Nat) :
    (forkExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel) true ≤
      (goodForkExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true +
        (forkBadExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true := by
  unfold forkExperiment goodForkExperiment forkBadExperiment
  refine ForkGoodOutcome.bind_true_le_add _ _ _ _ fun c _ => ?_
  cases c with
  | ended terminal =>
    simp only [forkAtCut, PMF.pure_apply]
    exact (RandomOracleTrap.ite_le_indicator false).trans (by rw [RandomOracleTrap.indicator_false]; exact zero_le _)
  | saved snapshot =>
    simp only [forkAtCut]
    exact ForkGoodOutcome.map_split_le _ _ _

/-- A successful candidate fork without the charged events: the uniform slope
data, or a branch's mask input first queried after the fork. -/
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
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      adversary snapshot).support)
    (hw : forkWins snapshot.input result = true) (hgood : forkBad (tau := tau) snapshot result = false) :
    ∃ left right a b bodyA bodyB recA recB, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.signature.body = some bodyA ∧ b.signature.body = some bodyB ∧ a.target ≠ b.target ∧
      Evaluates snapshot.world.other.family a.world.other.hashTable a.world.other.cipherHistory
        (Spec.CandidateScheme.verifyProgram V bodyA.1 bodyA.2.1 a.signature.piop bodyA.2.2.1) (Except.ok recA) ∧
      Evaluates snapshot.world.other.family b.world.other.hashTable b.world.other.cipherHistory
        (Spec.CandidateScheme.verifyProgram V bodyB.1 bodyB.2.1 b.signature.piop bodyB.2.2.1) (Except.ok recB) ∧
      recA.lines = snapshot.input.payload.1 ∧ recB.lines = snapshot.input.payload.1 ∧
      snapshot.input.payload.2 = (Spec.SignatureComposition.verificationInput widths S.hdegree S.hsize S.signer.xi
        S.expandBatching S.H' S.y snapshot.publicKey a.message ⟨bodyA.1, a.signature.piop, bodyA.2.1,
          (bodyA.2.2.1.1, ⟨[], fun e => bodyA.2.2.1.2.hiddenCommitments e⟩), bodyA.2.2.2⟩ recA).coefficients ∧
      (UniformSlope p randomCount enough V snapshot.world.other.family snapshot.world.other.hashTable
          (a.world.other.cipherHistory ++ b.world.other.cipherHistory) bodyA.1 bodyB.1 bodyA.2.1 bodyB.2.1
          a.signature.piop b.signature.piop bodyA.2.2.1 bodyB.2.2.1 ∨
        MaskAfterCut snapshot.world.other.hashTable a.world.other.hashTable ∨
        MaskAfterCut snapshot.world.other.hashTable b.world.other.hashTable) := by
  obtain ⟨left, right, a, b, bodyA, bodyB, recA, recB, hres, ha, hb, hbodyA, hbodyB, hne, hevalA, hevalB, hlinesA,
    hlinesB, hcoeffs, houtcome⟩ := fork_outcome S V verifyBudget publicKey sampleWitness adversary hlambda htau xi p encode
    randomCount enough hmid hencoding hlinesEnc index fuel c hc snapshot hsnap result hr hw
  have hwell := CandidateGameBounds.snapshot_wellFormed S V verifyBudget publicKey sampleWitness adversary index fuel c hc
    snapshot hsnap
  rw [hres] at hgood
  simp only [forkBad, ha, hb, terminalBad, Bool.or_eq_false_iff] at hgood
  obtain ⟨⟨_, hcollision⟩, hbadA, hbadB⟩ := hgood
  simp only [ForkEventUnion.branchBad, Bool.or_eq_false_iff] at hbadA hbadB
  have hfree : DigestCollisionFree snapshot.world.other.hashTable :=
    SharedCollisionBound.collisionFree_of_not_event _ hwell hcollision
  refine ⟨left, right, a, b, bodyA, bodyB, recA, recB, hres, ha, hb, hbodyA, hbodyB, hne, hevalA, hevalB, hlinesA,
    hlinesB, hcoeffs, ?_⟩
  rcases houtcome with huni | hevA | hevB | hcol
  · exact Or.inl huni
  · rcases hevA with ht | hm | hmask
    · exact absurd ht (by simp [targetEvent] at hbadA; simp [hbadA.1])
    · exact absurd hm (by simp [mentionEvent] at hbadA; simp [hbadA.2])
    · exact Or.inr (Or.inl hmask)
  · rcases hevB with ht | hm | hmask
    · exact absurd ht (by simp [targetEvent] at hbadB; simp [hbadB.1])
    · exact absurd hm (by simp [mentionEvent] at hbadB; simp [hbadB.2])
    · exact Or.inr (Or.inr hmask)
  · exact absurd hfree hcol

end Events

end
end SDitH.Proofs.CandidateForkOutcome
