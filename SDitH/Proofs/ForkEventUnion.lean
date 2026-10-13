import SDitH.Proofs.SharedCollisionBound
import SDitH.Proofs.ForkOutcome

/-! The charged events of the fork experiment, united. The bad event of a
fork at a saved snapshot is the prefix's mention or collision event at
the snapshot's world, or a branch's fixed-target or mention event at
either attempt, with the snapshot's own table and lines value as the
cut and the target. Its probability over the fork experiment is at most
the prefix mention and collision bounds plus twice the branch target and
mention bounds, all at the level fuel times twice the budget bound. The
mask event is not charged and stays in the deterministic outcome. -/

namespace SDitH.Proofs.ForkEventUnion

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrap
open Spec.SharedScheme Spec.SharedSigning
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open GameEventBound (terminalBad)
open CutEventBound (cutBad)
open SharedTargetBound (targetEvent digestInv)
open SharedMentionBound (mentionEvent epsilonM)
open SharedCollisionBound (collisionEvent epsilonC)
open SharedGameInvariant (WellFormed)
open scoped Classical ENNReal
noncomputable section

section Generic

variable {A : Type*}

theorem map_or_le (p : PMF A) (f g : A → Bool) :
    (p.map (fun x => f x || g x)) true ≤ (p.map f) true + (p.map g) true := by
  rw [RandomOracleTrap.map_true_eq, RandomOracleTrap.map_true_eq, RandomOracleTrap.map_true_eq, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← mul_add]
  refine mul_le_mul_right ?_ _
  cases f a <;> cases g a <;> simp [indicator]

theorem map_const_or_le (p : PMF A) (a : Bool) (g : A → Bool) :
    (p.map (fun x => a || g x)) true ≤ indicator a + (p.map g) true := by
  cases a
  · simp only [Bool.false_or, indicator, Bool.false_eq_true, ↓reduceIte, zero_add, le_refl]
  · simp only [Bool.true_or, indicator, ↓reduceIte]
    exact (PMF.coe_le_one _ _).trans le_self_add

end Generic

section Cut

variable {PK SK Msg Sig HI Dg Oth Qu Ans St : Type*} [Fintype Dg] [Nonempty Dg]

/-- A saved snapshot's remaining fuel is at most the cut's fuel. -/
theorem cut_remaining_le (scheme : Scheme PK SK Msg Sig HI Dg Oth Qu Ans)
    (adversary : Adversary PK Msg Sig HI Dg Qu Ans St) :
    ∀ (index fuel : Nat) (pk : PK) (sk : SK) (state : St)
      (world : World HI Dg Oth) (trace : Trace Msg HI Qu)
      (c : Spec.SignatureReplay.Cut PK SK Msg Sig HI Dg Oth Qu St),
      c ∈ (Spec.SignatureReplay.cut scheme adversary index fuel pk sk state world trace).support →
      ∀ snapshot, c = .saved snapshot → snapshot.remaining ≤ fuel := by
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state world trace c hc snapshot hs
    simp only [Spec.SignatureReplay.cut, PMF.mem_support_pure_iff] at hc
    subst hc
    cases hs
  | succ fuel ih =>
    intro pk sk state world trace c hc snapshot hs
    simp only [Spec.SignatureReplay.cut] at hc
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
    cases action with
    | abort =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst hrest
      cases hs
    | finish message signature =>
      obtain ⟨result, _, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst hres
      cases hr : result.1 with
      | none => rw [hr] at hs; cases hs
      | some input => rw [hr] at hs; cases hs
    | sign message next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact (ih index pk sk _ _ _ c hrun snapshot hs).trans (Nat.le_succ fuel)
    | hash input next =>
      cases index with
      | zero =>
        simp only [PMF.mem_support_pure_iff] at hrest
        subst hrest
        cases hs
        exact Nat.le_succ fuel
      | succ index =>
        obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
        exact (ih index pk sk _ _ _ c hrun snapshot hs).trans (Nat.le_succ fuel)
    | query input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact (ih index pk sk _ _ _ c hrun snapshot hs).trans (Nat.le_succ fuel)

end Cut

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

/-- The branch event charged at a snapshot: the fixed-target event at the
snapshot's table and lines value, or the mention event. -/
def branchBad (snapshot : Snapshot (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State)
    (world : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) : Bool :=
  targetEvent snapshot.world.other.hashTable snapshot.input.payload.1 world || mentionEvent tau world

/-- The charged events of a fork at a snapshot. -/
def forkBad (snapshot : Snapshot (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State)
    (result : Option (Branch (List Bool)
        (Signature (Spec.BAVC.Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
        (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) ×
      Branch (List Bool)
        (Signature (Spec.BAVC.Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
        (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda))) : Bool :=
  (mentionEvent tau snapshot.world.other || collisionEvent snapshot.world.other) ||
    match result with
    | none => false
    | some (l, r) => terminalBad (branchBad (tau := tau) snapshot) l.checked.terminal || terminalBad (branchBad (tau := tau) snapshot) r.checked.terminal

/-- The charged events over the fork experiment. -/
def forkBadExperiment (index fuel : Nat) : PMF Bool :=
  (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).bind fun c =>
    match c with
    | .ended _ => PMF.pure false
    | .saved snapshot => (forkAt (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
        (forkBad snapshot)

/-- A saved snapshot of the shared cut experiment has a well-formed world. -/
theorem snapshot_wellFormed (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot) : WellFormed snapshot.world.other := by
  have hpW := SharedGameInvariant.shared_preserves S V verifyBudget publicKey sampleWitness WellFormed
    (fun budget program world result hr hQ => SharedGameInvariant.runProgram_wellFormed budget program world result hr hQ)
  obtain ⟨generated, hgen, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
  obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  have hinit : WellFormed generated.2.2.other := by
    obtain ⟨g, hg, hgen'⟩ := (PMF.mem_support_map_iff _ _ _).mp hgen
    subst hgen'
    exact SharedGameInvariant.keygen_wellFormed publicKey sampleWitness g hg
  exact (SharedGameInvariant.cut_preserves _ WellFormed hpW adversary index fuel _ _ state _ _ c hcut hinit).1 snapshot hsnap

/-- The remaining fuel of a saved snapshot of the cut experiment. -/
theorem snapshot_remaining_le (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot) : snapshot.remaining ≤ fuel := by
  obtain ⟨generated, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
  obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  exact cut_remaining_le _ adversary index fuel _ _ state _ _ c hcut snapshot hsnap

/-- One fresh branch's charged event, at a well-formed snapshot without the
prefix mention event. -/
theorem branch_bad_bound (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound)
    (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (fuel : Nat)
    (snapshot : Snapshot (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State)
    (hw : WellFormed snapshot.world.other) (hrem : snapshot.remaining ≤ fuel)
    (hL : snapshot.world.other.trace.length + snapshot.remaining * (bound + bound) ≤ fuel * (bound + bound))
    (hmention : mentionEvent tau snapshot.world.other = false) :
    ((freshBranch (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
      (fun branch => terminalBad (branchBad (tau := tau) snapshot) branch.checked.terminal)) true ≤
      fuel * (bound * digestInv lambda + bound * digestInv lambda) +
        fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) := by
  have hsplit : (fun branch : Branch (List Bool)
        (Signature (Spec.BAVC.Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
        (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) =>
      terminalBad (branchBad (tau := tau) snapshot) branch.checked.terminal) =
      fun branch => terminalBad (targetEvent snapshot.world.other.hashTable snapshot.input.payload.1) branch.checked.terminal ||
        terminalBad (mentionEvent tau) branch.checked.terminal := by
    funext branch
    generalize branch.checked.terminal = t
    cases t <;> rfl
  rw [hsplit]
  refine (map_or_le _ _ _).trans (add_le_add ?_ ?_)
  · refine (SharedTargetBound.branch_target_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone
      adversary snapshot hw snapshot.input.payload.1).trans ?_
    exact mul_le_mul_left (Nat.cast_le.mpr hrem) _
  · refine (SharedMentionBound.branch_mention_bound S V verifyBudget publicKey sampleWitness bound hcommit hverify hone
      adversary snapshot (fuel * (bound + bound)) hL).trans ?_
    rw [hmention, RandomOracleTrap.indicator_false, zero_add]
    exact mul_le_mul_left (Nat.cast_le.mpr hrem) _

/-- The charged events of the fork experiment: the prefix mention and
collision bounds plus twice the branch target and mention bounds. -/
theorem forkBad_bound (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound)
    (hverify : verifyBudget ≤ bound) (hone : 1 ≤ bound) (index fuel : Nat) :
    (forkBadExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true ≤
      fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) +
      fuel * (epsilonC lambda bound (fuel * (bound + bound)) + epsilonC lambda bound (fuel * (bound + bound))) +
      (2 : ℝ≥0∞) * (fuel * (bound * digestInv lambda + bound * digestInv lambda) +
        fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound)))) := by
  set B := fuel * (bound * digestInv lambda + bound * digestInv lambda) +
    fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) with hB
  have hbind : (forkBadExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true ≤
      ((cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
        (cutBad (fun world => mentionEvent tau world || collisionEvent world))) true + (B + B) := by
    unfold forkBadExperiment
    have h := RandomOracleTrap.bind_map_indicator_le
      (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel)
      (fun c => match c with
        | .ended _ => PMF.pure false
        | .saved snapshot => (forkAt (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
            (forkBad snapshot))
      id (cutBad (fun world => mentionEvent tau world || collisionEvent world)) (B + B) ?_
    · simpa only [PMF.map_id] using h
    intro c hc
    cases c with
    | ended terminal =>
      simp only [PMF.pure_map, PMF.pure_apply, id]
      exact (RandomOracleTrap.ite_le_indicator false).trans (by rw [RandomOracleTrap.indicator_false]; exact zero_le _)
    | saved snapshot =>
      simp only [PMF.map_id, cutBad]
      have hw := snapshot_wellFormed S V verifyBudget publicKey sampleWitness adversary index fuel _ hc snapshot rfl
      have hrem := snapshot_remaining_le S V verifyBudget publicKey sampleWitness adversary index fuel _ hc snapshot rfl
      have hL := SharedCollisionBound.prefix_size S V verifyBudget publicKey sampleWitness adversary bound hcommit hverify
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
        have hfork : (forkAt (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
            (forkBad snapshot) = (forkAt (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).map
            (fun result => match result with
              | none => false
              | some (l, r) => terminalBad (branchBad (tau := tau) snapshot) l.checked.terminal ||
                  terminalBad (branchBad (tau := tau) snapshot) r.checked.terminal) := by
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
            (freshBranch (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot) _ _
            (fun l => terminalBad (branchBad (tau := tau) snapshot) l.checked.terminal) B ?_).trans ?_
          · intro l _
            rw [PMF.map_comp]
            refine (map_const_or_le _ _ _).trans (add_le_add_right ?_ _)
            exact branch_bad_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit hverify hone fuel
              snapshot hw hrem hL hmention
          · exact add_le_add_left (branch_bad_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit
              hverify hone fuel snapshot hw hrem hL hmention) _
  refine hbind.trans ?_
  have hpre := map_or_le (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel)
    (cutBad (mentionEvent tau)) (cutBad collisionEvent)
  have hcut : (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (cutBad (fun world => mentionEvent tau world || collisionEvent world)) =
      (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).map
      (fun c => cutBad (mentionEvent tau) c || cutBad collisionEvent c) := by
    congr 1
    funext c
    cases c with
    | saved snapshot => rfl
    | ended terminal => cases terminal <;> rfl
  rw [hcut]
  refine (add_le_add_left hpre _).trans ?_
  have hm := SharedCollisionBound.prefix_mention_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit
    hverify hone index fuel
  have hc := SharedCollisionBound.prefix_collision_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit
    hverify hone index fuel
  calc _ ≤ _ := add_le_add (add_le_add hm hc) le_rfl
    _ = _ := by rw [hB]; ring

end Shared

end
end SDitH.Proofs.ForkEventUnion
