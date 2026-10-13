import SDitH.Proofs.ForkWitnessedBound
import SDitH.Proofs.SharedSlopeBound

/-! The unseen match under the snapshot's family: through the
family-dependent fork bound, the event's probability is at most the
unobserved-key bound at the second branch's final world (a seed unqueried
at both paired inputs matching both recorded halves of a named seed's
commitment, under the family resampled at the end), hence at most the
unseen cost at the counted invariant's largest history length. -/

namespace SDitH.Proofs.ForkUnseenBound

open Spec.SignatureSecurity Spec.SignatureReplay Spec.IdealCipher Spec.IdealCipherPairCollision
open Spec.DomainSeparation (Bits)
open Spec.RandomOracleTrap (indicator)
open Spec.BAVC Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.SharedSlopeGame Spec.SeedPairing Spec.SlopeConsistency
open GameResample ChargeExpect RunWorld GamePrune HistoryShiftGame CipherResample ForkRestore ForkRestoreLemmas
open ForkRestoreShift ForkRestoreEq ForkRestoreEnd SharedResample HiddenSlice MeanHybrid PairMass PairOracles PairRun
open PairFork PairForkFamily ForkWitnessedBound SignBridge PruneCompatClosure
open CandidateResample CandidatePrepLaw CandidatePrune CipherInvariant InvCExtra CandidateReduction CandidateKeepsFamily
open CandidateShift SimulationGap ChargeCutExpect CutHybridGen ForkEventUnion SlopeEventSetting SlopeCoverFork
open ForgeryReduction SharedSlopeBound
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))

/-- The claim of two branches: the first's salt and auxiliary data with
the completed seed vector, when both are attempts with bodies. -/
def claimOf (left right : Br F lambda tau kappa s higherCount w widths) :
    Option (Claim lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) :=
  match left.checked.terminal, right.checked.terminal with
  | .attempt a, .attempt b =>
    match a.signature.body, b.signature.body with
    | some bodyA, some bodyB =>
      some ⟨bodyA.1, fullOf V a bodyA bodyB, fun _ => fun _ => false, fun _ => false, fun _ => false, bodyA.2.1⟩
    | _, _ => none
  | _, _ => none

/-- The unseen predicate of two branches at a family and a history. -/
def unseenΦ (left right : Br F lambda tau kappa s higherCount w widths) (g : Family (Bits lambda) (Bits lambda))
    (U : List (Entry (Bits lambda) (Bits lambda))) : Bool :=
  match claimOf V left right with
  | some c => decide (∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (seed out0 out1 : Bits lambda),
      seed ≠ c.full e i ∧
      Unseen U seed (input0 V.variant c.salt e i) ∧
      Unseen U seed (companion (input0 V.variant c.salt e i)) ∧
      (⟨c.full e i, input0 V.variant c.salt e i, out0⟩ : Entry (Bits lambda) (Bits lambda)) ∈ U ∧
      (⟨c.full e i, companion (input0 V.variant c.salt e i), out1⟩ : Entry (Bits lambda) (Bits lambda)) ∈ U ∧
      g seed (input0 V.variant c.salt e i) = out0 ∧
      g seed (companion (input0 V.variant c.salt e i)) = out1)
  | none => false

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem unseen_iff {U U' : List (Entry (Bits lambda) (Bits lambda))} (h : ∀ x, x ∈ U ↔ x ∈ U') (seed x : Bits lambda) :
    Unseen U seed x ↔ Unseen U' seed x := by
  constructor
  · intro hu e he hk
    exact hu e ((h e).mpr he) hk
  · intro hu e he hk
    exact hu e ((h e).mp he) hk

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem unseenΦ_set (left right : Br F lambda tau kappa s higherCount w widths) (g : Family (Bits lambda) (Bits lambda))
    (U U' : List (Entry (Bits lambda) (Bits lambda))) (h : ∀ x, x ∈ U ↔ x ∈ U') :
    unseenΦ V left right g U = unseenΦ V left right g U' := by
  unfold unseenΦ
  cases claimOf V left right with
  | none => rfl
  | some c =>
    refine decide_eq_decide.mpr ?_
    constructor
    · rintro ⟨e, i, seed, out0, out1, hne, hu0, hu1, hm0, hm1, h0, h1⟩
      exact ⟨e, i, seed, out0, out1, hne, (unseen_iff h _ _).mp hu0, (unseen_iff h _ _).mp hu1, (h _).mp hm0, (h _).mp hm1,
        h0, h1⟩
    · rintro ⟨e, i, seed, out0, out1, hne, hu0, hu1, hm0, hm1, h0, h1⟩
      exact ⟨e, i, seed, out0, out1, hne, (unseen_iff h _ _).mpr hu0, (unseen_iff h _ _).mpr hu1, (h _).mpr hm0,
        (h _).mpr hm1, h0, h1⟩

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem claimOf_shift (left right : Br F lambda tau kappa s higherCount w widths) (H : List (Entry (Bits lambda) (Bits lambda))) :
    claimOf V left (shiftBranch H right) = claimOf V left right := by
  unfold claimOf shiftBranch shiftT
  cases left.checked.terminal <;> cases right.checked.terminal <;> rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem claimOf_famR (left right : Br F lambda tau kappa s higherCount w widths) (f : Family (Bits lambda) (Bits lambda)) :
    claimOf V left (setFamilyBranch f right) = claimOf V left right := by
  unfold claimOf setFamilyBranch setFamilyT
  cases left.checked.terminal <;> cases right.checked.terminal <;> rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem unseenΦ_shift (left right : Br F lambda tau kappa s higherCount w widths) (g : Family (Bits lambda) (Bits lambda))
    (U : List (Entry (Bits lambda) (Bits lambda))) (H : List (Entry (Bits lambda) (Bits lambda))) :
    unseenΦ V left (shiftBranch H right) g U = unseenΦ V left right g U := by
  unfold unseenΦ
  rw [claimOf_shift]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem unseenΦ_famR (left right : Br F lambda tau kappa s higherCount w widths) (g : Family (Bits lambda) (Bits lambda))
    (U : List (Entry (Bits lambda) (Bits lambda))) (f : Family (Bits lambda) (Bits lambda)) :
    unseenΦ V left (setFamilyBranch f right) g U = unseenΦ V left right g U := by
  unfold unseenΦ
  rw [claimOf_famR]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The unseen predicate at a claim is the shared game's unseen event. -/
theorem unseenΦ_eq (left right : Br F lambda tau kappa s higherCount w widths)
    (c : Claim lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) (hc : claimOf V left right = some c)
    (g : Family (Bits lambda) (Bits lambda)) (U : List (Entry (Bits lambda) (Bits lambda))) :
    unseenΦ V left right g U = unseenEvent (slopeSetting S V) (fun c' => c') g c U := by
  unfold unseenΦ
  rw [hc]
  rfl

section Events

variable {State : Type*}

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem unseenFork_none (snapshot : Snap F lambda s higherCount w widths State) :
    unseenFork (tau := tau) (kappa := kappa) V snapshot none = false := rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem unseenFork_left (snapshot : Snap F lambda s higherCount w widths State)
    (left right : Br F lambda tau kappa s higherCount w widths)
    (h : unseenFork (tau := tau) (kappa := kappa) V snapshot (some (left, right)) = true) :
    ∃ att, left.checked.terminal = Terminal.attempt att := by
  simp only [unseenFork, onAttempts] at h
  cases hl : left.checked.terminal with
  | attempt a => exact ⟨a, rfl⟩
  | exhausted t => rw [hl] at h; simp at h
  | aborted t => rw [hl] at h; simp at h
  | rejected t => rw [hl] at h; simp at h

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem unseenFork_famL (snapshot : Snap F lambda s higherCount w widths State)
    (left right : Br F lambda tau kappa s higherCount w widths) (g : Family (Bits lambda) (Bits lambda)) :
    unseenFork (tau := tau) (kappa := kappa) V snapshot (some (setFamilyBranch g left, right)) =
      unseenFork (tau := tau) (kappa := kappa) V snapshot (some (left, right)) := by
  simp only [unseenFork, onAttempts, setFamilyBranch, setFamilyT]
  cases left.checked.terminal <;> cases right.checked.terminal <;> rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The unseen event at a family gives the unseen predicate on the union. -/
theorem unseenFork_union (snapshot : Snap F lambda s higherCount w widths State)
    (left right : Br F lambda tau kappa s higherCount w widths) (g : Family (Bits lambda) (Bits lambda))
    (h : unseenFork (tau := tau) (kappa := kappa) V { snapshot with world := setFamily snapshot.world g }
      (some (left, right)) = true) :
    unseenΦ V left right g (attemptHistory right ++ attemptHistory left) = true := by
  simp only [unseenFork, onAttempts] at h
  unfold unseenΦ claimOf attemptHistory
  cases hl : left.checked.terminal with
  | attempt a =>
    cases hr : right.checked.terminal with
    | attempt b =>
      rw [hl, hr] at h
      simp only at h ⊢
      rcases hba : a.signature.body with _ | bodyA
      · rw [hba] at h; simp at h
      rcases hbb : b.signature.body with _ | bodyB
      · rw [hba, hbb] at h; simp at h
      rw [hba, hbb] at h
      simp only at h ⊢
      have hw := of_decide_eq_true h
      have hiff : ∀ x, x ∈ a.world.other.cipherHistory ++ b.world.other.cipherHistory ↔
          x ∈ b.world.other.cipherHistory ++ a.world.other.cipherHistory := by
        intro x
        rw [List.mem_append, List.mem_append]
        exact or_comm
      obtain ⟨e, i, seed, out0, out1, hne, hu0, hu1, hm0, hm1, h0, h1⟩ := hw
      exact decide_eq_true ⟨e, i, seed, out0, out1, hne, (unseen_iff hiff _ _).mp hu0, (unseen_iff hiff _ _).mp hu1,
        (hiff _).mp hm0, (hiff _).mp hm1, h0, h1⟩
    | exhausted t => rw [hl, hr] at h; simp at h
    | aborted t => rw [hl, hr] at h; simp at h
    | rejected t => rw [hl, hr] at h; simp at h
  | exhausted t => rw [hl] at h; simp at h
  | aborted t => rw [hl] at h; simp at h
  | rejected t => rw [hl] at h; simp at h

end Events

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem claimOf_right_attempt (left right : Br F lambda tau kappa s higherCount w widths)
    (c : Claim lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) (hc : claimOf V left right = some c) :
    ∃ att, right.checked.terminal = Terminal.attempt att := by
  unfold claimOf at hc
  revert hc
  cases hl : left.checked.terminal <;> cases hr : right.checked.terminal <;> intro hc
  all_goals first | exact ⟨_, rfl⟩ | simp at hc

/-- The attempt of a fresh branch embeds exactly the branch's final world. -/
theorem freshBranchW_attempt_eq {PublicKey SecretKey Message Signature HashInput Digest Query Answer State : Type*}
    [Fintype Digest] [Nonempty Digest] {lambda s wit rnd : Nat}
    (sch : Scheme PublicKey SecretKey Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (snapshot : Snapshot PublicKey SecretKey Message HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query State)
    (rw : Branch Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query ×
      GW HashInput Digest lambda s wit rnd) (h : rw ∈ (freshBranchW sch adversary snapshot).support)
    (att : Attempt Message Signature HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) Query)
    (hatt : rw.1.checked.terminal = Terminal.attempt att) : att.world = rw.2 := by
  unfold freshBranchW at h
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at h
  obtain ⟨answer, -, r, hr, checked, hc, rfl⟩ := h
  have ht := finalize_terminal r.1 checked hc
  have hw := runW_attempt sch adversary _ _ _ _ _ _ r hr
  simp only at hatt
  rw [hatt] at ht
  rw [← ht] at hw
  simp only [withWorld, Terminal.attempt.injEq] at hw
  have := congrArg Attempt.world hw
  simpa using this.symm

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A mass bound on the uniform distribution transfers across finiteness
instances. -/
theorem uniform_le_congr {α : Type*} (i1 i2 : Fintype α) [Nonempty α] (f : α → Bool) (ε : ℝ≥0∞)
    (h : ((@PMF.uniformOfFintype α i1 _).map f) true ≤ ε) : ((@PMF.uniformOfFintype α i2 _).map f) true ≤ ε := by
  cases Subsingleton.elim i1 i2
  exact h

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
include S in
/-- The end-resampled unseen predicate on the union is at most the unseen
cost at the final history's length. -/
theorem unseen_le_cost (hlambda : 0 < lambda) (left right : Br F lambda tau kappa s higherCount w widths)
    (final : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hatt : ∀ att, right.checked.terminal = Terminal.attempt att → att.world.other.cipherHistory = final.cipherHistory)
    (hleft : attemptHistory left ⊆ final.cipherHistory)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g final.cipherHistory) (q : Nat)
    (hlen : final.cipherHistory.length ≤ q) :
    mean (posterior final.cipherHistory) (fun g =>
        indicator (unseenΦ V left right g (attemptHistory right ++ attemptHistory left))) ≤
      unseenCost lambda tau kappa q := by
  cases hc : claimOf V left right with
  | none =>
    refine (mean_le_const _ _ 0 fun g _ => ?_).trans (zero_le _)
    simp [unseenΦ, hc, indicator]
  | some c =>
    obtain ⟨att, hr⟩ := claimOf_right_attempt V left right c hc
    have hAH : attemptHistory right = final.cipherHistory := by
      unfold attemptHistory
      rw [hr]
      exact hatt att hr
    have hiff : ∀ x, x ∈ attemptHistory right ++ attemptHistory left ↔ x ∈ final.cipherHistory := by
      intro x
      rw [List.mem_append, hAH]
      constructor
      · rintro (hx | hx)
        · exact hx
        · exact hleft hx
      · intro hx
        exact Or.inl hx
    have hΦ : ∀ g, unseenΦ V left right g (attemptHistory right ++ attemptHistory left) =
        unseenEvent (slopeSetting S V) (fun c' => c') g c final.cipherHistory := by
      intro g
      rw [unseenΦ_set V left right g _ _ hiff, unseenΦ_eq S V left right c hc]
    simp only [hΦ]
    rw [posterior_world ⟨final.cipherHistory, hpos⟩, mean_map, ← map_true]
    exact uniform_le_congr _ _ _ _
      (unseen_fixed_world_bound (slopeSetting S V) hlambda (fun c' => c') c ⟨final.cipherHistory, hpos⟩ q hlen)

variable (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The fork bound of the unseen match. -/
theorem fork_unseen_bound (hvc : verifyBudget ≤ commitBudget tau kappa) (hlambda : 0 < lambda) (B : Nat)
    (snapshot : Snap F lambda s higherCount w widths State) (n : Nat)
    (hn : InvC (tau := tau) (kappa := kappa) n snapshot.world) (hB : n + 2 * (snapshot.remaining + 1) ≤ B) :
    mean (resampleW resample snapshot.world) (fun w' =>
        ((forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
          { snapshot with world := w' }).map (unseenFork V { snapshot with world := w' })) true) ≤
      unseenCost lambda tau kappa (commitBudget tau kappa * B) := by
  have hpub' : ∀ (query : Query lambda) (world) (n : Nat) (r), InvC (tau := tau) (kappa := kappa) n world →
      r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query
        world).support → InvC (tau := tau) (kappa := kappa) (n + 1) r.2 :=
    fun query world n r h hr => invC_pub S V verifyBudget publicKey sampleWitness query world n r h hr
  refine (fork_family_bound _ adversary (unseenΦ V) (fun l r g U U' h => unseenΦ_set V l r g U U' h)
    (fun l r g U H => unseenΦ_shift V l r g U H) (fun l r g U f => unseenΦ_famR V l r g U f)
    (fun snapshot => unseenFork V snapshot) (fun s' => unseenFork_none V s') (fun s' l r h => unseenFork_left V s' l r h)
    (fun s' l r g => unseenFork_famL V s' l r g) (fun s' l r g h => unseenFork_union V s' l r g h)
    (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
    (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
    (honest_keepsFamily S V verifyBudget publicKey sampleWitness) (publicOracle_keepsFamily S V verifyBudget publicKey sampleWitness)
    (prepareVerification_keepsFamily S V verifyBudget publicKey sampleWitness)
    (honest_grows S V verifyBudget publicKey sampleWitness) (publicOracle_grows S V verifyBudget publicKey sampleWitness)
    (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
    (honest_shiftLaw S V verifyBudget publicKey sampleWitness) (publicOracle_shiftLaw S V verifyBudget publicKey sampleWitness)
    (prepareVerification_shiftLaw S V verifyBudget publicKey sampleWitness) snapshot).trans ?_
  refine mean_le_const _ _ _ fun a _ => ?_
  have hWaInv : InvC (tau := tau) (kappa := kappa) (n + 1)
      { snapshot.world with hashTable := Function.update snapshot.world.hashTable snapshot.input (some a) } :=
    invC_update snapshot.world snapshot.input n a hn
  refine mean_le_const _ _ _ fun w0 hw0 => mean_le_const _ _ _ fun r hr => mean_le_const _ _ _ fun c hc =>
    mean_le_const _ _ _ fun y hy => mean_le_const _ _ _ fun rw hrw => ?_
  have hwInv := invC_resample _ _ hWaInv w0 hw0
  have hr2 : InvC (tau := tau) (kappa := kappa) (n + 1 + snapshot.remaining) r.2 :=
    runW_inv' _ adversary (InvC (tau := tau) (kappa := kappa)) invC_mono invC_query
      (invC_honest S V verifyBudget publicKey sampleWitness) hpub' (invC_prep S V verifyBudget publicKey sampleWitness hvc)
      _ _ _ _ _ _ _ hwInv r hr
  have hyInv : InvC (tau := tau) (kappa := kappa) (n + 1 + snapshot.remaining) y :=
    invC_resample _ _ (invC_restore _ _ _ (invC_mono _ _ _ (by omega) hn) hr2) y hy
  have hrwInv : InvC (tau := tau) (kappa := kappa) (n + 1 + snapshot.remaining + 1 + snapshot.remaining) rw.2 :=
    freshBranchW_inv _ adversary (InvC (tau := tau) (kappa := kappa)) invC_mono invC_query
      (invC_honest S V verifyBudget publicKey sampleWitness) hpub' (invC_prep S V verifyBudget publicKey sampleWitness hvc)
      invC_update { snapshot with world := y } _ hyInv rw hrw
  have hlen : rw.2.other.cipherHistory.length ≤ commitBudget tau kappa * B :=
    hrwInv.2.2.trans (Nat.mul_le_mul_left _ (by omega))
  have hsub := union_subset_final _ adversary (honest_grows S V verifyBudget publicKey sampleWitness)
    (publicOracle_grows S V verifyBudget publicKey sampleWitness) (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
    snapshot a r (runW_attempt _ adversary _ _ _ _ _ _ r hr) c (finalize_terminal r.1 c hc) y hy rw hrw
  have hleft : attemptHistory (⟨a, c⟩ : Br F lambda tau kappa s higherCount w widths) ⊆ rw.2.other.cipherHistory :=
    fun x hx => hsub (List.mem_append_right _ hx)
  have hatt : ∀ att, rw.1.checked.terminal = Terminal.attempt att →
      att.world.other.cipherHistory = rw.2.other.cipherHistory := by
    intro att hatt
    rw [freshBranchW_attempt_eq _ adversary _ rw hrw att hatt]
  have hmean : mean (resampleW resample rw.2) (fun w'' =>
      indicator (unseenΦ V ⟨a, c⟩ rw.1 w''.other.family (attemptHistory rw.1 ++ attemptHistory ⟨a, c⟩))) =
      mean (posterior rw.2.other.cipherHistory) (fun g =>
        indicator (unseenΦ V ⟨a, c⟩ rw.1 g (attemptHistory rw.1 ++ attemptHistory ⟨a, c⟩))) := by
    unfold resampleW resample
    rw [mean_map, mean_map]
  rw [hmean]
  exact unseen_le_cost S V hlambda ⟨a, c⟩ rw.1 rw.2.other hatt hleft ⟨_, hrwInv.2.1⟩ _ hlen

/-- The unseen-match bound in the real experiment. -/
theorem unseenFork_le (hvc : verifyBudget ≤ commitBudget tau kappa) (hl : 26 ≤ lambda) (fuel : Nat) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => unseenFork V snapshot) fuel)
        true ≤ unseenCost lambda tau kappa (commitBudget tau kappa * (3 * (fuel + 1) + 2)) := by
  have hlambda : 0 < lambda := by omega
  set B := 3 * (fuel + 1) + 2 with hB
  have hpub' : ∀ (query : Query lambda) (world) (n : Nat) (r), InvC (tau := tau) (kappa := kappa) n world →
      r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query
        world).support → InvC (tau := tau) (kappa := kappa) (n + 1) r.2 :=
    fun query world n r h hr => invC_pub S V verifyBudget publicKey sampleWitness query world n r h hr
  unfold randomEventExperiment
  rw [mean_bind_apply]
  refine mean_le_const _ _ _ fun index _ => ?_
  unfold eventExperiment cutExperiment
  rw [keygen_resampled S V verifyBudget publicKey sampleWitness]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [mean_bind_apply]
  refine mean_le_const _ _ _ fun g hg => ?_
  rw [PMF.bind_comm, mean_bind_apply]
  refine mean_le_const _ _ _ fun state _ => ?_
  rw [← PMF.bind_bind, cut_postLaw resample resample_idem _ adversary (honest_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness), PMF.bind_bind]
  simp only [mean_bind_apply, mean_bind]
  have hinv0 : InvC (tau := tau) (kappa := kappa) 0 g.2.2 := invC_keygen S V verifyBudget publicKey sampleWitness g hg
  refine mean_le_const _ _ _ fun w0 hw0 => mean_le_const _ _ _ fun c hc => ?_
  cases c with
  | ended t =>
    simp only [resampleCut, mean_pure, PMF.pure_apply]
    simp
  | saved sn =>
    simp only [resampleCut, mean_map]
    have hsn : InvC (tau := tau) (kappa := kappa) (0 + (fuel + 1)) sn.world :=
      cut_saved_gen (InvC (tau := tau) (kappa := kappa)) invC_mono invC_query _ adversary
        (invC_honest S V verifyBudget publicKey sampleWitness) hpub' index.val (fuel + 1) _ _ state _ _ 0
        (invC_resample 0 g.2.2 hinv0 w0 hw0) _ hc sn rfl
    have hrem := cut_remaining_le _ adversary index.val (fuel + 1) _ _ state _ _ _ hc sn rfl
    exact fork_unseen_bound S V verifyBudget publicKey sampleWitness adversary hvc hlambda B sn (0 + (fuel + 1)) hsn (by omega)

end
end SDitH.Proofs.ForkUnseenBound
