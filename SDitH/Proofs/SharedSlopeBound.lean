import SDitH.Proofs.SharedSlopeGame
import SDitH.Proofs.IdealCipherUnseenMatch
import SDitH.Proofs.HashCipherPair
import SDitH.Proofs.HashCipher

/-! Probability assembly for the shared-model slope game. The five covering
events are bounded separately: tau^2 mask traps over the hidden family, the
mention and digest-collision prefix events, the witnessed pair collision
through the projection onto the existing shared experiment, and the unseen
double match through the posterior view at the final world. The total is
`tau^2*budget*2^-s + choose(budget,2)*(tau+3)/|Digest| + choose(budget,2)*pairCost
+ tau*2^kappa*2^lambda/((2^lambda-budget)(2^lambda-budget-1))`. The named
claim's queried condition remains part of the winning event. -/

namespace SDitH.Proofs.SharedSlopeBound

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.SlopeConsistency
open Spec.SlopeConsistencyGame (Out)
open Spec.SharedSlopeGame Spec.SeedPrimitives Spec.SeedPairing Spec.IdealCipher Spec.IdealCipherPairCollision
open Spec.RandomOracleMention Spec.ProductOracle Spec.RandomOracleTrap
open Spec.RandomOracleTrace (traceBad)
open IdealCipherFresh
open scoped Classical ENNReal BigOperators
noncomputable section

section Generic

variable {Input Digest Key Block State : Type*} [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]

theorem joint_trace_bound_family (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (bad : Family Key Block → (Input → Option Digest) → Input → Digest → Bool) (epsilon : ℝ≥0∞)
    (hbad : ∀ family table input, ((PMF.uniformOfFintype Digest).map (bad family table input)) true ≤ epsilon)
    (budget : Nat) (initial : State) :
    ((Spec.HashCipherTrace.jointExperiment procedure budget initial).map
      (fun joint => traceBad (bad joint.1) joint.2.trace)) true ≤ budget * epsilon := by
  simp only [Spec.HashCipherTrace.jointExperiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply ChallengeMixtures.bind_true_le
  intro family _
  have h := HashCipherTrace.run_trace_bound procedure family (bad family) epsilon (hbad family) budget initial
    (fun _ => none) [] [] []
  simpa only [traceBad, List.any_nil, RandomOracleTrap.indicator_false, zero_add] using h

/-- An event of the family, final state and cipher history is bounded by
its posterior bound at the final world. -/
theorem runPosterior_final_bound (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (E : Family Key Block → State → List (Entry Key Block) → Bool) (epsilon : ℝ≥0∞) (q : Nat)
    (hE : ∀ (st : State) (w : World Key Block), w.history.length ≤ q →
      ((PMF.uniformOfFintype (Candidates w)).map (fun family => E family.val st w.history)) true ≤ epsilon)
    (budget : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (world : World Key Block) (hlen : world.history.length + budget ≤ q) :
    ((Spec.HashCipher.runPosterior procedure budget state table hashes world).map
      (fun joint => E joint.1 joint.2.state joint.2.cipherHistory)) true ≤ epsilon := by
  induction budget generalizing state table hashes world with
  | zero =>
    simp only [Spec.HashCipher.runPosterior, Spec.HashCipher.finish, PMF.map_comp, Function.comp_def]
    exact hE state world (by omega)
  | succ budget ih =>
    simp only [Spec.HashCipher.runPosterior, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      simp only [Spec.HashCipher.finish, PMF.map_comp, Function.comp_def]
      exact hE state world (by omega)
    | hash input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Spec.HashCipher.markJoint, Spec.HashCipher.markHash]
      apply ChallengeMixtures.bind_true_le
      intro result _
      exact ih (next result.1) result.2 ((input, result.1) :: hashes) world (by omega)
    | cipher request next =>
      simp only [PMF.map_bind]
      apply ChallengeMixtures.bind_true_le
      intro result hr
      have hlen' : result.2.history.length = world.history.length + 1 := by
        obtain ⟨family, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
        subst heq
        simp [Spec.IdealCipher.observe]
      exact ih (next result.1) table hashes result.2 (by omega)

end Generic

/-- Uniform laws for two `Fintype` instances coincide; instances synthesized
in a generic context (classical decidability) and in a concrete one differ
syntactically, and unifying them by unfolding is intractable. -/
theorem uniform_congr {α : Type*} (i1 i2 : Fintype α) [Nonempty α] :
    @PMF.uniformOfFintype α i1 _ = @PMF.uniformOfFintype α i2 _ := by
  cases Subsingleton.elim i1 i2
  rfl

/-- Transfer a mass bound across two decidability instances of the event. -/
theorem map_decide_le {A : Type*} (p : PMF A) (P : A → Prop) {i1 i2 : ∀ a, Decidable (P a)} (epsilon : ℝ≥0∞)
    (h : (p.map (fun a => @decide (P a) (i1 a))) true ≤ epsilon) :
    (p.map (fun a => @decide (P a) (i2 a))) true ≤ epsilon := by
  have hfun : (fun a => @decide (P a) (i2 a)) = (fun a => @decide (P a) (i1 a)) := by
    funext a
    exact decide_eq_decide.mpr Iff.rfl
  rw [hfun]
  exact h

variable {lambda tau kappa s wit rnd : Nat} {State : Type*}

/-- The unseen-match event as a function of the family, final state and cipher history. -/
def unseenEvent (S : Setting lambda tau kappa s wit rnd) (choose : State → Claim lambda tau kappa s wit rnd)
    (family : CipherFamily lambda) (st : State) (hist : History lambda) : Bool :=
  decide (∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (seed out0 out1 : Bits lambda),
    seed ≠ (choose st).full e i ∧
    Unseen hist seed (input0 S.variant (choose st).salt e i) ∧
    Unseen hist seed (companion (input0 S.variant (choose st).salt e i)) ∧
    (⟨(choose st).full e i, input0 S.variant (choose st).salt e i, out0⟩ : Entry (Bits lambda) (Bits lambda)) ∈ hist ∧
    (⟨(choose st).full e i, companion (input0 S.variant (choose st).salt e i), out1⟩ : Entry (Bits lambda) (Bits lambda)) ∈ hist ∧
    family seed (input0 S.variant (choose st).salt e i) = out0 ∧
    family seed (companion (input0 S.variant (choose st).salt e i)) = out1)

theorem unseenMatch_eq (S : Setting lambda tau kappa s wit rnd) (choose : State → Claim lambda tau kappa s wit rnd)
    (joint : CipherFamily lambda × Res lambda s wit rnd State) :
    unseenMatch S choose joint = unseenEvent S choose joint.1 joint.2.state joint.2.cipherHistory := rfl

def unseenCost (lambda tau kappa q : Nat) : ℝ≥0∞ :=
  (Fintype.card (Fin tau × Fin (2 ^ kappa)) : ℝ≥0∞) * ((Fintype.card (Bits lambda) : ℝ≥0∞) *
    (((1 : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) *
      ((1 : ℝ≥0∞) / ((Fintype.card (Bits lambda) - (q + 1) : Nat) : ℝ≥0∞))))

/-- At a fixed final world, the unseen double match is bounded by the union
over leaf positions of the unobserved-key bound. -/
theorem unseen_fixed_world_bound (S : Setting lambda tau kappa s wit rnd) (hlambda : 0 < lambda)
    (choose : State → Claim lambda tau kappa s wit rnd) (st : State)
    (world : World (Bits lambda) (Bits lambda)) (q : Nat) (hlen : world.history.length ≤ q) :
    ((PMF.uniformOfFintype (Candidates world)).map (fun family : Candidates world =>
      unseenEvent S choose family.val st world.history)) true ≤ unseenCost lambda tau kappa q := by
  set c := choose st with hc
  let x0 : Fin tau → Fin (2 ^ kappa) → Bits lambda := fun e i => input0 S.variant c.salt e i
  let keys : Fin tau → Fin (2 ^ kappa) → Finset (Bits lambda) := fun e i =>
    Finset.univ.filter fun seed => seed ≠ c.full e i ∧ Unseen world.history seed (x0 e i) ∧
      Unseen world.history seed (companion (x0 e i))
  let target : Fin tau → Fin (2 ^ kappa) → Bits lambda → Bits lambda := fun e i input =>
    if h : ∃ out, (⟨c.full e i, input, out⟩ : Entry (Bits lambda) (Bits lambda)) ∈ world.history then
      Classical.choose h else fun _ => false
  have hrecorded : ∀ (family : Candidates world) (e : Fin tau) (i : Fin (2 ^ kappa)) (input out : Bits lambda),
      (⟨c.full e i, input, out⟩ : Entry (Bits lambda) (Bits lambda)) ∈ world.history →
      out = target e i input := by
    intro family e i input out hmem
    have h : ∃ out, (⟨c.full e i, input, out⟩ : Entry (Bits lambda) (Bits lambda)) ∈ world.history := ⟨out, hmem⟩
    have h1 := family.property _ hmem
    have h2 := family.property _ (Classical.choose_spec h)
    simp only [target, dif_pos h]
    exact h1.symm.trans h2
  have h := ChallengeMixtures.boolean_union_bound (PMF.uniformOfFintype (Candidates world))
    (fun family : Candidates world => unseenEvent S choose family.val st world.history)
    (fun pair : Fin tau × Fin (2 ^ kappa) => fun family =>
      decide (∃ seed ∈ keys pair.1 pair.2, family.val seed (x0 pair.1 pair.2) = target pair.1 pair.2 (x0 pair.1 pair.2) ∧
        family.val seed (companion (x0 pair.1 pair.2)) = target pair.1 pair.2 (companion (x0 pair.1 pair.2)))) (by
      intro family _ hev
      obtain ⟨e, i, seed, out0, out1, hne, hu0, hu1, hm0, hm1, h0, h1⟩ := of_decide_eq_true hev
      rw [← hc] at hne hu0 hu1 hm0 hm1 h0 h1
      refine ⟨(e, i), decide_eq_true ⟨seed, ?_, ?_, ?_⟩⟩
      · simp only [keys, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hne, hu0, hu1⟩
      · rw [h0]
        exact hrecorded family e i _ out0 hm0
      · rw [h1]
        exact hrecorded family e i _ out1 hm1)
  refine h.trans ?_
  calc
    _ ≤ ∑ _pair : Fin tau × Fin (2 ^ kappa), (Fintype.card (Bits lambda) : ℝ≥0∞) *
        (((1 : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) *
          ((1 : ℝ≥0∞) / ((Fintype.card (Bits lambda) - (q + 1) : Nat) : ℝ≥0∞))) := by
      apply Finset.sum_le_sum
      intro pair _
      have hb := IdealCipherUnseenMatch.exists_unseen_double_match_bound world (keys pair.1 pair.2) (x0 pair.1 pair.2)
        (target pair.1 pair.2 (x0 pair.1 pair.2)) (target pair.1 pair.2 (companion (x0 pair.1 pair.2))) companion
        (SeedPairing.companion_ne hlambda _) (by
          intro seed hseed
          simp only [keys, Finset.mem_filter, Finset.mem_univ, true_and] at hseed
          exact ⟨hseed.2.1, hseed.2.2⟩) q hlen
      rw [uniform_congr _ (inferInstance : Fintype (Candidates world))] at hb
      refine (map_decide_le _ _ _ hb).trans ?_
      apply mul_le_mul_left
      exact Nat.cast_le.mpr (Finset.card_le_univ _)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unseenCost]

theorem unseen_bound (S : Setting lambda tau kappa s wit rnd) (hlambda : 0 < lambda)
    (choose : State → Claim lambda tau kappa s wit rnd)
    (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (budget : Nat) (initial : State) :
    ((Spec.HashCipherTrace.jointExperiment procedure budget initial).map (unseenMatch S choose)) true ≤
      unseenCost lambda tau kappa budget := by
  have hmap : (Spec.HashCipherTrace.jointExperiment procedure budget initial).map (unseenMatch S choose) =
      (Spec.HashCipher.jointExperiment procedure budget initial).map
        (fun joint => unseenEvent S choose joint.1 joint.2.state joint.2.cipherHistory) := by
    rw [← HashCipherTrace.joint_forget, PMF.map_comp]
    congr 1
  rw [hmap, ← HashCipher.experiments_eq]
  refine runPosterior_final_bound procedure (unseenEvent S choose) (unseenCost lambda tau kappa budget) budget ?_
    budget initial (fun _ => none) [] Spec.IdealCipher.empty (by simp [Spec.IdealCipher.empty])
  intro st w hw
  rw [uniform_congr _ (inferInstance : Fintype (Candidates w))]
  exact unseen_fixed_world_bound S hlambda choose st w budget hw

theorem witnessed_bound (hlambda : 0 < lambda)
    (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (budget : Nat) (initial : State) :
    ((Spec.HashCipherTrace.jointExperiment procedure budget initial).map (witnessed (lambda := lambda) (s := s) (wit := wit) (rnd := rnd))) true ≤
      (budget.choose 2 : ℝ≥0∞) * IdealCipherPairAdaptive.pairCost (Bits lambda) 1 budget := by
  have hmap : (Spec.HashCipherTrace.jointExperiment procedure budget initial).map witnessed =
      (Spec.HashCipher.jointExperiment procedure budget initial).map (Spec.HashCipher.cipherEvent id companion) := by
    rw [← HashCipherTrace.joint_forget, PMF.map_comp]
    rfl
  rw [hmap]
  exact HashCipherPair.experiment_pair_bound procedure budget initial id companion SeedPairing.companion_involutive
    (SeedPairing.companion_ne hlambda) 1 (fun target => IdealCipherUnseenMatch.target_card_one target)

theorem trapAny_bound (S : Setting lambda tau kappa s wit rnd)
    (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (budget : Nat) (initial : State) :
    ((Spec.HashCipherTrace.jointExperiment procedure budget initial).map (trapAny S)) true ≤
      (tau : ℝ≥0∞) * tau * (budget * (2 : ℝ≥0∞)⁻¹ ^ s) := by
  have h := ChallengeMixtures.boolean_union_bound (Spec.HashCipherTrace.jointExperiment procedure budget initial) (trapAny S)
    (fun pair : Fin tau × Fin tau => fun joint =>
      traceBad (tableMaskTrap (vectorOf S joint.1 pair.1 pair.2)) joint.2.trace) (by
      intro joint _ hany
      obtain ⟨e, e', he⟩ := of_decide_eq_true hany
      exact ⟨(e, e'), he⟩)
  refine h.trans ?_
  calc
    _ ≤ ∑ _pair : Fin tau × Fin tau, (budget : ℝ≥0∞) * (Fintype.card (ZMod 2) : ℝ≥0∞)⁻¹ ^ s := by
      apply Finset.sum_le_sum
      intro pair _
      exact joint_trace_bound_family procedure (fun family => tableMaskTrap (vectorOf S family pair.1 pair.2)) _
        (fun family table input => ProductOracle.uniform_mask_trap_le (vectorOf S family pair.1 pair.2) table input)
        budget initial
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, ZMod.card]
      push_cast
      ring

/-- The shared-model slope-consistency bound. -/
theorem bound (S : Setting lambda tau kappa s wit rnd)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (hlambda : 26 ≤ lambda) (htau : 0 < tau) (hcount : 4 * leafCount tau kappa ≤ 2 ^ 24)
    (procedure : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (budget : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd) :
    ((Spec.HashCipherTrace.jointExperiment procedure budget initial).map (wins S choose)) true ≤
      (tau : ℝ≥0∞) * tau * (budget * (2 : ℝ≥0∞)⁻¹ ^ s) +
        ((budget.choose 2 : ℝ≥0∞) * ((tau + 2 : Nat) : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ +
          ((budget.choose 2 : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ +
            ((budget.choose 2 : ℝ≥0∞) * IdealCipherPairAdaptive.pairCost (Bits lambda) 1 budget +
              unseenCost lambda tau kappa budget))) := by
  have hpos : 0 < lambda := by omega
  have hcover := HashCipherPipelineSecurity.event_mass_le (Spec.HashCipherTrace.jointExperiment procedure budget initial)
    (wins S choose)
    (fun joint => trapAny S joint || (prefixBad (digestMention (mentions lambda tau)) joint.2.trace ||
      (prefixBad digestCollision joint.2.trace || (witnessed joint || unseenMatch S choose joint)))) (by
      intro joint hout hwin
      rcases SharedSlopeGame.wins_covered S hencoding hlambda htau hcount procedure budget initial choose joint hout hwin
        with h | h | h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h])
  refine hcover.trans ?_
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  refine add_le_add (trapAny_bound S procedure budget initial) ?_
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  refine add_le_add ?_ ?_
  · have hm := HashCipherTrace.joint_prefix_bound procedure (digestMention (mentions lambda tau))
      (fun n => (n : ℝ≥0∞) * ((tau + 2 : Nat) : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹)
      (fun log input => ProductOracle.digest_mention_query_bound (mentions lambda tau) (tau + 2)
          (fun input => BAVCChainInputs.mentions_card_le input) log input) budget initial
    rw [RandomOracleMention.sum_range_mul] at hm
    exact hm
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  refine add_le_add ?_ ?_
  · have hc := HashCipherTrace.joint_prefix_bound procedure digestCollision
      (fun n => (n : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹)
      (fun log input => SlopeConsistency.digest_collision_query_bound log input) budget initial
    rw [SlopeConsistency.sum_range_mul_one] at hc
    exact hc
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  exact add_le_add (witnessed_bound hpos procedure budget initial) (unseen_bound S hpos choose procedure budget initial)

end
end SDitH.Proofs.SharedSlopeBound
