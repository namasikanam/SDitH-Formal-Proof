import SDitH.Spec.SharedSlopeExec
import SDitH.Proofs.SharedSlopeBound
import SDitH.Proofs.HashCipherTracePipeline
import SDitH.Proofs.HashCipherPipelineSecurity
import SDitH.Proofs.HashCipherEvaluation

/-! Executing the named claim's commitments discharges the queried
condition: the program is bounded by its call count, every call's entry is
in the final cipher history, and the final state carries the claim. The
five-event coverage and the bound then hold for the two-phase experiment
with budget q + 2*tau*2^kappa. -/

namespace SDitH.Proofs.SharedSlopeExec

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.SlopeConsistency
open Spec.SlopeConsistencyGame (Out)
open Spec.SharedSlopeGame Spec.SharedSlopeExec Spec.SeedPrimitives Spec.SeedPairing Spec.IdealCipher
open Spec.IdealCipherPairCollision Spec.RandomOracleMention Spec.ProductOracle Spec.ConsistencyMatrix
open Spec.OracleChain Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.RandomOracleTrace (Traced Extends traceBad)
open Spec.HashCipherTrace (forget)
open scoped Classical ENNReal BigOperators
noncomputable section

variable {lambda tau kappa s wit rnd : Nat} {State : Type*}

theorem mem_allPairs (e : Fin tau) (i : Fin (2 ^ kappa)) : (e, i) ∈ allPairs tau kappa := by
  simp [allPairs, List.mem_flatMap, List.mem_map, List.mem_finRange]

theorem callsProgram_bounded (S : Setting lambda tau kappa s wit rnd) (c : Claim lambda tau kappa s wit rnd)
    (pairs : List (Fin tau × Fin (2 ^ kappa))) : Bounded (2 * pairs.length) (callsProgram S c pairs) := by
  induction pairs with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨e, i⟩ := p
    rw [List.length_cons, Nat.mul_succ]
    intro _ _
    exact ih

theorem commitProgram_bounded (S : Setting lambda tau kappa s wit rnd) (c : Claim lambda tau kappa s wit rnd) :
    Bounded (commitBudget tau kappa) (commitProgram S c) :=
  callsProgram_bounded S c (allPairs tau kappa)

theorem calls_evaluates (S : Setting lambda tau kappa s wit rnd) (c : Claim lambda tau kappa s wit rnd)
    (family : CipherFamily lambda) (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : History lambda)
    (pairs : List (Fin tau × Fin (2 ^ kappa))) (value : Claim lambda tau kappa s wit rnd)
    (h : Evaluates family table ciphers (callsProgram S c pairs) value) :
    value = c ∧ ∀ p ∈ pairs, seedEntry family (c.full p.1 p.2) (input0 S.variant c.salt p.1 p.2) ∈ ciphers ∧
      seedEntry family (c.full p.1 p.2) (companion (input0 S.variant c.salt p.1 p.2)) ∈ ciphers := by
  induction pairs generalizing value with
  | nil =>
    cases h
    exact ⟨rfl, fun p hp => by simp at hp⟩
  | cons p rest ih =>
    obtain ⟨e, i⟩ := p
    cases h with
    | cipher _ _ _ recorded1 tail1 =>
      cases tail1 with
      | cipher _ _ _ recorded2 tail2 =>
        obtain ⟨hv, hrest⟩ := ih value tail2
        refine ⟨hv, fun q hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨recorded1, recorded2⟩
        · exact hrest q hq

/-- The final state carries the claim and every commitment call is recorded. -/
theorem exec_claim (S : Setting lambda tau kappa s wit rnd)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd)
    (joint : CipherFamily lambda × ExecRes lambda tau kappa s wit rnd)
    (hout : joint ∈ (jointExperiment S adversary q initial choose).support) :
    ∃ c, joint.2.state = .done c ∧ Queried S joint.1 joint.2.cipherHistory c := by
  have hmem : (joint.1, forget joint.2) ∈
      (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (commitBudget tau kappa)
        (fun state => commitProgram S (choose state))).support := by
    rw [← HashCipherTracePipeline.joint_forget]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨joint, hout, rfl⟩
  obtain ⟨start, _, tail, htail, heq⟩ := HashCipherPipeline.joint_decompose adversary q initial procedure
    (commitBudget tau kappa) (fun state => commitProgram S (choose state)) _ hmem
  obtain ⟨value, hstate, heval⟩ := HashCipherEvaluation.run_evaluates joint.1 _ (commitBudget tau kappa)
    (commitProgram_bounded S (choose start.state)) start.hashTable start.hashHistory start.cipherHistory tail htail
  obtain ⟨hv, hcalls⟩ := calls_evaluates S (choose start.state) joint.1 tail.hashTable tail.cipherHistory
    (allPairs tau kappa) value heval
  subst hv
  have hstate' : joint.2.state = .done (choose start.state) := by
    have := congrArg Spec.HashCipher.Result.state heq
    simpa [forget, Spec.HashCipher.markHash] using this.trans hstate
  have hhist : joint.2.cipherHistory = tail.cipherHistory := by
    have := congrArg Spec.HashCipher.Result.cipherHistory heq
    simpa [forget, Spec.HashCipher.markHash] using this
  refine ⟨choose start.state, hstate', fun e i => ?_⟩
  rw [hhist]
  exact hcalls (e, i) (mem_allPairs e i)

theorem joint_matches (S : Setting lambda tau kappa s wit rnd)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd)
    (joint : CipherFamily lambda × ExecRes lambda tau kappa s wit rnd)
    (hout : joint ∈ (jointExperiment S adversary q initial choose).support) :
    Matches joint.1 joint.2.cipherHistory := by
  have hmem : (joint.1, forget joint.2) ∈
      (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (commitBudget tau kappa)
        (fun state => commitProgram S (choose state))).support := by
    rw [← HashCipherTracePipeline.joint_forget]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨joint, hout, rfl⟩
  exact (HashCipherPipeline.invariants adversary q initial procedure (commitBudget tau kappa)
    (fun state => commitProgram S (choose state)) _ hmem).2.1

/-- Coverage from the invariants, for an explicit claim with recorded calls. -/
theorem covered_core (S : Setting lambda tau kappa s wit rnd)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (hlambda : 26 ≤ lambda) (htau : 0 < tau) (hcount : 4 * leafCount tau kappa ≤ 2 ^ 24)
    (family : CipherFamily lambda) (out : Spec.HashCipherTrace.Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (htraced : Traced out.hashTable out.trace) (hord : Ordered out.trace) (hfresh : Fresh out.trace)
    (hmatches : Matches family out.cipherHistory) (c : Claim lambda tau kappa s wit rnd)
    (hqueried : Queried S family out.cipherHistory c) (hchain : ChainIn' S family out.hashTable c)
    (pair : Out lambda s wit rnd) (hpair : out.hashTable (maskInput c.auxiliary) = some pair)
    (e e' : Fin tau) (hne : slopeOf S c e ≠ slopeOf S c e')
    (hmask : ∀ a, masked pair.2 (slopeOf S c e) a = masked pair.2 (slopeOf S c e') a) :
    trapAny S (family, out) = true ∨ prefixBad (digestMention (mentions lambda tau)) out.trace = true ∨
      prefixBad digestCollision out.trace = true ∨ witnessed (family, out) = true ∨
      SharedSlopeBound.unseenEvent S (fun _ : Unit => c) family () out.cipherHistory = true := by
  by_cases hmention : prefixBad (digestMention (mentions lambda tau)) out.trace = true
  · exact Or.inr (Or.inl hmention)
  by_cases hcoll : prefixBad digestCollision out.trace = true
  · exact Or.inr (Or.inr (Or.inl hcoll))
  by_cases hlocal : NoCollisionAt S family c
  · left
    obtain ⟨em, hem, hemi, hema, _, hemext⟩ := htraced.1 _ pair hpair
    have hfree : DigestCollisionFree out.hashTable :=
      SlopeConsistency.collision_free_of_not_prefix out.trace out.hashTable htraced hcoll
    have hN : 0 < 2 ^ kappa := Nat.two_pow_pos kappa
    rcases SharedSlopeGame.chain_present_or_mention_of_invariants (by omega) htau hN out.trace out.hashTable hord hfresh htraced
      c.salt (rows (commitOf S.variant family c.salt) c) c.rowHashes c.root (tail S.encoding c) c.auxiliary
      hchain.1 hchain.2.1 hchain.2.2 em hem hemi with hpresent | hbad
    · have hcin := SharedSlopeGame.chainIn_before S family em.before out.hashTable hemext c hchain hpresent
      have hfreeB := SlopeConsistency.collision_free_mono em.before out.hashTable hemext hfree
      have hvec := SharedSlopeGame.vectorOf_eq S family hencoding em.before hfreeB c hlocal hcin e e'
      rw [trapAny]
      refine SlopeConsistencyGame.decide_true_of ⟨e, e', List.any_eq_true.mpr ⟨em, hem, ?_⟩⟩
      rw [hemi, hema]
      show tableMaskTrap (vectorOf S family e e') em.before (maskInput c.auxiliary) pair = true
      rw [tableMaskTrap, Spec.RandomOracleTrap.kernelTrap]
      refine SlopeConsistencyGame.decide_true_of ?_
      rw [hvec]
      refine ⟨sub_ne_zero.mpr hne, fun a => ?_⟩
      rw [ConsistencyMatrix.masked_sub, hmask a, sub_self]
    · exact absurd hbad hmention
  · rcases SharedSlopeGame.collision_split S hlambda hcount family out.cipherHistory hmatches c hqueried hlocal with hw | hu
    · exact Or.inr (Or.inr (Or.inr (Or.inl (SlopeConsistencyGame.decide_true_of hw))))
    · obtain ⟨e, i, seed, hne', hu0, hu1, h0, h1⟩ := hu
      obtain ⟨hq0, hq1⟩ := hqueried e i
      exact Or.inr (Or.inr (Or.inr (Or.inr (SlopeConsistencyGame.decide_true_of
        ⟨e, i, seed, _, _, hne', hu0, hu1, hq0, hq1, h0, h1⟩))))

theorem winsExec_covered (S : Setting lambda tau kappa s wit rnd)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (hlambda : 26 ≤ lambda) (htau : 0 < tau) (hcount : 4 * leafCount tau kappa ≤ 2 ^ 24)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd)
    (joint : CipherFamily lambda × ExecRes lambda tau kappa s wit rnd)
    (hout : joint ∈ (jointExperiment S adversary q initial choose).support) (hwin : winsExec S joint = true) :
    trapAny S joint = true ∨ prefixBad (digestMention (mentions lambda tau)) joint.2.trace = true ∨
      prefixBad digestCollision joint.2.trace = true ∨ witnessed joint = true ∨
      unseenMatch S claimAt joint = true := by
  obtain ⟨c, hstate, hqueried⟩ := exec_claim S adversary q initial choose joint hout
  have hclaim : claimOf joint.2.state = some c := by rw [hstate]; rfl
  have hwin' : ChainIn' S joint.1 joint.2.hashTable c ∧
      ∃ pair, joint.2.hashTable (maskInput c.auxiliary) = some pair ∧
        ∃ e e', slopeOf S c e ≠ slopeOf S c e' ∧
          ∀ a, masked pair.2 (slopeOf S c e) a = masked pair.2 (slopeOf S c e') a := by
    unfold winsExec at hwin
    rw [hclaim] at hwin
    exact of_decide_eq_true hwin
  obtain ⟨hchain, pair, hpair, e, e', hne, hmask⟩ := hwin'
  obtain ⟨htraced, hord, hfresh, _, _⟩ := HashCipherTracePipeline.joint_invariants adversary q initial procedure
    (commitBudget tau kappa) (fun state => commitProgram S (choose state)) joint hout
  have hmatches := joint_matches S adversary q initial choose joint hout
  have hcore := covered_core S hencoding hlambda htau hcount joint.1 joint.2 htraced hord hfresh hmatches c hqueried
    hchain pair hpair e e' hne hmask
  have hat : claimAt joint.2.state = c := by simp [claimAt, hclaim]
  rcases hcore with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [SharedSlopeBound.unseenMatch_eq]
    simp only [SharedSlopeBound.unseenEvent, hat] at h ⊢
    exact h

/-- Two-phase version of the final-world posterior bound. -/
theorem pipeline_final_bound {Input Digest Key Block A B : Type*} [Fintype Digest] [Nonempty Digest]
    [Fintype Key] [Fintype Block]
    (first : Spec.HashCipher.Procedure Input Digest Key Block A) (second : Spec.HashCipher.Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) (E : Family Key Block → B → List (Entry Key Block) → Bool) (epsilon : ℝ≥0∞) (Q : Nat)
    (hE : ∀ (st : B) (w : World Key Block), w.history.length ≤ Q →
      ((PMF.uniformOfFintype (Candidates w)).map (fun family => E family.val st w.history)) true ≤ epsilon)
    (q : Nat) (state : A) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (world : World Key Block) (hlen : world.history.length + q + k ≤ Q) :
    ((Spec.HashCipherPipeline.runPosterior first second k next q state table hashes world).map
      (fun joint => E joint.1 joint.2.state joint.2.cipherHistory)) true ≤ epsilon := by
  induction q generalizing state table hashes world with
  | zero =>
    simp only [Spec.HashCipherPipeline.runPosterior]
    exact SharedSlopeBound.runPosterior_final_bound second E epsilon Q hE k (next state) table hashes world (by omega)
  | succ q ih =>
    simp only [Spec.HashCipherPipeline.runPosterior, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop =>
      exact SharedSlopeBound.runPosterior_final_bound second E epsilon Q hE k (next state) table hashes world (by omega)
    | hash input advance =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Spec.HashCipher.markJoint, Spec.HashCipher.markHash]
      apply ChallengeMixtures.bind_true_le
      intro result _
      exact ih (advance result.1) result.2 ((input, result.1) :: hashes) world (by omega)
    | cipher request advance =>
      simp only [PMF.map_bind]
      apply ChallengeMixtures.bind_true_le
      intro result hr
      have hlen' : result.2.history.length = world.history.length + 1 := by
        obtain ⟨family, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
        subst heq
        simp [Spec.IdealCipher.observe]
      exact ih (advance result.1) table hashes result.2 (by omega)

theorem unseen_bound (S : Setting lambda tau kappa s wit rnd) (hlambda : 0 < lambda)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd) :
    ((jointExperiment S adversary q initial choose).map (unseenMatch S claimAt)) true ≤
      SharedSlopeBound.unseenCost lambda tau kappa (q + commitBudget tau kappa) := by
  have hmap : (jointExperiment S adversary q initial choose).map (unseenMatch S claimAt) =
      (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (commitBudget tau kappa)
        (fun state => commitProgram S (choose state))).map
        (fun joint => SharedSlopeBound.unseenEvent S claimAt joint.1 joint.2.state joint.2.cipherHistory) := by
    rw [jointExperiment, ← HashCipherTracePipeline.joint_forget, PMF.map_comp]
    congr 1
  rw [hmap, ← HashCipherPipeline.experiments_eq]
  refine pipeline_final_bound adversary procedure (commitBudget tau kappa) _ (SharedSlopeBound.unseenEvent S claimAt)
    (SharedSlopeBound.unseenCost lambda tau kappa (q + commitBudget tau kappa)) (q + commitBudget tau kappa) ?_
    q initial (fun _ => none) [] Spec.IdealCipher.empty (by simp [Spec.IdealCipher.empty])
  intro st w hw
  rw [SharedSlopeBound.uniform_congr _ (inferInstance : Fintype (Candidates w))]
  exact SharedSlopeBound.unseen_fixed_world_bound S hlambda claimAt st w _ hw

theorem witnessed_bound (S : Setting lambda tau kappa s wit rnd) (hlambda : 0 < lambda)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd) :
    ((jointExperiment S adversary q initial choose).map witnessed) true ≤
      ((q + commitBudget tau kappa).choose 2 : ℝ≥0∞) *
        IdealCipherPairAdaptive.pairCost (Bits lambda) 1 (q + commitBudget tau kappa) := by
  have hmap : (jointExperiment S adversary q initial choose).map witnessed =
      (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (commitBudget tau kappa)
        (fun state => commitProgram S (choose state))).map (Spec.HashCipher.cipherEvent id companion) := by
    rw [jointExperiment, ← HashCipherTracePipeline.joint_forget, PMF.map_comp]
    rfl
  rw [hmap]
  exact HashCipherPipelineSecurity.pair_bound adversary q initial procedure (commitBudget tau kappa)
    (fun state => commitProgram S (choose state)) id companion SeedPairing.companion_involutive
    (SeedPairing.companion_ne hlambda) 1 (fun target => IdealCipherUnseenMatch.target_card_one target)

theorem trapAny_bound (S : Setting lambda tau kappa s wit rnd)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd) :
    ((jointExperiment S adversary q initial choose).map (trapAny S)) true ≤
      (tau : ℝ≥0∞) * tau * ((q + commitBudget tau kappa : Nat) * (2 : ℝ≥0∞)⁻¹ ^ s) := by
  have h := ChallengeMixtures.boolean_union_bound (jointExperiment S adversary q initial choose) (trapAny S)
    (fun pair : Fin tau × Fin tau => fun joint =>
      traceBad (tableMaskTrap (vectorOf S joint.1 pair.1 pair.2)) joint.2.trace) (by
      intro joint _ hany
      obtain ⟨e, e', he⟩ := of_decide_eq_true hany
      exact ⟨(e, e'), he⟩)
  refine h.trans ?_
  calc
    _ ≤ ∑ _pair : Fin tau × Fin tau, ((q + commitBudget tau kappa : Nat) : ℝ≥0∞) * (Fintype.card (ZMod 2) : ℝ≥0∞)⁻¹ ^ s := by
      apply Finset.sum_le_sum
      intro pair _
      have := HashCipherTracePipeline.joint_trace_bound_family adversary q initial procedure (commitBudget tau kappa)
        (fun state => commitProgram S (choose state)) (fun family => tableMaskTrap (vectorOf S family pair.1 pair.2)) _
        (fun family table input => ProductOracle.uniform_mask_trap_le (vectorOf S family pair.1 pair.2) table input)
      simpa only [Nat.cast_add] using this
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, ZMod.card]
      push_cast
      ring

theorem epsilon_monotone (m : Nat) (c : ℝ≥0∞) : Monotone (fun n : Nat => (n : ℝ≥0∞) * m * c) := by
  intro a b hab
  exact mul_le_mul_left (mul_le_mul_left (Nat.cast_le.mpr hab) _) _

/-- The slope-consistency bound with the queried condition discharged by
execution. The budget is q + 2*tau*2^kappa, counting the commitment calls. -/
theorem bound (S : Setting lambda tau kappa s wit rnd)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (hlambda : 26 ≤ lambda) (htau : 0 < tau) (hcount : 4 * leafCount tau kappa ≤ 2 ^ 24)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd) :
    ((jointExperiment S adversary q initial choose).map (winsExec S)) true ≤
      (tau : ℝ≥0∞) * tau * ((q + commitBudget tau kappa : Nat) * (2 : ℝ≥0∞)⁻¹ ^ s) +
        (((q + commitBudget tau kappa).choose 2 : ℝ≥0∞) * ((tau + 2 : Nat) : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ +
          (((q + commitBudget tau kappa).choose 2 : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ +
            (((q + commitBudget tau kappa).choose 2 : ℝ≥0∞) *
                IdealCipherPairAdaptive.pairCost (Bits lambda) 1 (q + commitBudget tau kappa) +
              SharedSlopeBound.unseenCost lambda tau kappa (q + commitBudget tau kappa)))) := by
  have hpos : 0 < lambda := by omega
  have hcover := HashCipherPipelineSecurity.event_mass_le (jointExperiment S adversary q initial choose) (winsExec S)
    (fun joint => trapAny S joint || (prefixBad (digestMention (mentions lambda tau)) joint.2.trace ||
      (prefixBad digestCollision joint.2.trace || (witnessed joint || unseenMatch S claimAt joint)))) (by
      intro joint hout hwin
      rcases winsExec_covered S hencoding hlambda htau hcount adversary q initial choose joint hout hwin
        with h | h | h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h])
  refine hcover.trans ?_
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  refine add_le_add (trapAny_bound S adversary q initial choose) ?_
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  refine add_le_add ?_ ?_
  · have hm := HashCipherTracePipeline.joint_prefix_bound adversary q initial procedure (commitBudget tau kappa)
      (fun state => commitProgram S (choose state)) (digestMention (mentions lambda tau))
      (fun n => (n : ℝ≥0∞) * ((tau + 2 : Nat) : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹)
      (epsilon_monotone (tau + 2) _)
      (fun log input => ProductOracle.digest_mention_query_bound (mentions lambda tau) (tau + 2)
          (fun input => BAVCChainInputs.mentions_card_le input) log input)
    rw [RandomOracleMention.sum_range_mul] at hm
    exact hm
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  refine add_le_add ?_ ?_
  · have hc := HashCipherTracePipeline.joint_prefix_bound adversary q initial procedure (commitBudget tau kappa)
      (fun state => commitProgram S (choose state)) digestCollision
      (fun n => (n : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹)
      (by
        intro a b hab
        exact mul_le_mul_left (Nat.cast_le.mpr hab) _)
      (fun log input => SlopeConsistency.digest_collision_query_bound log input)
    rw [SlopeConsistency.sum_range_mul_one] at hc
    exact hc
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  exact add_le_add (witnessed_bound S hpos adversary q initial choose) (unseen_bound S hpos adversary q initial choose)

end
end SDitH.Proofs.SharedSlopeExec
