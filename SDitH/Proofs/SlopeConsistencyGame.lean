import SDitH.Spec.SlopeConsistencyGame
import SDitH.Proofs.SlopeConsistency
import SDitH.Proofs.HashCipherPipelineSecurity

/-! The assembled slope-consistency bound. A winning run either raised one
of the tau^2 table-dependent mask traps, or a fresh digest hit a mentioned
value, or two fresh digests collided. The three events are bounded by the
trap, mention and collision lemmas, giving
tau^2*budget*2^(-s) + choose(budget,2)*(tau+2)/|Digest| + choose(budget,2)/|Digest|.
The commitment and serializer injectivity hypotheses are explicit; the join
to the cipher-model seed binding is a separate step. -/

namespace SDitH.Proofs.SlopeConsistencyGame

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.SlopeConsistency Spec.SlopeConsistencyGame
open Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.ConsistencyMatrix
open scoped Classical ENNReal BigOperators
noncomputable section

variable {lambda tau kappa s wit rnd : Nat} {State : Type*}

/-- `decide_eq_true` with the decidability instance unified rather than
re-synthesized, for terms whose instance is classical. -/
theorem decide_true_of {p : Prop} {inst : Decidable p} (h : p) : @decide p inst = true := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

theorem maskInput_injective (a b : Digest lambda) (h : maskInput a = maskInput b) : a = b :=
  List.ofFn_injective h

/-- Under uniqueness, the trap vector at a chained claim's mask input is
that claim's slope difference. -/
theorem vectorOf_eq (S : Setting lambda tau kappa s wit rnd)
    (hcommit : ∀ e i, Function.Injective (S.commit e i))
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (table : List Bool → Option (Out lambda s wit rnd)) (hfree : DigestCollisionFree table)
    (c : Claim lambda tau kappa s wit rnd) (hc : ChainIn S.commit S.encoding table c) (e e' : Fin tau) :
    vectorOf S e e' table (maskInput c.auxiliary) = slopeOf S c e - slopeOf S c e' := by
  have h : ∃ c' : Claim lambda tau kappa s wit rnd, ChainIn S.commit S.encoding table c' ∧ maskInput c'.auxiliary = maskInput c.auxiliary :=
    ⟨c, hc, rfl⟩
  rw [vectorOf, dif_pos h]
  obtain ⟨hc', hmask⟩ := Classical.choose_spec h
  have haux : (Classical.choose h).auxiliary = c.auxiliary := maskInput_injective _ _ hmask
  obtain ⟨hsalt, hfull, _, _, hcorr⟩ :=
    SlopeConsistency.chain_unique S.commit S.encoding hcommit hencoding table hfree (Classical.choose h) c hc' hc haux
  funext col
  simp only [Pi.sub_apply, slopeOf]
  rw [SlopeConsistency.slope_congr S.p _ _ S.randomCount S.enough _ c.aux hcorr e col,
    SlopeConsistency.slope_congr S.p _ _ S.randomCount S.enough _ c.aux hcorr e' col, hsalt, hfull]

theorem chainIn_before (S : Setting lambda tau kappa s wit rnd)
    (before table : List Bool → Option (Out lambda s wit rnd)) (hext : Extends before table)
    (c : Claim lambda tau kappa s wit rnd) (hc : ChainIn S.commit S.encoding table c)
    (hpresent : (∀ e, (before (rowString (rows S.commit c e))).isSome) ∧
      (before (outerString c.salt c.rowHashes)).isSome ∧ (before (auxString c.root (tail S.encoding c))).isSome) :
    ChainIn S.commit S.encoding before c := by
  obtain ⟨hrows, ⟨po, hpo, hpo1⟩, ⟨pa, hpa, hpa1⟩⟩ := hc
  obtain ⟨hprows, hpouter, hpaux⟩ := hpresent
  refine ⟨fun e => ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hprows e)
    obtain ⟨pr, hpr, hpr1⟩ := hrows e
    have := hext _ _ hq
    rw [hpr] at this
    exact ⟨q, hq, by rw [← Option.some.inj this]; exact hpr1⟩
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hpouter
    have := hext _ _ hq
    rw [hpo] at this
    exact ⟨q, hq, by rw [← Option.some.inj this]; exact hpo1⟩
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hpaux
    have := hext _ _ hq
    rw [hpa] at this
    exact ⟨q, hq, by rw [← Option.some.inj this]; exact hpa1⟩

/-- A winning run raised a trap, the mention event or the collision event. -/
theorem wins_covered (S : Setting lambda tau kappa s wit rnd)
    (hcommit : ∀ e i, Function.Injective (S.commit e i))
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (hlambda : 0 < lambda) (htau : 0 < tau)
    (procedure : Spec.RandomOracleCollision.Procedure (List Bool) (Out lambda s wit rnd) State)
    (budget : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd)
    (out : Result (List Bool) (Out lambda s wit rnd) State)
    (hout : out ∈ (experiment procedure budget initial).support) (hwin : wins S choose out = true) :
    trapAny S out = true ∨ prefixBad (digestMention (mentions lambda tau)) out.trace = true ∨
      prefixBad digestCollision out.trace = true := by
  by_cases hmention : prefixBad (digestMention (mentions lambda tau)) out.trace = true
  · exact Or.inr (Or.inl hmention)
  by_cases hcoll : prefixBad digestCollision out.trace = true
  · exact Or.inr (Or.inr hcoll)
  left
  obtain ⟨hchain, pair, hpair, e, e', hne, hmask⟩ := of_decide_eq_true hwin
  set c := choose out.state with hc
  have htraced := RandomOracleTrace.experiment_invariants procedure budget initial out hout
  obtain ⟨_, _, hextall, hstoredall⟩ := OracleChain.experiment_ordered procedure budget initial out hout
  obtain ⟨em, hem, hemi, hema, _, hemext⟩ := htraced.1 _ pair hpair
  have hfree : DigestCollisionFree out.table :=
    SlopeConsistency.collision_free_of_not_prefix out.trace out.table htraced hcoll
  have hN : 0 < 2 ^ kappa := Nat.two_pow_pos kappa
  rcases BAVCChainInputs.chain_present_or_mention hlambda htau hN procedure budget initial out hout
    c.salt (rows S.commit c) c.rowHashes c.root (tail S.encoding c) c.auxiliary hchain.1 hchain.2.1 hchain.2.2
    em hem hemi with hpresent | hbad
  · have hcin := chainIn_before S em.before out.table hemext c hchain hpresent
    have hfreeB := SlopeConsistency.collision_free_mono em.before out.table hemext hfree
    have hvec := vectorOf_eq S hcommit hencoding em.before hfreeB c hcin e e'
    rw [trapAny]
    refine decide_true_of ⟨e, e', List.any_eq_true.mpr ⟨em, hem, ?_⟩⟩
    rw [hemi, hema]
    show tableMaskTrap (vectorOf S e e') em.before (maskInput c.auxiliary) pair = true
    rw [tableMaskTrap, Spec.RandomOracleTrap.kernelTrap]
    refine decide_true_of ?_
    rw [hvec]
    refine ⟨sub_ne_zero.mpr hne, fun a => ?_⟩
    rw [ConsistencyMatrix.masked_sub, hmask a, sub_self]
  · exact absurd hbad hmention

theorem trapAny_bound (S : Setting lambda tau kappa s wit rnd)
    (procedure : Spec.RandomOracleCollision.Procedure (List Bool) (Out lambda s wit rnd) State)
    (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map (trapAny S)) true ≤
      (tau : ℝ≥0∞) * tau * (budget * (2 : ℝ≥0∞)⁻¹ ^ s) := by
  have h := ChallengeMixtures.boolean_union_bound (experiment procedure budget initial) (trapAny S)
    (fun pair : Fin tau × Fin tau => fun out => traceBad (tableMaskTrap (vectorOf S pair.1 pair.2)) out.trace) (by
      intro out _ hany
      obtain ⟨e, e', he⟩ := of_decide_eq_true hany
      exact ⟨(e, e'), he⟩)
  refine h.trans ?_
  calc
    _ ≤ ∑ _pair : Fin tau × Fin tau, (budget : ℝ≥0∞) * (Fintype.card (ZMod 2) : ℝ≥0∞)⁻¹ ^ s := by
      apply Finset.sum_le_sum
      intro pair _
      exact ProductOracle.mask_trap_bound procedure (vectorOf S pair.1 pair.2) budget initial
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, ZMod.card]
      push_cast
      ring

/-- The standalone slope-consistency bound. -/
theorem bound (S : Setting lambda tau kappa s wit rnd)
    (hcommit : ∀ e i, Function.Injective (S.commit e i))
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail S.encoding corrections))
    (hlambda : 0 < lambda) (htau : 0 < tau)
    (procedure : Spec.RandomOracleCollision.Procedure (List Bool) (Out lambda s wit rnd) State)
    (budget : Nat) (initial : State) (choose : State → Claim lambda tau kappa s wit rnd) :
    ((experiment procedure budget initial).map (wins S choose)) true ≤
      (tau : ℝ≥0∞) * tau * (budget * (2 : ℝ≥0∞)⁻¹ ^ s) +
        ((budget.choose 2 : ℝ≥0∞) * (tau + 2) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ +
          (budget.choose 2 : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹) := by
  have hcover := HashCipherPipelineSecurity.event_mass_le (experiment procedure budget initial) (wins S choose)
    (fun out => trapAny S out || (prefixBad (digestMention (mentions lambda tau)) out.trace ||
      prefixBad digestCollision out.trace)) (by
      intro out hout hwin
      rcases wins_covered S hcommit hencoding hlambda htau procedure budget initial choose out hout hwin with h | h | h
      · simp [h]
      · simp [h]
      · simp [h])
  refine hcover.trans ?_
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  refine add_le_add (trapAny_bound S procedure budget initial) ?_
  refine (RandomOracleCollision.boolean_or_mass _ _ _).trans ?_
  refine add_le_add ?_ (SlopeConsistency.digest_collision_bound procedure budget initial)
  have hm := ProductOracle.digest_mention_bound procedure (mentions lambda tau) (tau + 2)
    (fun input => BAVCChainInputs.mentions_card_le input) budget initial
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hm

end
end SDitH.Proofs.SlopeConsistencyGame
