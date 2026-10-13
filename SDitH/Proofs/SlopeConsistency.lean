import SDitH.Spec.SlopeConsistency
import SDitH.Proofs.BAVCChainInputs
import SDitH.Proofs.BLCBinding

/-! Injectivity of the chain strings, uniqueness of a chained claim with a
given auxiliary digest in a digest-collision-free table (under explicit
injective commitment and serializer hypotheses), and the digest-collision
prefix event: its bound choose(budget,2)/|Digest| and the fact that two
distinct stored inputs with equal digest components raise it. -/

namespace SDitH.Proofs.SlopeConsistency

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.SlopeConsistency
open Spec.RandomOracleTrace Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open scoped Classical ENNReal BigOperators
noncomputable section

variable {lambda tau kappa s wit rnd : Nat} {M : Type*}

theorem auxString_inj (root root' : Digest lambda) (tail tail' : List Bool)
    (h : auxString root tail = auxString root' tail') : root = root' ∧ tail = tail' := by
  have he := List.append_cancel_left h
  obtain ⟨hroot, htail⟩ := List.append_inj he (by simp)
  exact ⟨List.ofFn_injective hroot, htail⟩

theorem outerString_inj (salt salt' : Seed lambda) (rowHashes rowHashes' : Fin tau → Digest lambda)
    (h : outerString salt rowHashes = outerString salt' rowHashes') : salt = salt' ∧ rowHashes = rowHashes' := by
  have he := List.append_cancel_left h
  obtain ⟨hsalt, hrows⟩ := List.append_inj he (by simp)
  exact ⟨List.ofFn_injective hsalt, BAVCBinding.serializeArray_injective hrows⟩

theorem rowString_inj {N : Nat} (row row' : Fin N → Digest lambda) (h : rowString row = rowString row') : row = row' :=
  BAVCBinding.serializeArray_injective (List.append_cancel_left h)

/-- In a digest-collision-free table, two chained claims with the same
auxiliary digest agree on every component the slopes depend on, given
injective commitments and serializer. The plain check and witness
correction are not part of the chain and are not determined. -/
theorem chain_unique (commit : Spec.SlopeConsistency.Commit lambda tau kappa)
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s)
    (hcommit : ∀ e i, Function.Injective (commit e i))
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail encoding corrections))
    (table : List Bool → Option (Digest lambda × M)) (hfree : DigestCollisionFree table)
    (c c' : Claim lambda tau kappa s wit rnd) (hc : ChainIn commit encoding table c)
    (hc' : ChainIn commit encoding table c') (haux : c.auxiliary = c'.auxiliary) :
    c.salt = c'.salt ∧ c.full = c'.full ∧ c.rowHashes = c'.rowHashes ∧ c.root = c'.root ∧
      c.aux.corrections = c'.aux.corrections := by
  obtain ⟨hrows, ⟨po, hpo, hpo1⟩, ⟨pa, hpa, hpa1⟩⟩ := hc
  obtain ⟨hrows', ⟨po', hpo', hpo1'⟩, ⟨pa', hpa', hpa1'⟩⟩ := hc'
  have hauxEq : auxString c.root (tail encoding c) = auxString c'.root (tail encoding c') :=
    hfree _ _ pa pa' hpa hpa' (by rw [hpa1, hpa1', haux])
  obtain ⟨hroot, htail⟩ := auxString_inj _ _ _ _ hauxEq
  have hcorr : c.aux.corrections = c'.aux.corrections := hencoding htail
  have houterEq : outerString c.salt c.rowHashes = outerString c'.salt c'.rowHashes :=
    hfree _ _ po po' hpo hpo' (by rw [hpo1, hpo1', hroot])
  obtain ⟨hsalt, hrowHashes⟩ := outerString_inj _ _ _ _ houterEq
  have hfull : c.full = c'.full := by
    funext e i
    obtain ⟨pr, hpr, hpr1⟩ := hrows e
    obtain ⟨pr', hpr', hpr1'⟩ := hrows' e
    have hrowEq : rowString (rows commit c e) = rowString (rows commit c' e) :=
      hfree _ _ pr pr' hpr hpr' (by rw [hpr1, hpr1', hrowHashes])
    have hrow := rowString_inj _ _ hrowEq
    exact hcommit e i (congrFun hrow i)
  exact ⟨hsalt, hfull, hrowHashes, hroot, hcorr⟩

/-- The slope depends on the auxiliary data only through its corrections. -/
theorem slope_congr (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux aux' : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (h : aux.corrections = aux'.corrections) (e : Fin tau) (c : Fin (s + (wit + rnd))) :
    Spec.BLCSeedFold.slope p salt full randomCount enough aux e c =
      Spec.BLCSeedFold.slope p salt full randomCount enough aux' e c := by
  simp only [Spec.BLCSeedFold.slope, Spec.BLCSeedFold.correctionTerm, h]

section Collision

variable [Fintype M] [Nonempty M] {State : Type*}

theorem digest_collision_query_bound (log : List (Entry (List Bool) (Digest lambda × M))) (input : List Bool) :
    ((PMF.uniformOfFintype (Digest lambda × M)).map (digestCollision log input)) true ≤
      (log.length : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ := by
  have h := ChallengeMixtures.boolean_union_bound (PMF.uniformOfFintype (Digest lambda × M))
    (digestCollision log input)
    (fun i : Fin log.length => fun answer => decide (answer.1 ∈ ({(log[i]).answer.1} : Finset (Digest lambda)))) (by
      intro answer _ hhit
      obtain ⟨entry, hmem, he⟩ := List.any_eq_true.mp hhit
      obtain ⟨index, hlt, hindex⟩ := List.mem_iff_getElem.mp hmem
      refine ⟨⟨index, hlt⟩, ?_⟩
      simp only [Fin.getElem_fin, hindex, Finset.mem_singleton]
      simpa [eq_comm] using he)
  refine h.trans ?_
  calc
    _ ≤ ∑ _i : Fin log.length, (1 : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      rw [ProductOracle.uniform_fst_mem_mass]
      simp
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]

theorem sum_range_mul_one (n : Nat) (c : ℝ≥0∞) :
    ∑ i ∈ Finset.range n, (i : ℝ≥0∞) * c = (n.choose 2 : ℝ≥0∞) * c := by
  rw [← Finset.sum_mul]
  congr 1
  rw [← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]

/-- Some fresh digest equals an earlier fresh digest with probability at
most choose(budget,2)/|Digest|. -/
theorem digest_collision_bound (procedure : Spec.RandomOracleCollision.Procedure (List Bool) (Digest lambda × M) State)
    (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map (fun out => prefixBad digestCollision out.trace)) true ≤
      (budget.choose 2 : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ := by
  have h := RandomOracleMention.experiment_prefix_bound procedure digestCollision
    (fun n => (n : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹)
    (fun log input => digest_collision_query_bound log input) budget initial
  rw [sum_range_mul_one] at h
  exact h

omit [Fintype M] [Nonempty M] in
/-- Two distinct stored inputs with equal digest components raise the event. -/
theorem stored_collision_implies_prefix (log : List (Entry (List Bool) (Digest lambda × M)))
    (table : List Bool → Option (Digest lambda × M)) (htraced : Traced table log)
    (x y : List Bool) (px py : Digest lambda × M) (hx : table x = some px) (hy : table y = some py)
    (hxy : x ≠ y) (hd : px.1 = py.1) : prefixBad digestCollision log = true := by
  obtain ⟨ex, hex, hexi, hexa, _, _⟩ := htraced.1 x px hx
  obtain ⟨ey, hey, heyi, heya, _, _⟩ := htraced.1 y py hy
  obtain ⟨a, ha, hxa⟩ := List.mem_iff_getElem.mp hex
  obtain ⟨b, hb, hyb⟩ := List.mem_iff_getElem.mp hey
  have hab : a ≠ b := by
    intro h
    subst h
    rw [hxa] at hyb
    subst hyb
    exact hxy (hexi.symm.trans heyi)
  rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
  · apply OracleChain.prefixBad_of_index _ log a ha
    rw [hxa]
    refine List.any_eq_true.mpr ⟨ey, ?_, ?_⟩
    · rw [← hyb]
      exact OracleChain.getElem_mem_drop log a b hb hlt
    · rw [heya, hexa, hd]
      exact decide_eq_true rfl
  · apply OracleChain.prefixBad_of_index _ log b hb
    rw [hyb]
    refine List.any_eq_true.mpr ⟨ex, ?_, ?_⟩
    · rw [← hxa]
      exact OracleChain.getElem_mem_drop log b a ha hgt
    · rw [hexa, heya, hd]
      exact decide_eq_true rfl

omit [Fintype M] [Nonempty M] in
theorem collision_free_of_not_prefix (log : List (Entry (List Bool) (Digest lambda × M)))
    (table : List Bool → Option (Digest lambda × M)) (htraced : Traced table log)
    (hno : ¬ prefixBad digestCollision log = true) : DigestCollisionFree table := by
  intro x y px py hx hy hd
  by_contra hxy
  exact hno (stored_collision_implies_prefix log table htraced x y px py hx hy hxy hd)

omit [Fintype M] [Nonempty M] in
/-- Collision freeness restricts to any earlier table. -/
theorem collision_free_mono (small large : List Bool → Option (Digest lambda × M))
    (hext : Extends small large) (hfree : DigestCollisionFree large) : DigestCollisionFree small :=
  fun x y px py hx hy hd => hfree x y px py (hext x px hx) (hext y py hy) hd

end Collision

end
end SDitH.Proofs.SlopeConsistency
