import SDitH.Proofs.TouchTotal

/-! The touching bound for a constant hidden tuple. The assembled touching
bound asked the post-processing to be invariant under setting any internal
node of the committed tree, which the simulated post-processing is not: its
opening reveals the co-path of the hidden tuple. For a fixed hidden tuple,
read from the digest, the invariance is only needed at the root and on the
internal paths of that tuple's leaves; the slices of other tuples vanish. -/

namespace SDitH.Proofs.TouchConst

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys HiddenKeysExchange TreeExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange NodeTouchBound ViewNodeBound RootPosteriorBound RootHonestBound RootTouchBound ViewRootBound
open HiddenTuple HiddenSlice PathUnion AllViewBounds TouchSplit TreeDistinct ProductSwap
open CipherResample ChargeExpect ChargeCutExpect TreeStepFresh TouchAssembly TouchTotal
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w₀ : World lambda s wit rnd) {Sig β : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
  (hidden : Sig → Fin tau → Fin (2 ^ kappa))
  (cont : Sig × World lambda s wit rnd → PMF β) (new : β → List (Entry (Bits lambda) (Bits lambda)))
variable (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (h₀ : Fin tau → Fin (2 ^ kappa))
  (hpostP : ∀ b, b = 1 ∨ (∃ e : Fin tau, b ∈ innerPath (leafAddress e (h₀ e))) →
    ∀ c x, post (.done (setTree b x c)) = post (.done c))
  (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory)
  (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
  (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ cKey)
  (hNb : c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
  (hNR : cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))

/-- The root hit of a slice other than the constant tuple vanishes. -/
theorem hitVR_const_ne (h : Fin tau → Fin (2 ^ kappa)) (hh : h ≠ h₀) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    HitVR S (viewAll S salt witness w₀ h post) (sliceCont (fun _ => h₀) h cont) (sliceNew new) x = 0 := by
  unfold HitVR hitWeightR
  refine (mean_congr_support _ _ (fun _ => 0) fun v _ => ?_).trans (mean_const _ _)
  have hne : ¬ ((fun _ : Sig => h₀) v.1 = h) := fun e => hh e.symm
  simp only [sliceCont, hne, if_false, mean_pure, sliceNew, keysOf, List.map_nil, List.toFinset_nil, Finset.notMem_empty,
    decide_false, RandomOracleTrap.indicator_false]

/-- The node hit of a slice other than the constant tuple vanishes. -/
theorem hitV_const_ne (h : Fin tau → Fin (2 ^ kappa)) (hh : h ≠ h₀) (x : Bits lambda × Family (Bits lambda) (Bits lambda))
    (b : Nat) :
    HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont (fun _ => h₀) h cont) (sliceNew new) x.2 = 0 := by
  unfold HitV hitWeight
  refine (mean_congr_support _ _ (fun _ => 0) fun v _ => ?_).trans (mean_const _ _)
  have hne : ¬ ((fun _ : Sig => h₀) v.1 = h) := fun e => hh e.symm
  simp only [sliceCont, hne, if_false, mean_pure, sliceNew, keysOf, List.map_nil, List.toFinset_nil, Finset.notMem_empty,
    decide_false, RandomOracleTrap.indicator_false]

include hL2 hpostP hpos hfiberR hNR in
/-- The root term for the constant tuple. -/
theorem root_term_const :
    mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
        HitVR S (viewAll S salt witness w₀ h₀ post) (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new) x) ≤
      (cKey : ℝ≥0∞) / ((Fintype.card (Bits lambda) - cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory)
          (expectedNewVR (viewAll S salt witness w₀ h₀ post) (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new)) := by
  have hpos' : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  have e : Fin tau := ⟨0, by have := NeZero.pos tau; omega⟩
  have hbound := root_touch_bound_all S salt witness w₀ h₀ post (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new) hL2 e
    (fun c x => hpostP 1 (Or.inl rfl) c x) hpos cKey hfiberR
  have hgood : mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
      HitVR S (viewAll S salt witness w₀ h₀ post) (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new) x) ≤
      mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodAllR S salt w₀ x)) *
        HitVR S (viewAll S salt witness w₀ h₀ post) (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new) x) := by
    refine mean_le_mean _ _ _ fun x _ => mul_le_mul' ?_ le_rfl
    by_cases hd : GoodTree S salt w₀ x
    · simp [hd, goodAllR_of_distinct S salt w₀ hL2 x hd, indicator]
    · simp [hd, indicator]
  refine hgood.trans ?_
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  refine (ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr (by omega))) (Or.inl (ENNReal.natCast_ne_top _))).mpr ?_
  rw [mul_comm]
  exact hbound

include hL2 hin hl hL hpostP hpos hfiber hNb in
/-- The internal node term for the constant tuple, an execution and a node
of the execution's internal path. -/
theorem node_term_const (e : Fin tau) (b : Nat) (hb : b ∈ innerPath (leafAddress e (h₀ e))) :
    mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
        HitV S salt x.1 (viewAll S salt witness w₀ h₀ post x.1) b (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new) x.2) ≤
      (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory)
          (expectedNewVR (viewAll S salt witness w₀ h₀ post) (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new)) := by
  have hpos' : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  have ha := SDitH.Proofs.SeedTree.leafAddress_bounds e (h₀ e)
  have ha1 : 1 < leafAddress e (h₀ e) := by
    unfold leafAddress at ha ⊢
    omega
  obtain ⟨hb1, hb2⟩ := innerPath_bounds hb
  have hbk : b ≤ tau * 2 ^ kappa - 1 := by omega
  have hbL : b < 2 * (tau * 2 ^ kappa) := by omega
  have hpath := innerPath_subset ha1 hb
  set N : ℝ≥0∞ := ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞)
    with hN
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNtop : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hper : ∀ r : Bits lambda, mean (posterior w₀.cipherHistory) (fun g => indicator (decide (GoodAll S salt w₀ r b g)) *
      HitV S salt r (viewAll S salt witness w₀ h₀ post r) b (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new) g) ≤
      (c : ℝ≥0∞) / N * mean (posterior w₀.cipherHistory)
        (expectedNewV (viewAll S salt witness w₀ h₀ post r) (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new)) := by
    intro r
    have hbound := node_touch_bound_all S salt witness w₀ h₀ post (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new) r b hb1 hbk hin hl hL
      e hpath (fun c x => hpostP b (Or.inr ⟨e, hb⟩) c x) hpos c hfiber
    rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
    refine (ENNReal.le_div_iff_mul_le (Or.inl hN0) (Or.inl hNtop)).mpr ?_
    rw [mul_comm]
    exact hbound
  rw [mean_rootDraw, mean_rootDraw, ← mean_mul_left]
  refine mean_le_mean _ _ _ fun r _ => ?_
  refine le_trans (mean_le_mean _ _ _ fun g _ => mul_le_mul' ?_ le_rfl) (hper r)
  by_cases hd : GoodTree S salt w₀ (r, g)
  · simp [hd, goodAll_of_distinct S salt w₀ r g hd b hb1 hbL, indicator]
  · simp [hd, indicator]

include hL2 hin hl hL hpostP hpos hfiber hfiberR hNb hNR in
/-- The assembled touching bound against the joint draw for the constant
tuple: on the good pairs, the executions times the root and internal path rates times the
expected recorded length, plus the leaf term. -/
theorem touch_assembly_const (D : Nat) (hD : ∀ (e : Fin tau) (i : Fin (2 ^ kappa)), (innerPath (leafAddress e i)).card ≤ D) :
    mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
        touchAll S salt witness w₀ post (fun _ => h₀) cont new x) ≤
      (tau : ℝ≥0∞) *
          ((cKey : ℝ≥0∞) / ((Fintype.card (Bits lambda) - cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) +
            (D : ℝ≥0∞) * ((c : ℝ≥0∞) /
              ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞))) *
          mean (rootDraw w₀.cipherHistory) (expLen S salt witness w₀ post (fun _ => h₀) cont new) +
        leafTerm S salt witness w₀ post (fun _ => h₀) cont new := by
  set N_b : ℝ≥0∞ := ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞)
    with hNb'
  set N_R : ℝ≥0∞ := ((Fintype.card (Bits lambda) - cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞)
    with hNR'
  set M : (Fin tau → Fin (2 ^ kappa)) → ℝ≥0∞ := fun h => mean (rootDraw w₀.cipherHistory)
    (expectedNewVR (viewAll S salt witness w₀ h post) (sliceCont (fun _ => h₀) h cont) (sliceNew new)) with hM
  set Lf : (Fin tau → Fin (2 ^ kappa)) → Fin tau → ℝ≥0∞ := fun h e => mean (rootDraw w₀.cipherHistory) fun x =>
    indicator (decide (GoodTree S salt w₀ x)) * leafHit S salt witness w₀ post (fun _ => h₀) cont new h e x with hLf
  set A : ℝ≥0∞ := (cKey : ℝ≥0∞) / N_R + (D : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b) with hA
  -- step 1: the pointwise split, distributed over the means
  have h1 : mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
        touchAll S salt witness w₀ post (fun _ => h₀) cont new x) ≤
      ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau,
        (mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
            HitVR S (viewAll S salt witness w₀ h post) (sliceCont (fun _ => h₀) h cont) (sliceNew new) x) +
          Lf h e +
          ∑ b ∈ innerPath (leafAddress e (h e)), mean (rootDraw w₀.cipherHistory) (fun x =>
            indicator (decide (GoodTree S salt w₀ x)) *
              HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont (fun _ => h₀) h cont) (sliceNew new) x.2)) := by
    calc _ ≤ mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
          ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau,
            (HitVR S (viewAll S salt witness w₀ h post) (sliceCont (fun _ => h₀) h cont) (sliceNew new) x +
              leafHit S salt witness w₀ post (fun _ => h₀) cont new h e x +
              ∑ b ∈ innerPath (leafAddress e (h e)),
                HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont (fun _ => h₀) h cont) (sliceNew new) x.2)) :=
          mean_le_mean _ _ _ fun x _ => mul_le_mul' le_rfl (touchAll_le S salt witness w₀ post (fun _ => h₀) cont new hL2 x)
      _ = _ := by
          simp only [Finset.mul_sum, mul_add]
          rw [← sum_mean (rootDraw w₀.cipherHistory) (fun h x => ∑ e : Fin tau, _) Finset.univ]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [← sum_mean (rootDraw w₀.cipherHistory) (fun e x => _) Finset.univ]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [mean_add, mean_add, ← sum_mean (rootDraw w₀.cipherHistory) (fun b x => _) (innerPath (leafAddress e (h e)))]
  -- step 2: the root and node bounds
  have h2 : ∀ (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau),
      mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
          HitVR S (viewAll S salt witness w₀ h post) (sliceCont (fun _ => h₀) h cont) (sliceNew new) x) +
        Lf h e +
        ∑ b ∈ innerPath (leafAddress e (h e)), mean (rootDraw w₀.cipherHistory) (fun x =>
          indicator (decide (GoodTree S salt w₀ x)) *
            HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont (fun _ => h₀) h cont) (sliceNew new) x.2) ≤
      A * M h + Lf h e := by
    intro h e
    by_cases hh : h = h₀
    · rw [hh]
      have hr := root_term_const S salt witness w₀ post cont new hL2 h₀ hpostP hpos cKey hfiberR hNR
      have hn : ∑ b ∈ innerPath (leafAddress e (h₀ e)), mean (rootDraw w₀.cipherHistory) (fun x =>
          indicator (decide (GoodTree S salt w₀ x)) *
            HitV S salt x.1 (viewAll S salt witness w₀ h₀ post x.1) b (sliceCont (fun _ => h₀) h₀ cont) (sliceNew new) x.2) ≤
          (D : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b * M h₀) := by
        calc _ ≤ ∑ b ∈ innerPath (leafAddress e (h₀ e)), (c : ℝ≥0∞) / N_b * M h₀ :=
              Finset.sum_le_sum fun b hb =>
                node_term_const S salt witness w₀ post cont new hL2 hin hl hL h₀ hpostP hpos c hfiber hNb e b hb
          _ = ((innerPath (leafAddress e (h₀ e))).card : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b * M h₀) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (D : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b * M h₀) := mul_le_mul' (Nat.cast_le.mpr (hD e (h₀ e))) le_rfl
      calc _ ≤ (cKey : ℝ≥0∞) / N_R * M h₀ + Lf h₀ e + (D : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b * M h₀) :=
            add_le_add (add_le_add hr le_rfl) hn
        _ = A * M h₀ + Lf h₀ e := by
            rw [hA]
            ring
    · have hR : mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
          HitVR S (viewAll S salt witness w₀ h post) (sliceCont (fun _ => h₀) h cont) (sliceNew new) x) = 0 := by
        refine (mean_congr_support _ _ (fun _ => 0) fun x _ => ?_).trans (mean_const _ _)
        rw [hitVR_const_ne S salt witness w₀ post cont new h₀ h hh x, mul_zero]
      have hN : ∀ b ∈ innerPath (leafAddress e (h e)), mean (rootDraw w₀.cipherHistory) (fun x =>
          indicator (decide (GoodTree S salt w₀ x)) *
            HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont (fun _ => h₀) h cont) (sliceNew new) x.2) = 0 := by
        intro b _
        refine (mean_congr_support _ _ (fun _ => 0) fun x _ => ?_).trans (mean_const _ _)
        rw [hitV_const_ne S salt witness w₀ post cont new h₀ h hh x b, mul_zero]
      rw [hR, Finset.sum_eq_zero hN, zero_add, add_zero]
      exact le_add_self
  -- step 3: the sums
  have hsum : ∑ h : Fin tau → Fin (2 ^ kappa), M h =
      mean (rootDraw w₀.cipherHistory) (expLen S salt witness w₀ post (fun _ => h₀) cont new) := by
    rw [hM, sum_mean (rootDraw w₀.cipherHistory) (fun h x =>
      expectedNewVR (viewAll S salt witness w₀ h post) (sliceCont (fun _ => h₀) h cont) (sliceNew new) x) Finset.univ]
    exact congrArg _ (funext fun x => sum_expected S salt witness w₀ post (fun _ => h₀) cont new x)
  have h3 : ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau, (A * M h + Lf h e) =
      (tau : ℝ≥0∞) * A * mean (rootDraw w₀.cipherHistory) (expLen S salt witness w₀ post (fun _ => h₀) cont new) +
        leafTerm S salt witness w₀ post (fun _ => h₀) cont new := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_assoc]
    rfl
  calc _ ≤ _ := h1
    _ ≤ ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau, (A * M h + Lf h e) :=
        Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun e _ => h2 h e
    _ = _ := h3

include hpostP in
/-- The total touching bound under the joint draw: the distinctness
failure probability, plus the assembled bound with the internal path
depth the binary logarithm of the leaf count, plus the leaf term. -/
theorem touch_total_const (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ cKey)
    (hNb : c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (q : Nat) (hq : w₀.cipherHistory.length + 2 * (tau * 2 ^ kappa - 1) + 1 ≤ q) :
    mean (rootDraw w₀.cipherHistory) (touchAll S salt witness w₀ post (fun _ => h₀) cont new) ≤
      (((cKey * (keysOf w₀.cipherHistory).card : Nat) : ℝ≥0∞) * (Fintype.card (Bits lambda) : ℝ≥0∞)⁻¹ +
        (tau * 2 ^ kappa - 1 : ℕ) *
          (2 * (((c * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) /
              ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) +
            (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞))) +
      ((tau : ℝ≥0∞) *
          ((cKey : ℝ≥0∞) / ((Fintype.card (Bits lambda) - cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) +
            (Nat.log 2 (tau * 2 ^ kappa) : ℝ≥0∞) * ((c : ℝ≥0∞) /
              ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞))) *
          mean (rootDraw w₀.cipherHistory) (expLen S salt witness w₀ post (fun _ => h₀) cont new) +
        leafTerm S salt witness w₀ post (fun _ => h₀) cont new) := by
  calc mean (rootDraw w₀.cipherHistory) (touchAll S salt witness w₀ post (fun _ => h₀) cont new)
      ≤ mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (¬ GoodTree S salt w₀ x)) +
          indicator (decide (GoodTree S salt w₀ x)) * touchAll S salt witness w₀ post (fun _ => h₀) cont new x) := by
        refine mean_le_mean _ _ _ fun x _ => ?_
        by_cases hd : GoodTree S salt w₀ x
        · simp [hd, indicator]
        · simp only [hd, not_false_eq_true, decide_true, decide_false, RandomOracleTrap.indicator_true,
            RandomOracleTrap.indicator_false, zero_mul, add_zero]
          exact touchAll_le_one S salt witness w₀ post (fun _ => h₀) cont new x
    _ = mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (¬ GoodTree S salt w₀ x))) +
          mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
            touchAll S salt witness w₀ post (fun _ => h₀) cont new x) := mean_add _ _ _
    _ ≤ _ := add_le_add
        (bad_tree_le S salt w₀ hin hl hL (by omega) c hfiber cKey hfiberR hpos q hq)
        (touch_assembly_const S salt witness w₀ post cont new hL2 hin hl hL h₀ hpostP hpos c hfiber cKey hfiberR hNb hNR
          (Nat.log 2 (tau * 2 ^ kappa)) fun e i => innerPath_card_le e i)

end
end SDitH.Proofs.TouchConst
