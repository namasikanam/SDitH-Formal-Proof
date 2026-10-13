import SDitH.Proofs.TouchSplit
import SDitH.Proofs.TreeDistinct

/-! The assembled touching bound against the joint draw. For the joint draw
of a uniform root and the posterior family, on the pairs whose tree keys
are fresh and distinct, the probability that a continuation of the view
pruned at the signature's hidden keys records one of them is at most the
executions times the root and internal path rates times the expected
number of recorded entries, plus the leaf term (the hits at the hidden
leaves themselves, kept explicit). -/

namespace SDitH.Proofs.TouchAssembly

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys HiddenKeysExchange TreeExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange NodeTouchBound ViewNodeBound RootPosteriorBound RootHonestBound RootTouchBound ViewRootBound
open HiddenTuple HiddenSlice PathUnion AllViewBounds TouchSplit TreeDistinct ProductSwap
open CipherResample ChargeExpect ChargeCutExpect TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w₀ : World lambda s wit rnd) {Sig β : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
  (hidden : Sig → Fin tau → Fin (2 ^ kappa))
  (cont : Sig × World lambda s wit rnd → PMF β) (new : β → List (Entry (Bits lambda) (Bits lambda)))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The mean under the joint draw is the mean over the root of the mean
over the family. -/
theorem mean_rootDraw (H₀ : List (Entry (Bits lambda) (Bits lambda))) (φ : Bits lambda × Family (Bits lambda) (Bits lambda) → ℝ≥0∞) :
    mean (rootDraw H₀) φ = mean (PMF.uniformOfFintype (Bits lambda)) fun r => mean (posterior H₀) fun g => φ (r, g) := by
  unfold rootDraw product
  rw [mean_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [mean_map]

/-- A pair whose tree keys are fresh and distinct. -/
def GoodTree (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : Prop :=
  Distinct S.layout x.2 S.variant salt x.1 (tau * 2 ^ kappa) w₀.cipherHistory

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- Distinctness gives goodness and freshness at the root. -/
theorem goodAllR_of_distinct (hL2 : 2 ≤ tau * 2 ^ kappa) (x : Bits lambda × Family (Bits lambda) (Bits lambda))
    (hd : GoodTree S salt w₀ x) : GoodAllR S salt w₀ x := by
  have hroot : node (treeExpand S.layout x.2 S.variant salt) x.1 1 = x.1 := by
    rw [node]
    simp
  refine ⟨fun c h2 hc => ?_, ?_⟩
  · have := hd.2 c 1 (by omega) hc (by omega) (by omega) (by omega)
    rwa [hroot] at this
  · have := hd.1 1 (by omega) (by omega)
    show S.layout.key x.1 ∉ _
    rwa [hroot] at this

/-- The leaf term: the hits at the hidden leaves over the tuples and the
executions, on the good pairs. -/
def leafTerm : ℝ≥0∞ :=
  ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau, mean (rootDraw w₀.cipherHistory) fun x =>
    indicator (decide (GoodTree S salt w₀ x)) * leafHit S salt witness w₀ post hidden cont new h e x

/-- The sliced expected lengths sum to the expected length. -/
theorem sum_expected (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    ∑ h : Fin tau → Fin (2 ^ kappa),
      expectedNewVR (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new) x =
    expLen S salt witness w₀ post hidden cont new x := by
  have hs := mean_viewPruned_eq_sum S salt witness x.1 post { w₀ with family := x.2 } hidden
    (fun h g => hiddenKeysAll S.layout g S.variant salt x.1 h) (fun v => mean (cont v) fun y => ((new y).length : ℝ≥0∞))
  unfold expLen viewAct
  refine Eq.trans ?_ hs.symm
  refine Finset.sum_congr rfl fun h _ => ?_
  unfold expectedNewVR viewAll
  exact congrArg _ (funext fun v => length_slice hidden h cont new v)

variable (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.layout.input) (hl : 26 ≤ lambda)
  (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
  (hpost : ∀ b, b < tau * 2 ^ kappa → ∀ c x, post (.done (setTree b x c)) = post (.done c))
  (hpos : ∃ g : Family (Bits lambda) (Bits lambda), Matches g w₀.cipherHistory)
  (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key (S.layout.output r) = κ} ≤ c)
  (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.layout.key r = κ} ≤ cKey)
  (hNb : c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
  (hNR : cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))

include hL2 hpost hpos hfiberR hNR in
/-- The root term for a tuple. -/
theorem root_term (h : Fin tau → Fin (2 ^ kappa)) :
    mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
        HitVR S (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new) x) ≤
      (cKey : ℝ≥0∞) / ((Fintype.card (Bits lambda) - cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory)
          (expectedNewVR (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new)) := by
  have hpos' : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  have e : Fin tau := ⟨0, by have := NeZero.pos tau; omega⟩
  have hbound := root_touch_bound_all S salt witness w₀ h post (sliceCont hidden h cont) (sliceNew new) hL2 e
    (fun c x => hpost 1 (by omega) c x) hpos cKey hfiberR
  have hgood : mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
      HitVR S (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new) x) ≤
      mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodAllR S salt w₀ x)) *
        HitVR S (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new) x) := by
    refine mean_le_mean _ _ _ fun x _ => mul_le_mul' ?_ le_rfl
    by_cases hd : GoodTree S salt w₀ x
    · simp [hd, goodAllR_of_distinct S salt w₀ hL2 x hd, indicator]
    · simp [hd, indicator]
  refine hgood.trans ?_
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  refine (ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr (by omega))) (Or.inl (ENNReal.natCast_ne_top _))).mpr ?_
  rw [mul_comm]
  exact hbound

include hL2 hin hl hL hpost hpos hfiber hNb in
/-- The internal node term for a tuple, an execution and a node of the
execution's internal path. -/
theorem node_term (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau) (b : Nat) (hb : b ∈ innerPath (leafAddress e (h e))) :
    mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
        HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont hidden h cont) (sliceNew new) x.2) ≤
      (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) *
        mean (rootDraw w₀.cipherHistory)
          (expectedNewVR (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new)) := by
  have hpos' : 0 < tau * 2 ^ kappa := leafCount_pos (tau := tau) (kappa := kappa)
  have ha := SDitH.Proofs.SeedTree.leafAddress_bounds e (h e)
  have ha1 : 1 < leafAddress e (h e) := by
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
      HitV S salt r (viewAll S salt witness w₀ h post r) b (sliceCont hidden h cont) (sliceNew new) g) ≤
      (c : ℝ≥0∞) / N * mean (posterior w₀.cipherHistory)
        (expectedNewV (viewAll S salt witness w₀ h post r) (sliceCont hidden h cont) (sliceNew new)) := by
    intro r
    have hbound := node_touch_bound_all S salt witness w₀ h post (sliceCont hidden h cont) (sliceNew new) r b hb1 hbk hin hl hL
      e hpath (fun c x => hpost b (by omega) c x) hpos c hfiber
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

include hL2 hin hl hL hpost hpos hfiber hfiberR hNb hNR in
/-- The assembled touching bound against the joint draw: on the good
pairs, the executions times the root and internal path rates times the
expected recorded length, plus the leaf term. -/
theorem touch_assembly (D : Nat) (hD : ∀ (e : Fin tau) (i : Fin (2 ^ kappa)), (innerPath (leafAddress e i)).card ≤ D) :
    mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
        touchAll S salt witness w₀ post hidden cont new x) ≤
      (tau : ℝ≥0∞) *
          ((cKey : ℝ≥0∞) / ((Fintype.card (Bits lambda) - cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) +
            (D : ℝ≥0∞) * ((c : ℝ≥0∞) /
              ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞))) *
          mean (rootDraw w₀.cipherHistory) (expLen S salt witness w₀ post hidden cont new) +
        leafTerm S salt witness w₀ post hidden cont new := by
  set N_b : ℝ≥0∞ := ((Fintype.card (Bits lambda) - (c * ((keysOf w₀.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞)
    with hNb'
  set N_R : ℝ≥0∞ := ((Fintype.card (Bits lambda) - cKey * ((keysOf w₀.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞)
    with hNR'
  set M : (Fin tau → Fin (2 ^ kappa)) → ℝ≥0∞ := fun h => mean (rootDraw w₀.cipherHistory)
    (expectedNewVR (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new)) with hM
  set Lf : (Fin tau → Fin (2 ^ kappa)) → Fin tau → ℝ≥0∞ := fun h e => mean (rootDraw w₀.cipherHistory) fun x =>
    indicator (decide (GoodTree S salt w₀ x)) * leafHit S salt witness w₀ post hidden cont new h e x with hLf
  set A : ℝ≥0∞ := (cKey : ℝ≥0∞) / N_R + (D : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b) with hA
  -- step 1: the pointwise split, distributed over the means
  have h1 : mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
        touchAll S salt witness w₀ post hidden cont new x) ≤
      ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau,
        (mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
            HitVR S (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new) x) +
          Lf h e +
          ∑ b ∈ innerPath (leafAddress e (h e)), mean (rootDraw w₀.cipherHistory) (fun x =>
            indicator (decide (GoodTree S salt w₀ x)) *
              HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont hidden h cont) (sliceNew new) x.2)) := by
    calc _ ≤ mean (rootDraw w₀.cipherHistory) (fun x => indicator (decide (GoodTree S salt w₀ x)) *
          ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau,
            (HitVR S (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new) x +
              leafHit S salt witness w₀ post hidden cont new h e x +
              ∑ b ∈ innerPath (leafAddress e (h e)),
                HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont hidden h cont) (sliceNew new) x.2)) :=
          mean_le_mean _ _ _ fun x _ => mul_le_mul' le_rfl (touchAll_le S salt witness w₀ post hidden cont new hL2 x)
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
          HitVR S (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new) x) +
        Lf h e +
        ∑ b ∈ innerPath (leafAddress e (h e)), mean (rootDraw w₀.cipherHistory) (fun x =>
          indicator (decide (GoodTree S salt w₀ x)) *
            HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont hidden h cont) (sliceNew new) x.2) ≤
      A * M h + Lf h e := by
    intro h e
    have hr := root_term S salt witness w₀ post hidden cont new hL2 hpost hpos cKey hfiberR hNR h
    have hn : ∑ b ∈ innerPath (leafAddress e (h e)), mean (rootDraw w₀.cipherHistory) (fun x =>
        indicator (decide (GoodTree S salt w₀ x)) *
          HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont hidden h cont) (sliceNew new) x.2) ≤
        (D : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b * M h) := by
      calc _ ≤ ∑ b ∈ innerPath (leafAddress e (h e)), (c : ℝ≥0∞) / N_b * M h :=
            Finset.sum_le_sum fun b hb =>
              node_term S salt witness w₀ post hidden cont new hL2 hin hl hL hpost hpos c hfiber hNb h e b hb
        _ = ((innerPath (leafAddress e (h e))).card : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b * M h) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (D : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b * M h) := mul_le_mul' (Nat.cast_le.mpr (hD e (h e))) le_rfl
    calc _ ≤ (cKey : ℝ≥0∞) / N_R * M h + Lf h e + (D : ℝ≥0∞) * ((c : ℝ≥0∞) / N_b * M h) :=
          add_le_add (add_le_add hr le_rfl) hn
      _ = A * M h + Lf h e := by
          rw [hA]
          ring
  -- step 3: the sums
  have hsum : ∑ h : Fin tau → Fin (2 ^ kappa), M h =
      mean (rootDraw w₀.cipherHistory) (expLen S salt witness w₀ post hidden cont new) := by
    rw [hM, sum_mean (rootDraw w₀.cipherHistory) (fun h x =>
      expectedNewVR (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new) x) Finset.univ]
    exact congrArg _ (funext fun x => sum_expected S salt witness w₀ post hidden cont new x)
  have h3 : ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau, (A * M h + Lf h e) =
      (tau : ℝ≥0∞) * A * mean (rootDraw w₀.cipherHistory) (expLen S salt witness w₀ post hidden cont new) +
        leafTerm S salt witness w₀ post hidden cont new := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_assoc]
    rfl
  calc _ ≤ _ := h1
    _ ≤ ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau, (A * M h + Lf h e) :=
        Finset.sum_le_sum fun h _ => Finset.sum_le_sum fun e _ => h2 h e
    _ = _ := h3

end
end SDitH.Proofs.TouchAssembly
