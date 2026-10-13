import SDitH.Proofs.AllViewBounds
import SDitH.Proofs.HiddenSlice
import SDitH.Proofs.PathUnion

/-! Splitting the touching probability for the view-dependent pruning. A
signature's hidden keys are those of all executions' hidden leaves, chosen
from the signature; the probability that a continuation of the view pruned
at them records one of them is at most the sum, over the hidden tuples and
the executions, of the root hit, the leaf hit and the hits at the internal
path nodes, each for the continuation restricted to the tuple. -/

namespace SDitH.Proofs.TouchSplit

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry Matches)
open Spec.RandomOracleTrap (indicator)
open HiddenLeafNode HiddenEntries HiddenKeys HiddenKeysExchange TreeExchange CommitPhaseExchange CommitRunExchange
open OwnViewExchange NodeTouchBound ViewNodeBound RootTouchBound ViewRootBound HiddenTuple HiddenSlice PathUnion
open AllViewBounds CipherResample ChargeExpect ChargeCutExpect TreeStepFresh
open scoped Classical ENNReal

noncomputable section

section Sums

variable {α γ δ : Type*} [Fintype γ]

/-- A mean bounded pointwise by a sum of three kinds of terms is bounded by
the sum of their means. -/
theorem mean_le_triple_sum (p : PMF α) (φ : α → ℝ≥0∞) (A B : γ → α → ℝ≥0∞) (T : γ → Finset δ)
    (C : γ → δ → α → ℝ≥0∞) (h : ∀ a, φ a ≤ ∑ e, (A e a + B e a + ∑ b ∈ T e, C e b a)) :
    mean p φ ≤ ∑ e, (mean p (A e) + mean p (B e) + ∑ b ∈ T e, mean p (C e b)) := by
  calc mean p φ ≤ mean p (fun a => ∑ e, (A e a + B e a + ∑ b ∈ T e, C e b a)) :=
        mean_le_mean _ _ _ fun a _ => h a
    _ = ∑ e, (mean p (A e) + mean p (B e) + ∑ b ∈ T e, mean p (C e b)) := by
        rw [← sum_mean p (fun e a => A e a + B e a + ∑ b ∈ T e, C e b a) Finset.univ]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [mean_add, mean_add, sum_mean p (fun b a => C e b a) (T e)]

end Sums

/-- The internal path of a leaf: the addresses strictly between the leaf
and the root. -/
def innerPath (a : Nat) : Finset Nat := (pathAddresses (a / 2)).toFinset

/-- The sum over the root and the path of a leaf splits into the root, the
leaf and the internal path. -/
theorem sum_pathSet_split (a : Nat) (ha : 1 < a) (F : Nat → ℝ≥0∞) :
    ∑ b ∈ pathSet a, F b = F 1 + F a + ∑ b ∈ innerPath a, F b := by
  unfold pathSet innerPath
  rw [pathAddresses_of_lt ha, List.toFinset_cons, List.toFinset_cons]
  have h1 : (1 : Nat) ∉ insert a (pathAddresses (a / 2)).toFinset := by
    simp only [Finset.mem_insert, List.mem_toFinset, not_or]
    exact ⟨by omega, fun h => by have := (mem_pathAddresses_iff.mp h).1; omega⟩
  have ha' : a ∉ (pathAddresses (a / 2)).toFinset := by
    rw [List.mem_toFinset]
    intro h
    have := le_of_mem_pathAddresses h
    omega
  rw [Finset.sum_insert h1, Finset.sum_insert ha', add_assoc]

/-- An internal path address is above the root and at most half the leaf. -/
theorem innerPath_bounds {a b : Nat} (hb : b ∈ innerPath a) : 1 < b ∧ b ≤ a / 2 := by
  unfold innerPath at hb
  rw [List.mem_toFinset] at hb
  exact ⟨(mem_pathAddresses_iff.mp hb).1, le_of_mem_pathAddresses hb⟩

/-- An internal path address lies on the leaf's path. -/
theorem innerPath_subset {a b : Nat} (ha : 1 < a) (hb : b ∈ innerPath a) : b ∈ pathAddresses a := by
  unfold innerPath at hb
  rw [List.mem_toFinset] at hb
  rw [pathAddresses_of_lt ha]
  exact List.mem_cons_of_mem _ hb

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2)
  (w₀ : World lambda s wit rnd) {Sig β : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
  (hidden : Sig → Fin tau → Fin (2 ^ kappa))
  (cont : Sig × World lambda s wit rnd → PMF β) (new : β → List (Entry (Bits lambda) (Bits lambda)))

/-- The view pruned at the signature's hidden keys, from a pair. -/
def viewAct (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : PMF (Sig × World lambda s wit rnd) :=
  viewPruned S salt witness x.1 post { w₀ with family := x.2 } fun q g => hiddenKeysAll S.layout g S.variant salt x.1 (hidden q)

/-- The probability that the continuation records one of the signature's
hidden keys. -/
def touchAll (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (viewAct S salt witness w₀ post hidden x) fun v => mean (cont v) fun y =>
    indicator (decide (∃ e ∈ new y, e.key ∈ hiddenKeysAll S.layout x.2 S.variant salt x.1 (hidden v.1)))

/-- The expected number of entries the continuation records. -/
def expLen (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (viewAct S salt witness w₀ post hidden x) fun v => mean (cont v) fun y => ((new y).length : ℝ≥0∞)

/-- The leaf hit for a tuple and an execution: the probability, for the
continuation restricted to the tuple, of recording the key of the
execution's hidden leaf. -/
def leafHit (h : Fin tau → Fin (2 ^ kappa)) (e : Fin tau) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) : ℝ≥0∞ :=
  mean (viewAll S salt witness w₀ h post x.1 x.2) fun v => indicator (decide (hidden v.1 = h)) *
    mean (cont v) fun y => indicator (decide (S.layout.key
      (node (treeExpand S.layout x.2 S.variant salt) x.1 (leafAddress e (h e))) ∈ keysOf (new y)))

/-- The touching probability is at most the sum over the tuples and the
executions of the root hit, the leaf hit and the internal path hits. -/
theorem touchAll_le (hL2 : 2 ≤ tau * 2 ^ kappa) (x : Bits lambda × Family (Bits lambda) (Bits lambda)) :
    touchAll S salt witness w₀ post hidden cont new x ≤
      ∑ h : Fin tau → Fin (2 ^ kappa), ∑ e : Fin tau,
        (HitVR S (viewAll S salt witness w₀ h post) (sliceCont hidden h cont) (sliceNew new) x +
          leafHit S salt witness w₀ post hidden cont new h e x +
          ∑ b ∈ innerPath (leafAddress e (h e)),
            HitV S salt x.1 (viewAll S salt witness w₀ h post x.1) b (sliceCont hidden h cont) (sliceNew new) x.2) := by
  have hslice := mean_viewPruned_eq_sum S salt witness x.1 post { w₀ with family := x.2 } hidden
    (fun h g => hiddenKeysAll S.layout g S.variant salt x.1 h) (fun v => mean (cont v) fun y =>
      indicator (decide (∃ e ∈ new y, e.key ∈ hiddenKeysAll S.layout x.2 S.variant salt x.1 (hidden v.1))))
  have htouch : touchAll S salt witness w₀ post hidden cont new x =
      ∑ h : Fin tau → Fin (2 ^ kappa), mean (viewAll S salt witness w₀ h post x.1 x.2) (fun v =>
        indicator (decide (hidden v.1 = h)) * mean (cont v) fun y =>
          indicator (decide (∃ e ∈ new y, e.key ∈ hiddenKeysAll S.layout x.2 S.variant salt x.1 (hidden v.1)))) := by
    unfold touchAll viewAct
    convert hslice using 6
    exact decide_eq_decide.mpr Iff.rfl
  rw [htouch]
  refine Finset.sum_le_sum fun h _ => ?_
  have hroot : node (treeExpand S.layout x.2 S.variant salt) x.1 1 = x.1 := by
    rw [node]
    simp
  -- the pointwise bound on the recorded entries
  have hpt : ∀ N : List (Entry (Bits lambda) (Bits lambda)),
      indicator (decide (∃ e ∈ N, e.key ∈ hiddenKeysAll S.layout x.2 S.variant salt x.1 h)) ≤
        ∑ e : Fin tau, (indicator (decide (S.layout.key x.1 ∈ keysOf N)) +
          indicator (decide (S.layout.key (node (treeExpand S.layout x.2 S.variant salt) x.1 (leafAddress e (h e))) ∈ keysOf N)) +
          ∑ b ∈ innerPath (leafAddress e (h e)),
            indicator (decide (S.layout.key (S.layout.output (nodeBlock S.layout x.2 S.variant salt x.1 b)) ∈ keysOf N))) := by
    intro N
    refine (touchAll_le_sum S.layout x.2 S.variant salt x.1 h N).trans (Finset.sum_le_sum fun e _ => ?_)
    have ha : 1 < leafAddress e (h e) := by
      have := SDitH.Proofs.SeedTree.leafAddress_bounds e (h e)
      unfold leafAddress at this ⊢
      omega
    refine (touch_le_sum S.layout x.2 S.variant salt x.1 (leafAddress e (h e)) N).trans (le_of_eq ?_)
    rw [sum_pathSet_split _ ha, hroot]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [node_eq_output_nodeBlock S.layout x.2 S.variant salt x.1 b (innerPath_bounds hb).1]
  -- the pointwise bound on the views
  have hv : ∀ v : Sig × World lambda s wit rnd,
      indicator (decide (hidden v.1 = h)) * mean (cont v) (fun y =>
        indicator (decide (∃ e ∈ new y, e.key ∈ hiddenKeysAll S.layout x.2 S.variant salt x.1 (hidden v.1)))) ≤
      ∑ e : Fin tau, (hitWeightR S (sliceCont hidden h cont) (sliceNew new) x.1 v +
        indicator (decide (hidden v.1 = h)) * mean (cont v) (fun y => indicator (decide (S.layout.key
          (node (treeExpand S.layout x.2 S.variant salt) x.1 (leafAddress e (h e))) ∈ keysOf (new y)))) +
        ∑ b ∈ innerPath (leafAddress e (h e)),
          hitWeight S (sliceCont hidden h cont) (sliceNew new) (nodeBlock S.layout x.2 S.variant salt x.1 b) v) := by
    intro v
    by_cases hvh : hidden v.1 = h
    · simp only [hitWeightR_slice, hitWeight_slice, hvh, decide_true, RandomOracleTrap.indicator_true, one_mul]
      unfold hitWeightR hitWeight
      exact mean_le_triple_sum (cont v) _ (fun e y => indicator (decide (S.layout.key x.1 ∈ keysOf (new y))))
        (fun e y => indicator (decide (S.layout.key
          (node (treeExpand S.layout x.2 S.variant salt) x.1 (leafAddress e (h e))) ∈ keysOf (new y))))
        (fun e => innerPath (leafAddress e (h e)))
        (fun e b y => indicator (decide (S.layout.key (S.layout.output (nodeBlock S.layout x.2 S.variant salt x.1 b)) ∈
          keysOf (new y))))
        (fun y => hpt (new y))
    · simp only [hvh, decide_false, RandomOracleTrap.indicator_false, zero_mul]
      exact zero_le _
  exact mean_le_triple_sum (viewAll S salt witness w₀ h post x.1 x.2) _
    (fun e => hitWeightR S (sliceCont hidden h cont) (sliceNew new) x.1)
    (fun e v => indicator (decide (hidden v.1 = h)) * mean (cont v) (fun y => indicator (decide (S.layout.key
      (node (treeExpand S.layout x.2 S.variant salt) x.1 (leafAddress e (h e))) ∈ keysOf (new y)))))
    (fun e => innerPath (leafAddress e (h e)))
    (fun e b => hitWeight S (sliceCont hidden h cont) (sliceNew new) (nodeBlock S.layout x.2 S.variant salt x.1 b)) hv

end
end SDitH.Proofs.TouchSplit
