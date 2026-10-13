import SDitH.Spec.BLCSeedFold
import SDitH.Proofs.BLCRecompute
import SDitH.Proofs.BLCArithmetic

/-! Under the extractor's explicit bindings, Algorithm 12's fold at any
hidden index is an affine function of that index's Gray row, with slope and
intercept computed from the seed vector and the transmitted corrections.
Two hidden indices therefore differ by the slope times the row difference.
For the honest Algorithm-10 auxiliary data on the signer's own seeds, the
slope is the committed common accumulator. These are deterministic
identities; no source binding is repaired and no witness validity is claimed. -/

namespace SDitH.Proofs.BLCSeedFold

open Spec.BLCRecompute Spec.BLCSeedFold Spec.DomainSeparation
open scoped BigOperators

variable {lambda tau kappa s wit rnd : Nat}

theorem foldExecution_extracted (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (nodes : Spec.BAVC.NodesBinding lambda tau (2 ^ kappa)) (full : Fin tau → Fin (2 ^ kappa) → Bits lambda)
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount) (e : Fin tau) :
    foldExecution p salt (extractedBindings nodes full) aux hidden randomCount enough e =
      .ok ⟨0, some fun c j => affine p salt full randomCount enough aux e (hidden e) c j⟩ := by
  rw [extractedBindings, BLCRecompute.foldExecution_sum]
  congr 3
  funext c j
  have hs : (∑ i ∈ Finset.univ.erase (hidden e),
      Spec.BLCCommit.randomTable p salt full randomCount enough e i c *
        (Spec.GrayCode.grayFieldRow (hidden e) j - Spec.GrayCode.grayFieldRow i j)) =
      ∑ i, Spec.BLCCommit.randomTable p salt full randomCount enough e i c *
        (Spec.GrayCode.grayFieldRow (hidden e) j - Spec.GrayCode.grayFieldRow i j) := by
    rw [Finset.sum_erase _ (by simp)]
  simp only [Pi.zero_apply, zero_add, hs, affine, Spec.BLCSeedFold.slope, intercept, folded, correctionTerm,
    BLC.fold_acc_formula, BLC.fold_base_formula]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hneg (a : ZMod 2) : -a = a := CharTwo.neg_eq a
  split_ifs
  · simp only [sub_eq_add_neg, hneg]
    ring
  · simp only [sub_eq_add_neg, hneg]
    ring

/-- Reaching the line-21 operands under the extractor's bindings gives the
affine share matrix at the expanded hidden indices. -/
theorem prepare_extracted_Q {F : Type} [Field F] [DecidableEq F] {B wpow : Nat}
    (p : Spec.BLCCommit.Primitives lambda tau kappa (lambda + B) wit rnd)
    (salt : Bits lambda) (aux : Spec.BLCCommit.Auxiliary tau (lambda + B) wit rnd)
    (decomposition : Spec.BLCRetry.Counter × Spec.BAVC.Opening lambda tau)
    (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
    (nodes : Spec.BAVC.NodesBinding lambda tau (2 ^ kappa)) (full : Fin tau → Fin (2 ^ kappa) → Bits lambda)
    (randomCount consistencyCount : Nat)
    (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount)
    (state : ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd)
    (h : prepareWithBindings p salt aux decomposition expand encode Topen (extractedBindings nodes full)
      randomCount consistencyCount hrandom hconsistency = .ok state) (c : Fin ((lambda + B) + (wit + rnd)))
    (e : Fin tau) (j : Fin kappa) :
    state.Q c e j = affine p salt full randomCount hrandom aux e ((expand decomposition.1).hidden e) c j := by
  obtain ⟨_, _, reconstruction, folded, shares, _, hf, hc, rfl⟩ :=
    (BLCRecompute.prepare_ok_iff p salt aux decomposition expand encode Topen (extractedBindings nodes full)
      randomCount consistencyCount hrandom hconsistency state).mp h
  have hrow := BLCRecompute.foldExecutions_coordinate p salt (extractedBindings nodes full) aux
    (expand decomposition.1).hidden randomCount hrandom tau le_rfl folded hf e.val e.isLt
  rw [foldExecution_extracted] at hrow
  have hshare := BLCRecompute.collectShares_coordinate folded shares hc e.val e.isLt
  have hval : folded[e.val] = ⟨0, some fun c j =>
      affine p salt full randomCount hrandom aux ⟨e.val, e.isLt⟩ ((expand decomposition.1).hidden ⟨e.val, e.isLt⟩) c j⟩ :=
    (Except.ok.inj hrow).symm
  rw [hval] at hshare
  have hfin : (⟨e.val, e.isLt⟩ : Fin tau) = e := Fin.eta e e.isLt
  simp only [hfin] at hshare
  have hs := Option.some.inj hshare
  show shares[e.val] c j = _
  rw [← hs]

/-- Two hidden indices at one execution differ by the slope times the Gray
row difference; the intercept cancels in characteristic two. -/
theorem affine_difference (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (e : Fin tau) (i i' : Fin (2 ^ kappa)) (c : Fin (s + (wit + rnd))) (j : Fin kappa) :
    affine p salt full randomCount enough aux e i c j + affine p salt full randomCount enough aux e i' c j =
      slope p salt full randomCount enough aux e c *
        (Spec.GrayCode.grayFieldRow i j + Spec.GrayCode.grayFieldRow i' j) := by
  simp only [affine]
  have hself := CharTwo.add_self_eq_zero (intercept p salt full randomCount enough e c j)
  linear_combination hself

/-- With the honest Algorithm-10 corrections computed from the same seeds,
the slope is the committed common accumulator of execution zero. This is a
statement about honest auxiliary data, not about an adversarial signature. -/
theorem honest_slope {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {B : Nat} [NeZero tau]
    (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa (lambda + B) wit rnd)
    (salt root : Bits lambda) (witness : Fin wit → ZMod 2)
    (randomCount consistencyCount : Nat)
    (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount) (e : Fin tau) (c : Fin ((lambda + B) + (wit + rnd))) :
    slope p salt (Spec.BAVC.commit (Spec.SeedPrimitives.bavcPrimitives (tau * (2 ^ kappa)) p.grinding p.encStar p.hash) salt root).seeds
      randomCount hrandom
      (Spec.BLCCommit.commit xi p salt root witness randomCount consistencyCount hrandom hconsistency).auxiliary e c =
    Spec.BLC.commonAcc Spec.GrayCode.grayFieldRow
      (Spec.BLCCommit.randomTable p salt
        (Spec.BAVC.commit (Spec.SeedPrimitives.bavcPrimitives (tau * (2 ^ kappa)) p.grinding p.encStar p.hash) salt root).seeds
        randomCount hrandom) c := by
  simp only [Spec.BLCSeedFold.slope, folded, correctionTerm, Spec.BLCCommit.commit, Spec.BLCCommit.positiveCorrections]
  split_ifs with he
  · have hidx : Spec.BLCCommit.positiveIndex (correctionIndex e he) = e := by
      apply Fin.ext
      simp only [Spec.BLCCommit.positiveIndex, correctionIndex]
      omega
    rw [hidx]
    simp only [Spec.BLC.correction, Pi.sub_apply, Spec.BLC.foldExecutions]
    ring
  · have hzero : e = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    subst hzero
    simp only [Spec.BLC.commonAcc, Spec.BLC.foldExecutions, add_zero]

end SDitH.Proofs.BLCSeedFold
