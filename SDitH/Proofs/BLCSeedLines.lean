import SDitH.Spec.BLCSeedLines
import SDitH.Proofs.BLCSeedFold

/-! psi of the affine share matrix splits into per-execution slope terms plus
the intercept; with a constant slope the suffix witness value is affine in
delta with constant term the correction plus that slope. Under the candidate
binary reading of line 21, two challenges differing at one Gray bit of an
execution force the masked slope of that execution to equal the transmitted
plain check. These are deterministic identities, not a soundness theorem. -/

namespace SDitH.Proofs.BLCSeedLines

open Spec.BLCRecompute Spec.BLCSeedFold Spec.BLCSeedLines Spec.DomainSeparation
open scoped BigOperators

variable {lambda tau kappa s wit rnd : Nat}

theorem psi_affine {F : Type*} [CommRing F] [Algebra (ZMod 2) F] (xi : F)
    (slopes : Fin tau → ZMod 2) (hidden : Fin tau → Fin (2 ^ kappa)) (I : Fin tau → Fin kappa → ZMod 2) :
    Spec.BLC.psi xi (fun e j => slopes e * Spec.GrayCode.grayFieldRow (hidden e) j + I e j) =
      ∑ e, algebraMap (ZMod 2) F (slopes e) * rowPsi xi hidden e + Spec.BLC.psi xi I := by
  simp only [BLC.psi_formula, rowPsi, map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem psi_affine_constant {F : Type*} [CommRing F] [Algebra (ZMod 2) F] (xi : F)
    (u : ZMod 2) (hidden : Fin tau → Fin (2 ^ kappa)) (I : Fin tau → Fin kappa → ZMod 2) :
    Spec.BLC.psi xi (fun e j => u * Spec.GrayCode.grayFieldRow (hidden e) j + I e j) =
      algebraMap (ZMod 2) F u * Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden) +
        Spec.BLC.psi xi I :=
  BLC.psi_common_line xi u (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden) I

section Suffix

variable {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {B wpow : Nat}
  (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa (lambda + B) wit rnd)
  (salt : Bits lambda) (aux : Spec.BLCCommit.Auxiliary tau (lambda + B) wit rnd)
  (decomposition : Spec.BLCRetry.Counter × Spec.BAVC.Opening lambda tau)
  (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
  (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
  (nodes : Spec.BAVC.NodesBinding lambda tau (2 ^ kappa)) (full : Fin tau → Fin (2 ^ kappa) → Bits lambda)
  (randomCount consistencyCount : Nat)
  (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
  (hconsistency : wit + rnd ≤ 8 * consistencyCount)
  (hashLines : LinesHashInput lambda tau kappa (lambda + B) → Spec.BLCCommit.Digest lambda)
  (state : ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd)
  (h : prepareWithBindings p salt aux decomposition expand encode Topen (extractedBindings nodes full)
    randomCount consistencyCount hrandom hconsistency = .ok state)

omit [Algebra (ZMod 2) F] in
include h in
theorem state_Q : state.Q = shareMatrix p salt full randomCount hrandom aux (expand decomposition.1).hidden := by
  funext c e j
  exact BLCSeedFold.prepare_extracted_Q p salt aux decomposition expand encode Topen nodes full
    randomCount consistencyCount hrandom hconsistency state h c e j

omit [Algebra (ZMod 2) F] in
include h in
theorem state_auxiliary : state.auxiliary = aux := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ :=
    (BLCRecompute.prepare_ok_iff p salt aux decomposition expand encode Topen (extractedBindings nodes full)
      randomCount consistencyCount hrandom hconsistency state).mp h
  rfl

include h in
/-- The suffix witness value: correction plus delta times the per-execution
slope terms and the intercept psi. -/
theorem suffix_witness_extracted (base : Fin (lambda + B) → Fin tau → Fin kappa → ZMod 2) (j : Fin wit) :
    (suffix xi hashLines state base).witness j =
      algebraMap (ZMod 2) F (aux.witnessCorrection j) + state.delta *
        (∑ e, algebraMap (ZMod 2) F (slope p salt full randomCount hrandom aux e (Spec.BLC.witnessIndex j)) *
            rowPsi xi (expand decomposition.1).hidden e +
          Spec.BLC.psi xi (interceptMatrix p salt full randomCount hrandom (Spec.BLC.witnessIndex j))) := by
  rw [(BLCRecompute.suffix_values xi hashLines state base).2.1 j, state_auxiliary p salt aux decomposition expand encode
    Topen nodes full randomCount consistencyCount hrandom hconsistency state h,
    state_Q p salt aux decomposition expand encode Topen nodes full randomCount consistencyCount hrandom hconsistency state h]
  have hQ : shareMatrix p salt full randomCount hrandom aux (expand decomposition.1).hidden (Spec.BLC.witnessIndex j) =
      fun e j' => slope p salt full randomCount hrandom aux e (Spec.BLC.witnessIndex j) *
        Spec.GrayCode.grayFieldRow ((expand decomposition.1).hidden e) j' +
        interceptMatrix p salt full randomCount hrandom (Spec.BLC.witnessIndex j) e j' := by
    funext e j'
    rfl
  rw [hQ, psi_affine]

include h in
theorem suffix_randomness_extracted (base : Fin (lambda + B) → Fin tau → Fin kappa → ZMod 2) (j : Fin rnd) :
    (suffix xi hashLines state base).randomness j =
      state.delta *
        (∑ e, algebraMap (ZMod 2) F (slope p salt full randomCount hrandom aux e (Spec.BLC.randomnessIndex j)) *
            rowPsi xi (expand decomposition.1).hidden e +
          Spec.BLC.psi xi (interceptMatrix p salt full randomCount hrandom (Spec.BLC.randomnessIndex j))) := by
  rw [(BLCRecompute.suffix_values xi hashLines state base).2.2.1 j,
    state_Q p salt aux decomposition expand encode Topen nodes full randomCount consistencyCount hrandom hconsistency state h]
  have hQ : shareMatrix p salt full randomCount hrandom aux (expand decomposition.1).hidden (Spec.BLC.randomnessIndex j) =
      fun e j' => slope p salt full randomCount hrandom aux e (Spec.BLC.randomnessIndex j) *
        Spec.GrayCode.grayFieldRow ((expand decomposition.1).hidden e) j' +
        interceptMatrix p salt full randomCount hrandom (Spec.BLC.randomnessIndex j) e j' := by
    funext e j'
    rfl
  rw [hQ, psi_affine]

include h in
/-- With a constant slope u across executions and the Gray merge as the
header encoding, the witness value is affine in delta with constant term
correction plus u. For honest auxiliary data u is the committed accumulator. -/
theorem suffix_witness_constant_slope (base : Fin (lambda + B) → Fin tau → Fin kappa → ZMod 2) (j : Fin wit)
    (u : ZMod 2) (hu : ∀ e, slope p salt full randomCount hrandom aux e (Spec.BLC.witnessIndex j) = u)
    (hencode : encode = fun hidden => Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden)) :
    (suffix xi hashLines state base).witness j =
      algebraMap (ZMod 2) F (aux.witnessCorrection j + u) +
        state.delta * Spec.BLC.psi xi (interceptMatrix p salt full randomCount hrandom (Spec.BLC.witnessIndex j)) := by
  rw [(BLCRecompute.suffix_values xi hashLines state base).2.1 j, state_auxiliary p salt aux decomposition expand encode
    Topen nodes full randomCount consistencyCount hrandom hconsistency state h,
    state_Q p salt aux decomposition expand encode Topen nodes full randomCount consistencyCount hrandom hconsistency state h]
  obtain ⟨hinv, hdelta, hne⟩ := BLCRecompute.prepare_delta_nonzero p salt aux decomposition expand encode Topen
    (extractedBindings nodes full) randomCount consistencyCount hrandom hconsistency state h
  have hQ : shareMatrix p salt full randomCount hrandom aux (expand decomposition.1).hidden (Spec.BLC.witnessIndex j) =
      fun e j' => u * Spec.GrayCode.grayFieldRow ((expand decomposition.1).hidden e) j' +
        interceptMatrix p salt full randomCount hrandom (Spec.BLC.witnessIndex j) e j' := by
    funext e j'
    show slope p salt full randomCount hrandom aux e (Spec.BLC.witnessIndex j) * _ + _ = _
    rw [hu]
    rfl
  have hd : encode (expand decomposition.1).hidden ≠ 0 := by
    intro h0
    apply hne
    rw [hdelta, hinv, h0, inv_zero]
  have hmerge : state.delta * Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow (expand decomposition.1).hidden) = 1 := by
    rw [hdelta, hinv]
    have hd' : Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow (expand decomposition.1).hidden) ≠ 0 := by
      rw [hencode] at hd
      exact hd
    rw [hencode]
    exact inv_mul_cancel₀ hd'
  rw [hQ, psi_affine_constant, mul_add, ← mul_assoc, map_add,
    mul_comm state.delta (algebraMap (ZMod 2) F u), mul_assoc, hmerge, mul_one, add_assoc]

end Suffix

theorem consistencyColumns_affine (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (hidden : Fin tau → Fin (2 ^ kappa))
    (a : Fin s) (e : Fin tau) (j : Fin kappa) :
    Spec.BLC.consistencyColumns M (shareMatrix p salt full randomCount enough aux hidden) a e j =
      maskedSlope p salt full randomCount enough aux M e a * Spec.GrayCode.grayFieldRow (hidden e) j +
        Spec.BLC.consistencyColumns M (interceptMatrix p salt full randomCount enough) a e j := by
  simp only [Spec.BLC.consistencyColumns, shareMatrix, affine, interceptMatrix, maskedSlope, Finset.sum_mul,
    mul_add, Finset.sum_add_distrib, mul_assoc]

theorem zmod2_distinct_sub (x y : ZMod 2) (h : x ≠ y) : x - y = 1 := by
  revert x y
  decide

/-- Under the candidate line-21 reading at two hidden vectors whose Gray rows
differ at bit j of execution e, the masked slope of e equals the plain check,
and the intercept's consistency columns equal the base at that coordinate. -/
theorem two_challenge_masked_slope (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (plain : Fin s → ZMod 2)
    (base : Fin s → Fin tau → Fin kappa → ZMod 2) (hidden hidden' : Fin tau → Fin (2 ^ kappa))
    (hl : CandidateConsistency M plain base (shareMatrix p salt full randomCount enough aux hidden) hidden)
    (hr : CandidateConsistency M plain base (shareMatrix p salt full randomCount enough aux hidden') hidden')
    (e : Fin tau) (j : Fin kappa)
    (hne : Spec.GrayCode.grayFieldRow (hidden e) j ≠ Spec.GrayCode.grayFieldRow (hidden' e) j) (a : Fin s) :
    maskedSlope p salt full randomCount enough aux M e a = plain a ∧
      Spec.BLC.consistencyColumns M (interceptMatrix p salt full randomCount enough) a e j = base a e j := by
  have h1 := hl a e j
  have h2 := hr a e j
  rw [consistencyColumns_affine] at h1 h2
  have hd := zmod2_distinct_sub _ _ hne
  have hs : maskedSlope p salt full randomCount enough aux M e a = plain a := by
    linear_combination h1 - h2 - (maskedSlope p salt full randomCount enough aux M e a - plain a) * hd
  refine ⟨hs, ?_⟩
  linear_combination h1 - Spec.GrayCode.grayFieldRow (hidden e) j * hs

end SDitH.Proofs.BLCSeedLines
