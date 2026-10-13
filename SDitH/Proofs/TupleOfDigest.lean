import SDitH.Proofs.SwapDischarge

/-! The hidden tuple of a simulated signature is determined by the digest.
The candidate attempt decides between retry and ready from the challenge
expanded from the digest and the counter alone (the grinding test and the
nonzero merged challenge); the key enters only the opening. So the
returned counter is the first passing counter of the digest, and the
signature's hidden tuple is the digest's tuple when the body is present
and the default tuple otherwise. -/

namespace SDitH.Proofs.TupleOfDigest

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.BLCRetry (Counter Challenge GrindingPassed observe step advance Observation Attempt Step)
open CandidateResample SwapDischarge
open scoped Classical

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]

/-- The attempt's decision: the grinding test and the nonzero merged challenge. -/
def passes (expand : Counter → Challenge tau (2 ^ kappa) wpow) (encode : (Fin tau → Fin (2 ^ kappa)) → F) (ctr : Counter) : Prop :=
  GrindingPassed (expand ctr).grinding ∧ encode (expand ctr).hidden ≠ 0

/-- The first passing counter within the fuel, following the attempt loop. -/
def firstPassing (expand : Counter → Challenge tau (2 ^ kappa) wpow) (encode : (Fin tau → Fin (2 ^ kappa)) → F) :
    Nat → Counter → Option Counter
  | 0, _ => none
  | fuel + 1, ctr =>
    if passes expand encode ctr then some ctr
    else if h : ctr.val + 1 < 2 ^ 32 then firstPassing expand encode fuel ⟨ctr.val + 1, h⟩ else none

omit [Algebra (ZMod 2) F] [NeZero tau] in
/-- The attempt loop returns the first passing counter, whatever the key. -/
theorem observe_eq_firstPassing (key : Key lambda tau (2 ^ kappa)) (expand : Counter → Challenge tau (2 ^ kappa) wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) :
    ∀ (fuel : Nat) (ctr c : Counter) (opening : Spec.CandidateBAVC.Opening lambda tau (2 ^ kappa)),
      observe (attempt (F := F) key expand encode) fuel ctr = .returned c opening →
        firstPassing expand encode fuel ctr = some c := by
  intro fuel
  induction fuel with
  | zero =>
    intro ctr c opening h
    simp [observe] at h
  | succ fuel ih =>
    intro ctr c opening h
    by_cases hp : passes expand encode ctr
    · have hready : attempt (F := F) key expand encode ctr = .ready (Spec.CandidateBAVC.openKey key (expand ctr).hidden) := by
        unfold passes at hp
        unfold attempt
        dsimp only
        rw [if_pos hp]
      simp only [observe, step, hready] at h
      simp only [Observation.returned.injEq] at h
      rw [firstPassing, if_pos hp, h.1]
    · have hretry : attempt (F := F) key expand encode ctr = .retry := by
        unfold passes at hp
        unfold attempt
        dsimp only
        rw [if_neg hp]
      simp only [observe, step, hretry, advance] at h
      rw [firstPassing, if_neg hp]
      by_cases hc : ctr.val + 1 < 2 ^ 32
      · rw [dif_pos hc] at h
        rw [dif_pos hc]
        exact ih _ c opening h
      · rw [dif_neg hc] at h
        simp at h

variable (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The default tuple, the hidden tuple of a signature without a body. -/
def defaultTuple : Fin tau → Fin (2 ^ kappa) := fun _ => ⟨0, Nat.two_pow_pos kappa⟩

/-- The digest's hidden tuple: the challenge's tuple at the first passing
counter, the default tuple if none. -/
def hiddenOfDigest (digest : Digest lambda) : Fin tau → Fin (2 ^ kappa) :=
  match firstPassing (S.expandEvaluation digest) S.encode S.fuel 0 with
  | some ctr => (S.expandEvaluation digest ctr).hidden
  | none => defaultTuple

omit [NeZero tau] in
/-- A simulated signature's hidden tuple is the digest's tuple or the default
tuple. -/
theorem sigHidden_simPost (publicKey message : List Bool) (salt : Bits lambda) (digest : Digest lambda)
    (result : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
      (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (table : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda))
    (q) (hq : q ∈ (simPost S publicKey message salt digest result table).support) :
    sigHidden S q.1 = hiddenOfDigest S digest ∨ sigHidden S q.1 = defaultTuple := by
  simp only [simPost, PMF.mem_support_pure_iff] at hq
  subst hq
  cases result with
  | done committed =>
    simp only
    cases hobs : observe (attempt (F := F) (stateOf S salt committed).2.key (S.expandEvaluation digest) S.encode) S.fuel 0 with
    | pending c => right; rfl
    | returned ctr opening =>
      have hfp := observe_eq_firstPassing (stateOf S salt committed).2.key (S.expandEvaluation digest) S.encode S.fuel 0 ctr
        opening hobs
      dsimp only
      split
      · left
        simp only [sigHidden, hiddenOfDigest, hfp]
      · right
        rfl
    | undefined f => right; rfl
  | hash input next => right; rfl
  | cipher request next => right; rfl

end
end SDitH.Proofs.TupleOfDigest
