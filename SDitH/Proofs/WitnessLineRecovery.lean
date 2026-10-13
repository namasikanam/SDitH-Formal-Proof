import SDitH.Proofs.SlopeConsistencyLink

/-! Recovering the extracted witness coordinate from the two branches.
Under a common slope the candidate witness value of each branch is the
same line evaluated at that branch's inverted challenge; two evaluations
at distinct points determine the line's constant term, which is the
transmitted correction plus the common slope. The extraction's algebraic
step therefore reads the witness coordinate directly from the two
accepting transcripts, given distinct merged challenges. -/

namespace SDitH.Proofs.WitnessLineRecovery

open Spec.DomainSeparation Spec.BLCSeedLines Spec.BLCSeedFold
open scoped BigOperators
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The constant term of a line from two evaluations. -/
def extractCoordinate {F : Type*} [Field F] (vL vR dL dR : F) : F :=
  vL - dL * ((vL - vR) / (dL - dR))

/-- Two evaluations of a line at distinct points determine its constant term. -/
theorem line_recover {F : Type*} [Field F] (x c dL dR : F) (hne : dL ≠ dR) :
    extractCoordinate (x + dL * c) (x + dR * c) dL dR = x := by
  unfold extractCoordinate
  have h : dL - dR ≠ 0 := sub_ne_zero.mpr hne
  have hc : (x + dL * c - (x + dR * c)) / (dL - dR) = c := by
    rw [show x + dL * c - (x + dR * c) = (dL - dR) * c by ring]
    exact mul_div_cancel_left₀ c h
  rw [hc]
  ring

/-- The witness coordinate from the two branches' candidate witness values:
with a common slope, the psi-of-challenge-row encoding and distinct merged
challenges, the extracted coordinate is the correction plus the slope. -/
theorem extract_witness_coordinate {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (hiddenL hiddenR : Fin tau → Fin (2 ^ kappa)) (encode : (Fin tau → Fin (2 ^ kappa)) → F) (j : Fin wit) (u : ZMod 2)
    (hu : ∀ e, Spec.BLCSeedFold.slope p salt full randomCount enough aux e (Spec.BLC.witnessIndex j) = u)
    (hencode : encode = fun hidden => Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hnzL : encode hiddenL ≠ 0) (hnzR : encode hiddenR ≠ 0) (hdist : encode hiddenL ≠ encode hiddenR) :
    extractCoordinate
      (algebraMap (ZMod 2) F (aux.witnessCorrection j) + (encode hiddenL)⁻¹ *
        Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hiddenL (Spec.BLC.witnessIndex j)))
      (algebraMap (ZMod 2) F (aux.witnessCorrection j) + (encode hiddenR)⁻¹ *
        Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hiddenR (Spec.BLC.witnessIndex j)))
      (encode hiddenL)⁻¹ (encode hiddenR)⁻¹ =
    algebraMap (ZMod 2) F (aux.witnessCorrection j + u) := by
  rw [SlopeConsistencyLink.candidate_witness_constant_slope xi p salt full randomCount enough aux hiddenL encode j u hu
      hencode hnzL,
    SlopeConsistencyLink.candidate_witness_constant_slope xi p salt full randomCount enough aux hiddenR encode j u hu
      hencode hnzR]
  exact line_recover _ _ _ _ (fun h => hdist (inv_injective h))

end
end SDitH.Proofs.WitnessLineRecovery
