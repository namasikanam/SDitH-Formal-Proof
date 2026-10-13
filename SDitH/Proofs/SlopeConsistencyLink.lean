import SDitH.Proofs.ForkOutcomeUniform

/-! From the uniform fork data to slope consistency and the extracted
line. Under separation at every execution and no recorded seed collision,
every execution's masked slope at the stored mask is the plain check, so
all masked images agree; then either two executions have distinct slopes
with equal masked images (the slope-consistency game's winning condition
at that mask) or all slopes are equal. With a common slope the candidate
middle's witness value is affine in the inverted challenge, with constant
term the transmitted correction plus the common slope: the extracted
witness coordinate. The separation and the absence of seed collisions are
explicit hypotheses here, the former pending the recorded decision. -/

namespace SDitH.Proofs.SlopeConsistencyLink

open Spec.BAVC Spec.DomainSeparation Spec.BLCSeedLines Spec.BLCSeedFold Spec.ConsistencyMatrix Spec.BLCSeedExtraction
open Spec.SharedScheme Spec.HashCipherEvaluation Spec.SlopeConsistency
open Spec.SlopeConsistencyGame (Out)
open ForkOutcomeUniform (UniformSlope)
open scoped BigOperators Classical
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

theorem maskedSlope_eq_masked (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (e : Fin tau) (a : Fin s) :
    maskedSlope p salt full randomCount enough aux M e a =
      masked M (Spec.BLCSeedFold.slope p salt full randomCount enough aux e) a := rfl

/-- Under separation at every execution: a recorded seed collision at some
execution, or every execution's masked slope at the stored mask is the plain check. -/
theorem all_executions_plain {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (V : VerifierSetting F lambda tau kappa s wit rnd)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (P : List Bool → Option (Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (saltL saltR : Bits lambda)
    (auxL auxR : Spec.BLCCommit.Auxiliary tau s wit rnd) (piopL piopR : Digest lambda)
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau)
    (h : UniformSlope p randomCount enough V family P ciphers saltL saltR auxL auxR piopL piopR decL decR)
    (hsep : ∀ e, V.expand piopL decL.1 e ≠ V.expand piopR decR.1 e) :
    ∃ (reconL reconR : Reconstructed lambda tau (2 ^ kappa)) (auxD : Digest lambda) (pm : Out lambda s wit rnd),
      saltL = saltR ∧ auxL.corrections = auxR.corrections ∧ auxL.plain = auxR.plain ∧
      P (Spec.BAVCChainInputs.maskInput auxD) = some pm ∧
      ((∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (ls rs : Seed lambda),
          Spec.BAVCBinding.IsSeedCollision
            (Spec.BAVCReconstructionProgram.primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family
              (SharedSchemeChain.projected P))
            saltL (Spec.SeedTree.leafOffset e i) ls rs ∧
          ∀ side : Bool,
            Spec.IdealCipher.entry (.encrypt (V.layout.key ls)
              (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
              (family (V.layout.key ls) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers ∧
            Spec.IdealCipher.entry (.encrypt (V.layout.key rs)
              (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
              (family (V.layout.key rs) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers) ∨
        ∀ e a, masked pm.2 (Spec.BLCSeedFold.slope p saltL (fun e' i => merge reconL reconR e' i) randomCount enough auxL e) a =
          auxL.plain a) := by
  obtain ⟨reconL, reconR, auxD, pm, hsalt, hcorr, hplain, _, _, hpm, hall⟩ := h
  refine ⟨reconL, reconR, auxD, pm, hsalt, hcorr, hplain, hpm, ?_⟩
  by_cases hcol : ∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (ls rs : Seed lambda),
      Spec.BAVCBinding.IsSeedCollision
        (Spec.BAVCReconstructionProgram.primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family
          (SharedSchemeChain.projected P))
        saltL (Spec.SeedTree.leafOffset e i) ls rs ∧
      ∀ side : Bool,
        Spec.IdealCipher.entry (.encrypt (V.layout.key ls)
          (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
          (family (V.layout.key ls) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers ∧
        Spec.IdealCipher.entry (.encrypt (V.layout.key rs)
          (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
          (family (V.layout.key rs) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers
  · exact Or.inl hcol
  · right
    intro e a
    rcases hall e (hsep e) with ⟨i, ls, rs, hseed, hcalls⟩ | hid
    · exact absurd ⟨e, i, ls, rs, hseed, hcalls⟩ hcol
    · exact hid a

/-- Equal masked images across executions: two executions with distinct
slopes and equal masked images, or all slopes equal. -/
theorem slopes_dichotomy (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2))
    (slopes : Fin tau → Fin (s + (wit + rnd)) → ZMod 2) (plain : Fin s → ZMod 2)
    (h : ∀ e a, masked M (slopes e) a = plain a) :
    (∃ e e', slopes e ≠ slopes e' ∧ ∀ a, masked M (slopes e) a = masked M (slopes e') a) ∨
      ∀ e e', slopes e = slopes e' := by
  by_cases hall : ∀ e e', slopes e = slopes e'
  · exact Or.inr hall
  · push_neg at hall
    obtain ⟨e, e', hne⟩ := hall
    exact Or.inl ⟨e, e', hne, fun a => by rw [h e a, h e' a]⟩

/-- With a common slope, the candidate middle's witness value is affine in
the inverted challenge: constant term correction plus the common slope,
coefficient the psi image of the intercept row. -/
theorem candidate_witness_constant_slope {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (hidden : Fin tau → Fin (2 ^ kappa)) (encode : (Fin tau → Fin (2 ^ kappa)) → F) (j : Fin wit) (u : ZMod 2)
    (hu : ∀ e, Spec.BLCSeedFold.slope p salt full randomCount enough aux e (Spec.BLC.witnessIndex j) = u)
    (hencode : encode = fun hidden => Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (hnz : encode hidden ≠ 0) :
    algebraMap (ZMod 2) F (aux.witnessCorrection j) + (encode hidden)⁻¹ *
        Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.witnessIndex j)) =
      algebraMap (ZMod 2) F (aux.witnessCorrection j + u) +
        (encode hidden)⁻¹ * Spec.BLC.psi xi (interceptMatrix p salt full randomCount enough (Spec.BLC.witnessIndex j)) := by
  have hQ : shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.witnessIndex j) =
      fun e j' => u * Spec.GrayCode.grayFieldRow (hidden e) j' +
        interceptMatrix p salt full randomCount enough (Spec.BLC.witnessIndex j) e j' := by
    funext e j'
    show Spec.BLCSeedFold.slope p salt full randomCount enough aux e (Spec.BLC.witnessIndex j) * _ + _ = _
    rw [hu]
    rfl
  have hmerge : (encode hidden)⁻¹ * Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden) = 1 := by
    have hd : Spec.BLC.psi xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden) ≠ 0 := by
      rw [hencode] at hnz
      exact hnz
    rw [hencode]
    exact inv_mul_cancel₀ hd
  rw [hQ, BLCSeedLines.psi_affine_constant, map_add, mul_add, ← mul_assoc, mul_comm ((encode hidden)⁻¹) (algebraMap (ZMod 2) F u),
    mul_assoc, hmerge, mul_one]
  ring

end
end SDitH.Proofs.SlopeConsistencyLink
