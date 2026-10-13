import SDitH.Proofs.BAVCReconstructionGame
import SDitH.Proofs.SeedPairBinding

/-! Probability of inconsistent common revealed seeds for two actually
executed reconstructions with equal roots. All tree, leaf and hash queries
are included. This component statement neither fixes the source algorithms
nor supplies signature extraction, signing simulation or EUF-CMA security. -/

namespace SDitH.Proofs.BAVCReconstructionSecurity

open Spec.DomainSeparation Spec.BAVC Spec.BAVCCipherProgram Spec.BAVCReconstructionGame
open Spec.BAVCReconstructionProgram Spec.HashCipherProgram
open scoped Classical ENNReal
noncomputable section

variable {lambda tau N : Nat} {State : Type*}

theorem full_winning_covered (hlambda : 26 ≤ lambda) (hcount : 4 * (tau * N) ≤ 2 ^ 24)
    (variant : Grinding) (Topen : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N)
    (joint : Spec.IdealCipher.Family (Bits lambda) (Bits lambda) ×
      Spec.HashCipher.Result (List Bool) (Digest lambda) (Bits lambda) (Bits lambda)
        (ReconstructionProgram lambda (Bits lambda) (Bits lambda) (Checked lambda tau N)))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N)
      (fun state => verifyProgram (fullLayout lambda) variant Topen (choose state))).support)
    (hwin : wins joint.2 = true) :
    (∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView joint.2) = true) ∨
      Spec.IdealCipherPairCollision.Witnessed id Spec.SeedPairing.companion joint.1 joint.2.cipherHistory := by
  obtain ⟨claim, left, right, e, i, ls, rs, hl, hr, hroot, hls, hrs, hne⟩ :=
    BAVCReconstructionGame.winning_evaluations (fullLayout lambda) variant Topen adversary q initial choose joint hout hwin
  rcases BAVCReconstructionGame.evaluated_collision (fullLayout lambda) variant Topen claim joint.1 joint.2
    left right hl hr hroot e i ls rs hls hrs hne with hh | ⟨_, hseed, hcalls⟩
  · exact Or.inl hh
  · exact Or.inr (SeedPairBinding.full_seed_collision_witnessed hlambda hcount (SeedTree.leafOffset_lt e i)
      variant joint.1 claim.left.salt ls rs joint.2.cipherHistory hseed.1 hseed.2 (hcalls false).1 (hcalls false).2)

theorem truncated_winning_covered (hcount : 4 * (tau * N) ≤ 2 ^ 24) (variant : Grinding) (Topen : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest 192) (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → Claim 192 tau N)
    (joint : Spec.IdealCipher.Family (Bits 256) (Bits 256) ×
      Spec.HashCipher.Result (List Bool) (Digest 192) (Bits 256) (Bits 256)
        (ReconstructionProgram 192 (Bits 256) (Bits 256) (Checked 192 tau N)))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N)
      (fun state => verifyProgram truncatedLayout variant Topen (choose state))).support)
    (hwin : wins joint.2 = true) :
    (∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView joint.2) = true) ∨
      Spec.IdealCipherPairCollision.Witnessed Spec.IdealCipherSeed.project192 Spec.SeedPairing.companion joint.1 joint.2.cipherHistory := by
  obtain ⟨claim, left, right, e, i, ls, rs, hl, hr, hroot, hls, hrs, hne⟩ :=
    BAVCReconstructionGame.winning_evaluations truncatedLayout variant Topen adversary q initial choose joint hout hwin
  rcases BAVCReconstructionGame.evaluated_collision truncatedLayout variant Topen claim joint.1 joint.2
    left right hl hr hroot e i ls rs hls hrs hne with hh | ⟨_, hseed, hcalls⟩
  · exact Or.inl hh
  · exact Or.inr (SeedPairBinding.truncated_seed_collision_witnessed hcount (SeedTree.leafOffset_lt e i)
      variant joint.1 claim.left.salt ls rs joint.2.cipherHistory hseed.1 hseed.2 (hcalls false).1 (hcalls false).2)

/-- Q = q + 2*budget includes both complete reconstructions. The event asks
only about successful equal-root reconstructions with a disagreeing common
revealed seed; undefined-source outcomes are retained separately by the game. -/
theorem full_disagreement_bound (hlambda : 26 ≤ lambda) (hcount : 4 * (tau * N) ≤ 2 ^ 24)
    (variant : Grinding) (Topen : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N) :
    ((experiment (fullLayout lambda) variant Topen adversary q initial choose).map wins) true ≤
      ((q + verificationBudget tau N).choose 2 : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹ ^ (2 * lambda) +
          (((2 ^ lambda - (q + verificationBudget tau N) : Nat) : ℝ≥0∞)⁻¹ *
            ((2 ^ lambda - (q + verificationBudget tau N + 2) : Nat) : ℝ≥0∞)⁻¹)) := by
  have h := BAVCReconstructionGame.event_bound (fullLayout lambda) variant Topen adversary q initial choose id Spec.SeedPairing.companion
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by omega)) 1 (by intro target; simp)
    (fun joint hj hw => full_winning_covered hlambda hcount variant Topen adversary q initial choose joint hj hw)
  simpa only [Digest, Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow, IdealCipherPairAdaptive.pairCost, Nat.cast_one, one_div] using h

theorem truncated_disagreement_bound (hcount : 4 * (tau * N) ≤ 2 ^ 24) (variant : Grinding) (Topen : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest 192) (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → Claim 192 tau N) :
    ((experiment truncatedLayout variant Topen adversary q initial choose).map wins) true ≤
      ((q + verificationBudget tau N).choose 2 : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹ ^ 384 +
          (((2 : ℝ≥0∞) ^ 64 / ((2 ^ 256 - (q + verificationBudget tau N) : Nat) : ℝ≥0∞)) *
            ((2 : ℝ≥0∞) ^ 64 / ((2 ^ 256 - (q + verificationBudget tau N + 2) : Nat) : ℝ≥0∞)))) := by
  have h := BAVCReconstructionGame.event_bound truncatedLayout variant Topen adversary q initial choose Spec.IdealCipherSeed.project192 Spec.SeedPairing.companion
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by decide : 0 < 256)) (2 ^ 64)
    (fun target => IdealCipherSeed.project192_fiber_card target _)
    (fun joint hj hw => truncated_winning_covered hcount variant Topen adversary q initial choose joint hj hw)
  apply h.trans
  apply le_of_eq
  simp only [Digest, Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow, IdealCipherPairAdaptive.pairCost]

end
end SDitH.Proofs.BAVCReconstructionSecurity
