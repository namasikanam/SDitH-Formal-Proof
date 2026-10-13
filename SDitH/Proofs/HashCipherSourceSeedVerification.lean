import SDitH.Proofs.HashCipherVerification

/-! Exact source seed-collision laws and bounds after an adversary that can
interleave hash, encryption and decryption queries. This is one component of
commitment binding; no tree, BLC or signature security theorem is asserted. -/

namespace SDitH.Proofs.HashCipherSourceSeedVerification

open Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedPairing
open Spec.HashCipher Spec.HashCipherVerification
open Spec.SeedVerification (SourceClaim fullClaim truncatedClaim checked sourceWins)
open scoped Classical ENNReal
noncomputable section

variable {Input Digest State : Type*} [Fintype Digest] [Nonempty Digest]

theorem full_experiments_eq {lambda leaves : Nat} (variant : Grinding)
    (adversary : Procedure Input Digest (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim lambda leaves) :
    (seedExperiment adversary q initial id (fun state => fullClaim variant (choose state))).map seedWins =
      directFullExperiment variant adversary q initial choose := by
  rw [HashCipherVerification.seed_experiment_law]
  unfold directFullExperiment
  congr 1
  funext family state
  apply Bool.eq_iff_iff.mpr
  simpa only [Spec.SeedVerification.wins, sourceWins, decide_eq_true_eq] using
    SourceSeedVerification.full_wins_iff variant family (choose state) []

theorem truncated_experiments_eq {leaves : Nat} (variant : Grinding)
    (adversary : Procedure Input Digest (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim 192 leaves) :
    (seedExperiment adversary q initial Spec.IdealCipherSeed.project192
      (fun state => truncatedClaim variant (choose state))).map seedWins =
      directTruncatedExperiment variant adversary q initial choose := by
  rw [HashCipherVerification.seed_experiment_law]
  unfold directTruncatedExperiment
  congr 1
  funext family state
  apply Bool.eq_iff_iff.mpr
  simpa only [Spec.SeedVerification.wins, sourceWins, decide_eq_true_eq] using
    SourceSeedVerification.truncated_wins_iff variant family (choose state) []

/-- The event is the literal source equality of the two computed commitments,
with distinct selected seeds and a common salt/index. No query-membership or
program-completion condition is part of that event. -/
theorem full_binding_bound {lambda leaves : Nat} (hlambda : 26 ≤ lambda)
    (hcount : 4 * leaves ≤ 2 ^ 24) (variant : Grinding)
    (adversary : Procedure Input Digest (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim lambda leaves) :
    directFullExperiment variant adversary q initial choose true ≤
      ((q + 4).choose 2 : ℝ≥0∞) *
        (((2 ^ lambda - (q + 4) : Nat) : ℝ≥0∞)⁻¹ * ((2 ^ lambda - (q + 6) : Nat) : ℝ≥0∞)⁻¹) := by
  rw [← full_experiments_eq]
  have h := HashCipherVerification.seed_binding_bound adversary q initial id
    (fun state => fullClaim variant (choose state)) companion
    (fun state => SeedPairing.cipherInput_companion hlambda hcount
      (by have hi := (choose state).index.isLt; omega) variant (choose state).salt)
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by omega)) 1 (by intro target; simp)
  simpa only [IdealCipherPairAdaptive.pairCost, Bits, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_one, one_div, Nat.add_assoc] using h

theorem truncated_binding_bound {leaves : Nat} (hcount : 4 * leaves ≤ 2 ^ 24)
    (variant : Grinding) (adversary : Procedure Input Digest (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim 192 leaves) :
    directTruncatedExperiment variant adversary q initial choose true ≤
      ((q + 4).choose 2 : ℝ≥0∞) *
        (((2 : ℝ≥0∞)^64 / ((2 ^ 256 - (q + 4) : Nat) : ℝ≥0∞)) *
         ((2 : ℝ≥0∞)^64 / ((2 ^ 256 - (q + 6) : Nat) : ℝ≥0∞))) := by
  rw [← truncated_experiments_eq]
  have h := HashCipherVerification.seed_binding_bound adversary q initial Spec.IdealCipherSeed.project192
    (fun state => truncatedClaim variant (choose state)) companion
    (fun state => SeedPairing.padded_cipherInput_companion hcount
      (by have hi := (choose state).index.isLt; omega) variant (choose state).salt)
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by decide : 0 < 256)) (2 ^ 64)
    (fun target => IdealCipherSeed.project192_fiber_card target _)
  simpa only [IdealCipherPairAdaptive.pairCost, Bits, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Nat.add_assoc] using h

end
end SDitH.Proofs.HashCipherSourceSeedVerification
