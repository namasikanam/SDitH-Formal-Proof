import SDitH.Proofs.HashCipherSecurity
import SDitH.Proofs.SeedPairBinding

/-! The joint bound at the submitted full-output and Category-III bit widths.
It is a bound on the defined collision events, not full BAVC or EUF-CMA. -/

namespace SDitH.Proofs.HashCipherParameters

open Spec.DomainSeparation Spec.SeedPairing Spec.HashCipher
open scoped Classical ENNReal
noncomputable section

theorem full_model_bound {lambda : Nat} (hlambda : 0 < lambda) {State : Type*}
    (procedure : Procedure (List Bool) (Bits (2 * lambda)) (Bits lambda) (Bits lambda) State)
    (budget : Nat) (initial : State) :
    ((jointExperiment procedure budget initial).map (combinedEvent id companion)) true ≤
      (budget.choose 2 : ℝ≥0∞) * (((2 : ℝ≥0∞)^(2 * lambda))⁻¹ +
        (((2 ^ lambda - budget : Nat) : ℝ≥0∞)⁻¹ * ((2 ^ lambda - (budget + 2) : Nat) : ℝ≥0∞)⁻¹)) := by
  have h := HashCipherSecurity.combined_bound procedure budget initial id companion
    SeedPairing.companion_involutive (SeedPairing.companion_ne hlambda) 1 (by intro target; simp)
  simpa only [IdealCipherPairAdaptive.pairCost, Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_one, one_div, Nat.cast_pow, Nat.cast_ofNat] using h

theorem truncated_model_bound {State : Type*}
    (procedure : Procedure (List Bool) (Bits 384) (Bits 256) (Bits 256) State)
    (budget : Nat) (initial : State) :
    ((jointExperiment procedure budget initial).map (combinedEvent Spec.IdealCipherSeed.project192 companion)) true ≤
      (budget.choose 2 : ℝ≥0∞) * (((2 : ℝ≥0∞)^384)⁻¹ +
        (((2 : ℝ≥0∞)^64 / ((2 ^ 256 - budget : Nat) : ℝ≥0∞)) *
         ((2 : ℝ≥0∞)^64 / ((2 ^ 256 - (budget + 2) : Nat) : ℝ≥0∞)))) := by
  have h := HashCipherSecurity.combined_bound procedure budget initial Spec.IdealCipherSeed.project192 companion
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by decide : 0 < 256)) (2 ^ 64)
    (fun target => IdealCipherSeed.project192_fiber_card target _)
  simpa only [IdealCipherPairAdaptive.pairCost, Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat] using h

end
end SDitH.Proofs.HashCipherParameters
