import SDitH.Proofs.SeedVerification
import SDitH.Proofs.SeedPairBinding

/-! The fully queried binding experiment specialized to the literal seed
commitment inputs and outputs. Structural companion/capacity premises are
discharged here. No signature-level security conclusion is asserted. -/

namespace SDitH.Proofs.SourceSeedVerification

open Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedPairing Spec.IdealCipher Spec.SeedVerification
open scoped Classical ENNReal
noncomputable section

theorem concatenate_eq_iff {lambda : Nat} (left right : Bits lambda × Bits lambda) :
    concatenate left.1 left.2 = concatenate right.1 right.2 ↔ left = right := by
  constructor
  · intro h
    apply Prod.ext
    · funext i
      have he := congrFun h ⟨i.val, by have hi := i.isLt; omega⟩
      simpa only [SeedPrimitives.concatenate_left] using he
    · funext i
      have he := congrFun h ⟨lambda + i.val, by have hi := i.isLt; omega⟩
      simpa only [SeedPrimitives.concatenate_right] using he
  · rintro rfl
    rfl

theorem full_outputs {lambda leaves : Nat} (variant : Grinding)
    (family : Family (Bits lambda) (Bits lambda)) (claim : SourceClaim lambda leaves) :
    concatenate (checked family id (fullClaim variant claim)).left.1 (checked family id (fullClaim variant claim)).left.2 =
      commitSeed leaves variant (fun key input => family key input) claim.salt claim.left claim.index.val ∧
    concatenate (checked family id (fullClaim variant claim)).right.1 (checked family id (fullClaim variant claim)).right.2 =
      commitSeed leaves variant (fun key input => family key input) claim.salt claim.right claim.index.val := ⟨rfl, rfl⟩

theorem truncated_outputs {leaves : Nat} (variant : Grinding)
    (family : Family (Bits 256) (Bits 256)) (claim : SourceClaim 192 leaves) :
    concatenate (checked family Spec.IdealCipherSeed.project192 (truncatedClaim variant claim)).left.1
      (checked family Spec.IdealCipherSeed.project192 (truncatedClaim variant claim)).left.2 =
      commitSeed leaves variant (encStarIII (fun key input => family key input)) claim.salt claim.left claim.index.val ∧
    concatenate (checked family Spec.IdealCipherSeed.project192 (truncatedClaim variant claim)).right.1
      (checked family Spec.IdealCipherSeed.project192 (truncatedClaim variant claim)).right.2 =
      commitSeed leaves variant (encStarIII (fun key input => family key input)) claim.salt claim.right claim.index.val := ⟨rfl, rfl⟩

theorem full_wins_iff {lambda leaves : Nat} (variant : Grinding)
    (family : Family (Bits lambda) (Bits lambda)) (claim : SourceClaim lambda leaves)
    (history : List (Entry (Bits lambda) (Bits lambda))) :
    wins (⟨.done (checked family id (fullClaim variant claim)), history⟩ : Result _ _ _) = true ↔
      claim.left ≠ claim.right ∧
        commitSeed leaves variant (fun key input => family key input) claim.salt claim.left claim.index.val =
          commitSeed leaves variant (fun key input => family key input) claim.salt claim.right claim.index.val := by
  rw [SeedVerification.wins_done, ← (full_outputs variant family claim).1,
    ← (full_outputs variant family claim).2, concatenate_eq_iff]
  rfl

theorem truncated_wins_iff {leaves : Nat} (variant : Grinding)
    (family : Family (Bits 256) (Bits 256)) (claim : SourceClaim 192 leaves)
    (history : List (Entry (Bits 256) (Bits 256))) :
    wins (⟨.done (checked family Spec.IdealCipherSeed.project192 (truncatedClaim variant claim)), history⟩ : Result _ _ _) = true ↔
      claim.left ≠ claim.right ∧
        commitSeed leaves variant (encStarIII (fun key input => family key input)) claim.salt claim.left claim.index.val =
          commitSeed leaves variant (encStarIII (fun key input => family key input)) claim.salt claim.right claim.index.val := by
  rw [SeedVerification.wins_done, ← (truncated_outputs variant family claim).1,
    ← (truncated_outputs variant family claim).2, concatenate_eq_iff]
  change (pad192 claim.left ≠ pad192 claim.right ∧ _) ↔ (claim.left ≠ claim.right ∧ _)
  rw [CipherPrimitives.pad192_injective.ne_iff]

theorem full_experiments_eq {lambda leaves : Nat} (variant : Grinding) {State : Type*}
    (adversary : Procedure (Bits lambda) (Bits lambda) State) (q : Nat) (initial : State)
    (choose : State → SourceClaim lambda leaves) :
    (fullExperiment variant adversary q initial choose).map wins =
      directFullExperiment variant adversary q initial choose := by
  refine (SeedVerification.experiment_law adversary q initial id (fun state => fullClaim variant (choose state))).trans ?_
  unfold directFullExperiment directExperiment
  congr 1
  funext family
  congr 1
  funext start
  have h := full_wins_iff variant family (choose start.state) []
  have hs : sourceWins variant (fun key input => family key input) (choose start.state) = true ↔
      (choose start.state).left ≠ (choose start.state).right ∧
        commitSeed leaves variant (fun key input => family key input) (choose start.state).salt (choose start.state).left (choose start.state).index.val =
          commitSeed leaves variant (fun key input => family key input) (choose start.state).salt (choose start.state).right (choose start.state).index.val := by
    simp only [sourceWins, decide_eq_true_eq]
  exact Bool.eq_iff_iff.mpr (h.trans hs.symm)

theorem truncated_experiments_eq {leaves : Nat} (variant : Grinding) {State : Type*}
    (adversary : Procedure (Bits 256) (Bits 256) State) (q : Nat) (initial : State)
    (choose : State → SourceClaim 192 leaves) :
    (truncatedExperiment variant adversary q initial choose).map wins =
      directTruncatedExperiment variant adversary q initial choose := by
  refine (SeedVerification.experiment_law adversary q initial Spec.IdealCipherSeed.project192
    (fun state => truncatedClaim variant (choose state))).trans ?_
  unfold directTruncatedExperiment directExperiment
  congr 1
  funext family
  congr 1
  funext start
  have h := truncated_wins_iff variant family (choose start.state) []
  have hs : sourceWins variant (encStarIII (fun key input => family key input)) (choose start.state) = true ↔
      (choose start.state).left ≠ (choose start.state).right ∧
        commitSeed leaves variant (encStarIII (fun key input => family key input)) (choose start.state).salt (choose start.state).left (choose start.state).index.val =
          commitSeed leaves variant (encStarIII (fun key input => family key input)) (choose start.state).salt (choose start.state).right (choose start.state).index.val := by
    simp only [sourceWins, decide_eq_true_eq]
  exact Bool.eq_iff_iff.mpr (h.trans hs.symm)

theorem full_binding_bound {lambda leaves : Nat} (hlambda : 26 ≤ lambda)
    (hcount : 4 * leaves ≤ 2 ^ 24) (variant : Grinding) {State : Type*}
    (adversary : Procedure (Bits lambda) (Bits lambda) State) (q : Nat) (initial : State)
    (choose : State → SourceClaim lambda leaves) :
    ((fullExperiment variant adversary q initial choose).map wins) true ≤
      ((q + 4).choose 2 : ℝ≥0∞) *
        (((2 ^ lambda - (q + 4) : Nat) : ℝ≥0∞)⁻¹ * ((2 ^ lambda - (q + 6) : Nat) : ℝ≥0∞)⁻¹) := by
  have h := SeedVerification.binding_bound adversary q initial id (fun state => fullClaim variant (choose state)) companion
    (fun state => SeedPairing.cipherInput_companion hlambda hcount (by have hi := (choose state).index.isLt; omega) variant (choose state).salt)
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by omega)) 1 (by intro target; simp)
  simpa only [fullExperiment, IdealCipherPairAdaptive.pairCost, Bits, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_one, one_div, Nat.add_assoc] using h

theorem truncated_binding_bound {leaves : Nat} (hcount : 4 * leaves ≤ 2 ^ 24)
    (variant : Grinding) {State : Type*} (adversary : Procedure (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim 192 leaves) :
    ((truncatedExperiment variant adversary q initial choose).map wins) true ≤
      ((q + 4).choose 2 : ℝ≥0∞) *
        (((2 : ℝ≥0∞)^64 / ((2 ^ 256 - (q + 4) : Nat) : ℝ≥0∞)) *
         ((2 : ℝ≥0∞)^64 / ((2 ^ 256 - (q + 6) : Nat) : ℝ≥0∞))) := by
  have h := SeedVerification.binding_bound adversary q initial Spec.IdealCipherSeed.project192
    (fun state => truncatedClaim variant (choose state)) companion
    (fun state => SeedPairing.padded_cipherInput_companion hcount (by have hi := (choose state).index.isLt; omega) variant (choose state).salt)
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by decide : 0 < 256)) (2 ^ 64)
    (fun target => IdealCipherSeed.project192_fiber_card target _)
  simpa only [truncatedExperiment, IdealCipherPairAdaptive.pairCost, Bits, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Nat.add_assoc] using h

theorem direct_full_binding_bound {lambda leaves : Nat} (hlambda : 26 ≤ lambda)
    (hcount : 4 * leaves ≤ 2 ^ 24) (variant : Grinding) {State : Type*}
    (adversary : Procedure (Bits lambda) (Bits lambda) State) (q : Nat) (initial : State)
    (choose : State → SourceClaim lambda leaves) :
    directFullExperiment variant adversary q initial choose true ≤
      ((q + 4).choose 2 : ℝ≥0∞) *
        (((2 ^ lambda - (q + 4) : Nat) : ℝ≥0∞)⁻¹ * ((2 ^ lambda - (q + 6) : Nat) : ℝ≥0∞)⁻¹) := by
  rw [← full_experiments_eq]
  exact full_binding_bound hlambda hcount variant adversary q initial choose

theorem direct_truncated_binding_bound {leaves : Nat} (hcount : 4 * leaves ≤ 2 ^ 24)
    (variant : Grinding) {State : Type*} (adversary : Procedure (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → SourceClaim 192 leaves) :
    directTruncatedExperiment variant adversary q initial choose true ≤
      ((q + 4).choose 2 : ℝ≥0∞) *
        (((2 : ℝ≥0∞)^64 / ((2 ^ 256 - (q + 4) : Nat) : ℝ≥0∞)) *
         ((2 : ℝ≥0∞)^64 / ((2 ^ 256 - (q + 6) : Nat) : ℝ≥0∞))) := by
  rw [← truncated_experiments_eq]
  exact truncated_binding_bound hcount variant adversary q initial choose

end
end SDitH.Proofs.SourceSeedVerification
