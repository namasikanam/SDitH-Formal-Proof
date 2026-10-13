import SDitH.Proofs.SeedPairing
import SDitH.Proofs.IdealCipherPairAdaptive
import SDitH.Proofs.IdealCipherSeed
import SDitH.Proofs.BAVCBindingReconstruction
import SDitH.Proofs.CipherPrimitives

/-! Source instantiations of the paired-cipher collision event. Collision-to-event
coverage below explicitly requires the two left-half graph entries. Deriving
that coverage by executing the complete seed verification, with its query cost,
remains separate from the generic adaptive bound proved here. -/

namespace SDitH.Proofs.SeedPairBinding

open Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedPairing Spec.IdealCipher Spec.IdealCipherPairCollision
open scoped Classical ENNReal
noncomputable section

theorem full_seed_collision_witnessed {lambda leafCount index : Nat}
    (hlambda : 26 ≤ lambda) (hcount : 4 * leafCount ≤ 2 ^ 24) (hindex : index < leafCount)
    (variant : Grinding) (family : Family (Bits lambda) (Bits lambda))
    (salt left right : Bits lambda) (history : List (Entry (Bits lambda) (Bits lambda)))
    (hne : left ≠ right)
    (hcollision : commitSeed leafCount variant (fun key input => family key input) salt left index =
      commitSeed leafCount variant (fun key input => family key input) salt right index)
    (hleft : (⟨left, cipherInput variant salt (leafCount + index) false,
      family left (cipherInput variant salt (leafCount + index) false)⟩ : Entry _ _) ∈ history)
    (hright : (⟨right, cipherInput variant salt (leafCount + index) false,
      family right (cipherInput variant salt (leafCount + index) false)⟩ : Entry _ _) ∈ history) :
    Witnessed id companion family history := by
  have he := (BAVCBindingReconstruction.commitSeed_eq_iff leafCount variant (fun key input => family key input)
    salt left right index).mp hcollision
  refine ⟨_, hleft, _, hright, hne, rfl, he false, ?_⟩
  change family left (companion (cipherInput variant salt (leafCount + index) false)) =
    family right (companion (cipherInput variant salt (leafCount + index) false))
  rw [← SeedPairing.cipherInput_companion hlambda hcount (by omega)]
  exact he true

/-- Category III uses padded keys and plaintexts in one full 256-bit family.
Only the compared outputs are projected. This instantiates the existing source
interpretation of the seed routine at lambda=192; its source scope is reviewed. -/
theorem truncated_seed_collision_witnessed {leafCount index : Nat}
    (hcount : 4 * leafCount ≤ 2 ^ 24) (hindex : index < leafCount)
    (variant : Grinding) (family : Family (Bits 256) (Bits 256))
    (salt left right : Bits 192) (history : List (Entry (Bits 256) (Bits 256)))
    (hne : left ≠ right)
    (hcollision : commitSeed leafCount variant (encStarIII (fun key input => family key input)) salt left index =
      commitSeed leafCount variant (encStarIII (fun key input => family key input)) salt right index)
    (hleft : (⟨pad192 left, pad192 (cipherInput variant salt (leafCount + index) false),
      family (pad192 left) (pad192 (cipherInput variant salt (leafCount + index) false))⟩ : Entry _ _) ∈ history)
    (hright : (⟨pad192 right, pad192 (cipherInput variant salt (leafCount + index) false),
      family (pad192 right) (pad192 (cipherInput variant salt (leafCount + index) false))⟩ : Entry _ _) ∈ history) :
    Witnessed Spec.IdealCipherSeed.project192 companion family history := by
  have he := (BAVCBindingReconstruction.commitSeed_eq_iff leafCount variant (encStarIII (fun key input => family key input))
    salt left right index).mp hcollision
  refine ⟨_, hleft, _, hright, (fun h => hne (CipherPrimitives.pad192_injective h)), rfl, he false, ?_⟩
  change Spec.IdealCipherSeed.project192 (family (pad192 left) (companion (pad192 (cipherInput variant salt (leafCount + index) false)))) =
    Spec.IdealCipherSeed.project192 (family (pad192 right) (companion (pad192 (cipherInput variant salt (leafCount + index) false))))
  rw [← SeedPairing.padded_cipherInput_companion hcount (by omega)]
  exact he true

theorem full_experiment_bound {lambda : Nat} (hlambda : 0 < lambda) {State : Type*}
    (procedure : Procedure (Bits lambda) (Bits lambda) State) (budget : Nat) (initial : State) :
    ((Spec.IdealCipherJoint.experiment procedure budget initial).map (fun joint =>
      decide (Witnessed id companion joint.1 joint.2.history))) true ≤
      (budget.choose 2 : ℝ≥0∞) *
        (((2 ^ lambda - budget : Nat) : ℝ≥0∞)⁻¹ * ((2 ^ lambda - (budget + 2) : Nat) : ℝ≥0∞)⁻¹) := by
  have h := IdealCipherPairAdaptive.experiment_bound procedure budget initial id companion
    SeedPairing.companion_involutive (SeedPairing.companion_ne hlambda) 1 (by intro target; simp)
  simpa only [IdealCipherPairAdaptive.pairCost, Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_one, one_div] using h

theorem truncated_experiment_bound {State : Type*}
    (procedure : Procedure (Bits 256) (Bits 256) State) (budget : Nat) (initial : State) :
    ((Spec.IdealCipherJoint.experiment procedure budget initial).map (fun joint =>
      decide (Witnessed Spec.IdealCipherSeed.project192 companion joint.1 joint.2.history))) true ≤
      (budget.choose 2 : ℝ≥0∞) *
        (((2 : ℝ≥0∞)^64 / ((2 ^ 256 - budget : Nat) : ℝ≥0∞)) *
         ((2 : ℝ≥0∞)^64 / ((2 ^ 256 - (budget + 2) : Nat) : ℝ≥0∞))) := by
  have h := IdealCipherPairAdaptive.experiment_bound procedure budget initial Spec.IdealCipherSeed.project192 companion
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by decide : 0 < 256)) (2 ^ 64)
    (fun target => IdealCipherSeed.project192_fiber_card target _)
  simpa only [IdealCipherPairAdaptive.pairCost, Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat] using h

end
end SDitH.Proofs.SeedPairBinding
