import SDitH.Proofs.FreshKeyProbability
import SDitH.Proofs.TruncatedLayoutUniform

/-! Both submitted layouts have injective key maps: the full layout's key is
the identity, and the truncated layout's key is the zero extension of a
192-bit seed to 256 bits, which is injective on the first 192 coordinates.
Hence the fresh-parent-key probability bound applies to both layouts, and
both are output-uniform, so every input of the hidden-share step other than
the fresh-parent-key event itself and the PRG hypothesis is discharged for
the submitted parameters. -/

namespace SDitH.Proofs.LayoutKeyInjective

open Spec.BAVCCipherProgram Spec.SeedPrimitives Spec.DomainSeparation Spec.UniformChallenges
open FreshKeyUniform FreshKeyProbability LeafSeedUniform TruncatedLayoutUniform
open scoped Classical ENNReal

noncomputable section

theorem fullLayout_key_injective (lambda : Nat) : Function.Injective (fullLayout lambda).key := fun _ _ h => h

theorem pad192_injective : Function.Injective pad192 := by
  intro a b h
  funext i
  have hi := congrFun h ⟨i.val, by have := i.isLt; omega⟩
  simpa [pad192, i.isLt] using hi

theorem truncatedLayout_key_injective : Function.Injective truncatedLayout.key := pad192_injective

/-- The fresh-parent-key bound for the full layout. -/
theorem fullLayout_not_fresh_probability (lambda : Nat) (world : Spec.IdealCipher.World (Bits lambda) (Bits lambda)) :
    probability (fun parent : Bits lambda => ¬ FreshKey world ((fullLayout lambda).key parent)) ≤
      (world.history.length : ℝ≥0∞) / (2 ^ lambda : ℕ) :=
  not_fresh_probability (fullLayout lambda) (fullLayout_key_injective lambda) world

/-- The fresh-parent-key bound for the truncated layout. -/
theorem truncatedLayout_not_fresh_probability (world : Spec.IdealCipher.World (Bits 256) (Bits 256)) :
    probability (fun parent : Bits 192 => ¬ FreshKey world (truncatedLayout.key parent)) ≤
      (world.history.length : ℝ≥0∞) / (2 ^ 192 : ℕ) :=
  not_fresh_probability truncatedLayout truncatedLayout_key_injective world

end
end SDitH.Proofs.LayoutKeyInjective
