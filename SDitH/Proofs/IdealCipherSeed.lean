import SDitH.Spec.IdealCipherSeed
import SDitH.Proofs.IdealCipherCapacity

namespace SDitH.Proofs.IdealCipherSeed

open Spec.DomainSeparation Spec.IdealCipher Spec.IdealCipherSeed
open scoped Classical ENNReal
noncomputable section

/-- Exact relation to the submitted padded/truncated Enc*, with the ideal
permutation replacing only the block-cipher function argument. -/
theorem encStarIII_projection (family : Family (Bits 256) (Bits 256)) (key input : Bits 192) :
    project192 (family (Spec.SeedPrimitives.pad192 key) (Spec.SeedPrimitives.pad192 input)) =
      Spec.SeedPrimitives.encStarIII (fun k x => family k x) key input := rfl

theorem project192_fiber_card (target : Bits 192)
    (inst : Fintype {block : Bits 256 // project192 block = target}) :
    @Fintype.card {block : Bits 256 // project192 block = target} inst ≤ 2 ^ 64 := by
  letI := inst
  let tail : {block : Bits 256 // project192 block = target} → Bits 64 :=
    fun block i => block.val ⟨192 + i.val, by have hi := i.isLt; omega⟩
  have hinj : Function.Injective tail := by
    intro left right he
    apply Subtype.ext
    funext i
    by_cases hi : i.val < 192
    · have hl := congrFun left.property (⟨i.val, hi⟩ : Fin 192)
      have hr := congrFun right.property (⟨i.val, hi⟩ : Fin 192)
      exact hl.trans hr.symm
    · let j : Fin 64 := ⟨i.val - 192, by have hi' := i.isLt; omega⟩
      have hj : (⟨192 + j.val, by have hj' := j.isLt; omega⟩ : Fin 256) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      have ht := congrFun he j
      simpa only [tail, hj] using ht
  calc
    _ ≤ Fintype.card (Bits 64) := Fintype.card_le_of_injective tail hinj
    _ = _ := by simp [Bits]

theorem project192_fiber_bound (target : Bits 192)
    (inst : Fintype {block : Bits 256 // project192 block = target}) :
    ((@Fintype.card {block : Bits 256 // project192 block = target} inst) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 64 := by
  exact_mod_cast project192_fiber_card target inst

/-- A fresh Category-III Enc* answer has at most 2^64 compatible full-block
outputs for any chosen 192-bit target. This is a conditional single-query
bound; the adaptive two-call seed-collision event still needs to be composed. -/
theorem queryIII_target_bound (world : World (Bits 256) (Bits 256)) (key input target : Bits 192)
    (hfresh : IdealCipherFresh.FreshInput world (Spec.SeedPrimitives.pad192 key) (Spec.SeedPrimitives.pad192 input))
    (q : Nat) (hlen : world.history.length ≤ q) :
    ((queryIII world key input).map (fun result => decide (result.1 = target))) true ≤
      (2 : ℝ≥0∞) ^ 64 / ((2 ^ 256 - q : Nat) : ℝ≥0∞) := by
  have h := IdealCipherCapacity.fresh_encrypt_event_budget_bound world
    (Spec.SeedPrimitives.pad192 key) (Spec.SeedPrimitives.pad192 input) hfresh q hlen
    (fun block => project192 block = target)
  simp only [queryIII, PMF.map_comp, Function.comp_def]
  have htest : (fun result : Bits 256 × World (Bits 256) (Bits 256) => decide (project192 result.1 = target)) =
      (fun result => @decide (project192 result.1 = target) (Classical.propDecidable _)) := by
    funext result
    by_cases he : project192 result.1 = target <;> simp [he]
  rw [htest]
  apply h.trans
  have hsize : Fintype.card (Bits 256) = 2 ^ 256 := by
    simp only [Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [← hsize]
  apply ENNReal.div_le_div_right
  exact project192_fiber_bound target _

end
end SDitH.Proofs.IdealCipherSeed
