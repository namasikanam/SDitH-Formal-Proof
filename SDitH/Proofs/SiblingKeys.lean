import SDitH.Proofs.PrunedRun
import SDitH.Proofs.TreeStepFresh
import SDitH.Proofs.MeanHybrid

/-! The keys of two outputs at one fresh key. Under the posterior family,
the outputs of a fresh key at two distinct inputs have the same layout key
with probability at most the fiber bound over the remaining block count:
after the first output is drawn, the second is a fresh answer whose key
hits the first's with at most the fiber bound many blocks. -/

namespace SDitH.Proofs.SiblingKeys

open Spec.IdealCipher (Family Entry Matches World entry answer)
open Spec.DomainSeparation
open CipherResample PrunedRun TreeStepFresh ChargeExpect MeanHybrid IdealCipherFresh FreshKeyUniform
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat} (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (c : Nat)
  (hfiber : ∀ κ, Fintype.card {r : Bits lambda // layout.key (layout.output r) = κ} ≤ c)

include hfiber in
/-- The two outputs of a fresh key at distinct inputs have the same layout
key with probability at most the fiber bound over the remaining blocks. -/
theorem sibling_keys_le (world : World (Bits lambda) (Bits lambda)) (p t₁ t₂ : Bits lambda) (hne : t₁ ≠ t₂)
    (hfresh : FreshKey world p) (q : Nat) (hlen : world.history.length + 1 ≤ q) :
    ((posterior world.history).map fun f =>
        decide (layout.key (layout.output (f p t₂)) = layout.key (layout.output (f p t₁)))) true ≤
      (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞) := by
  have hstep := posterior_cipher_step world (.encrypt p t₁) fun v _ f' =>
    PMF.pure (decide (layout.key (layout.output (f' p t₂)) = layout.key (layout.output v)))
  have hmap : ((posterior world.history).map fun f =>
      decide (layout.key (layout.output (f p t₂)) = layout.key (layout.output (f p t₁)))) =
      (posterior world.history).bind fun f =>
        PMF.pure (decide (layout.key (layout.output (f p t₂)) = layout.key (layout.output (answer f (.encrypt p t₁))))) := rfl
  rw [hmap, ← hstep, mean_bind_apply]
  refine mean_le_const _ _ _ fun f hf => ?_
  have hmatch := matches_of_mem_posterior world.history world.possible f hf
  have hpos' : ∃ g : Family (Bits lambda) (Bits lambda),
      Matches g (entry (.encrypt p t₁) (answer f (.encrypt p t₁)) :: world.history) :=
    ⟨f, (IdealCipher.matches_cons f world.history (.encrypt p t₁) _).mpr ⟨hmatch, rfl⟩⟩
  have hfresh' : FreshInput (⟨entry (.encrypt p t₁) (answer f (.encrypt p t₁)) :: world.history, hpos'⟩ :
      World (Bits lambda) (Bits lambda)) p t₂ := by
    intro e he hk
    rcases List.mem_cons.mp he with rfl | he'
    · exact hne
    · exact absurd hk (hfresh e he')
  have h := posterior_key_le ⟨entry (.encrypt p t₁) (answer f (.encrypt p t₁)) :: world.history, hpos'⟩ p t₂ hfresh' q
    (by simp only [List.length_cons]; exact hlen) layout c hfiber {layout.key (layout.output (f p t₁))}
  simp only [Finset.card_singleton, Nat.mul_one, Finset.mem_singleton] at h
  exact h

end
end SDitH.Proofs.SiblingKeys
