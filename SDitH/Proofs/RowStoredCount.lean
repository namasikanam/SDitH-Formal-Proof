import SDitH.Proofs.RowStoredReduce
import SDitH.Proofs.PosteriorFresh

/-! Counting the last blocks that hit a fixed set. The last execution's
row query is injective in the last block, so the blocks whose row query
lies in a finite set number at most the set's size; through the layout's
output map with fibers of bounded size, the cipher outputs whose row query
lies in the set number at most the fiber bound times the set's size; so
under the posterior family at a fresh input the row query lies in the set
with probability at most that count over the remaining block count. -/

namespace SDitH.Proofs.RowStoredCount

open Spec.DomainSeparation
open Spec.IdealCipher (World)
open IdealCipherFresh RowStoredReduce HeadCommitSplit PosteriorFresh CipherResample
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa : Nat}

theorem card_instance_eq {α : Type*} (i₁ i₂ : Fintype α) : @Fintype.card α i₁ = @Fintype.card α i₂ := by
  cases Subsingleton.elim i₁ i₂
  rfl

/-- The cipher outputs whose row query lies in a finite set number at most
the fiber bound times the set's size, under any finiteness instance. -/
theorem count_hits (htau : tau ≠ 0) (v : BeforeData lambda tau kappa) (output : Bits lambda → Bits lambda) (c : Nat)
    (hfiber : ∀ b, Fintype.card {r : Bits lambda // output r = b} ≤ c) (T : Finset (List Bool))
    (inst : Fintype {r : Bits lambda // lastRowQuery htau v (output r) ∈ T}) :
    @Fintype.card {r : Bits lambda // lastRowQuery htau v (output r) ∈ T} inst ≤ c * T.card := by
  rw [card_instance_eq inst inferInstance, Fintype.card_subtype]
  refine Finset.card_le_mul_card_image_of_maps_to (f := fun r => lastRowQuery htau v (output r)) (t := T)
    (fun r hr => (Finset.mem_filter.mp hr).2) c (fun x _ => ?_)
  by_cases hx : ∃ b, lastRowQuery htau v b = x
  · obtain ⟨b, rfl⟩ := hx
    calc _ ≤ (Finset.univ.filter fun r : Bits lambda => output r = b).card :=
          Finset.card_le_card fun r hr => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            exact lastRowQuery_injective htau v hr.2
      _ = Fintype.card {r : Bits lambda // output r = b} := (Fintype.card_subtype _).symm
      _ ≤ c := hfiber b
  · have hempty : ((Finset.univ.filter fun r : Bits lambda => lastRowQuery htau v (output r) ∈ T).filter
        fun r => lastRowQuery htau v (output r) = x) = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨-, hr⟩
      exact hx ⟨output r, hr⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le c

/-- Under the posterior family at a fresh input, the last execution's row
query lies in a finite set with probability at most the fiber bound times
the set's size over the remaining block count. -/
theorem posterior_row_le (world : World (Bits lambda) (Bits lambda)) (key input : Bits lambda)
    (hfresh : FreshInput world key input) (q : Nat) (hlen : world.history.length ≤ q) (htau : tau ≠ 0)
    (v : BeforeData lambda tau kappa) (output : Bits lambda → Bits lambda) (c : Nat)
    (hfiber : ∀ b, Fintype.card {r : Bits lambda // output r = b} ≤ c) (T : Finset (List Bool)) :
    ((posterior world.history).map (fun f => decide (lastRowQuery htau v (output (f key input)) ∈ T))) true ≤
      ((c * T.card : Nat) : ℝ≥0∞) / ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞) := by
  have h := posterior_event_le world key input hfresh q hlen (fun r => lastRowQuery htau v (output r) ∈ T)
  refine le_trans ?_ (h.trans (ENNReal.div_le_div_right
    ((Nat.cast_le (α := ℝ≥0∞)).mpr (count_hits htau v output c hfiber T _)) _))
  exact le_of_eq (congrArg (fun p : PMF Bool => p true) (congrArg (fun g => PMF.map g (posterior world.history))
    (funext fun f => by congr)))

end
end SDitH.Proofs.RowStoredCount
