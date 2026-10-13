import SDitH.Proofs.NodeExchange
import SDitH.Proofs.IntegerSamplingProbability

/-! Invariance of a product distribution under a product map. A pair of
independent draws is invariant under a map acting independently on the two
components when each component's law is invariant under its map; and a
uniform draw is invariant under a transposition. -/

namespace SDitH.Proofs.ProductSwap

open scoped Classical

noncomputable section

variable {α β : Type*}

/-- The product of two distributions. -/
def product (pr : PMF α) (pf : PMF β) : PMF (α × β) :=
  pr.bind fun r => pf.map fun g => (r, g)

/-- A product map preserves the product when each map preserves its
component. -/
theorem product_map_eq (pr : PMF α) (pf : PMF β) (e₁ : α → α) (e₂ : β → β) (h₁ : pr.map e₁ = pr)
    (h₂ : pf.map e₂ = pf) : (product pr pf).map (fun x => (e₁ x.1, e₂ x.2)) = product pr pf := by
  unfold product
  rw [PMF.map_bind]
  calc (pr.bind fun r => (pf.map fun g => (r, g)).map fun x => (e₁ x.1, e₂ x.2))
      = pr.bind fun r => (pf.map e₂).map fun g => (e₁ r, g) := by
        refine congrArg _ (funext fun r => ?_)
        rw [PMF.map_comp, PMF.map_comp]
        rfl
    _ = (pr.map e₁).bind fun r => pf.map fun g => (r, g) := by
        rw [h₂, PMF.bind_map]
        rfl
    _ = pr.bind fun r => pf.map fun g => (r, g) := by rw [h₁]

/-- A uniform draw is invariant under a transposition. -/
theorem uniform_map_swap [Fintype α] [Nonempty α] (a b : α) :
    (PMF.uniformOfFintype α).map (Equiv.swap a b) = PMF.uniformOfFintype α :=
  IntegerSamplingProbability.map_uniform_equiv (Equiv.swap a b)

end
end SDitH.Proofs.ProductSwap
