import SDitH.Proofs.CipherResample
import SDitH.Proofs.IdealCipherCapacity

/-! Fresh-input answers under the posterior family. The posterior family's
answer to a query is the lazily sampled answer, so at a fresh input of a
key the answer hits a target block with probability at most the inverse
of the remaining block count, satisfies an event with probability at
most the event's count over the remaining block count, and lies in a
finite set with probability at most the set's size over the remaining
block count. -/

namespace SDitH.Proofs.PosteriorFresh

open Spec.IdealCipher (Family Entry Matches Candidates World answer)
open IdealCipherFresh IdealCipherCapacity CipherResample
open scoped Classical ENNReal

noncomputable section

variable {Key Block : Type*} [Fintype Key] [Fintype Block]

/-- The posterior family's answer is the lazily sampled answer. -/
theorem posterior_answer (world : World Key Block) (request : Spec.IdealCipher.Query Key Block) :
    (posterior world.history).map (fun f => answer f request) =
      (Spec.IdealCipher.query world request).map Prod.fst := by
  rw [posterior_world]
  unfold Spec.IdealCipher.query
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- A fresh-input posterior answer satisfies an event with probability at
most the event's count over the remaining block count. -/
theorem posterior_event_le (world : World Key Block) (key : Key) (input : Block)
    (hfresh : FreshInput world key input) (q : Nat) (hlen : world.history.length ≤ q) (event : Block → Prop) :
    ((posterior world.history).map (fun f => decide (event (f key input)))) true ≤
      (Fintype.card {output : Block // event output} : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞) := by
  have h := fresh_encrypt_event_budget_bound world key input hfresh q hlen event
  have hc : (fun result : Block × World Key Block => decide (event result.1)) =
      (fun output : Block => decide (event output)) ∘ Prod.fst := rfl
  rw [hc, ← PMF.map_comp, ← posterior_answer world (.encrypt key input), PMF.map_comp] at h
  exact h

/-- A fresh-input posterior answer hits a target with probability at most
the inverse of the remaining block count. -/
theorem posterior_target_le (world : World Key Block) (key : Key) (input target : Block)
    (hfresh : FreshInput world key input) (q : Nat) (hlen : world.history.length ≤ q) :
    ((posterior world.history).map (fun f => decide (f key input = target))) true ≤
      ((Fintype.card Block - q : Nat) : ℝ≥0∞)⁻¹ := by
  simpa using posterior_event_le world key input hfresh q hlen (fun output => output = target)

/-- A fresh-input posterior answer lies in a finite set with probability at
most the set's size over the remaining block count. -/
theorem posterior_mem_le (world : World Key Block) (key : Key) (input : Block)
    (hfresh : FreshInput world key input) (q : Nat) (hlen : world.history.length ≤ q) (T : Finset Block) :
    ((posterior world.history).map (fun f => decide (f key input ∈ T))) true ≤
      (T.card : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞) := by
  have h := posterior_event_le world key input hfresh q hlen (fun output => output ∈ T)
  simpa [Fintype.card_coe] using h

end
end SDitH.Proofs.PosteriorFresh
