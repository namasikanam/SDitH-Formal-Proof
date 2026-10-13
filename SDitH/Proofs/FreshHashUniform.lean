import SDitH.Spec.RandomOracle
import SDitH.Proofs.IntegerSamplingProbability

/-! A fresh hash answer is uniform. The random oracle answers an absent
input by a uniform digest stored at that input, and a present input by its
stored digest; so the answer's distribution at an absent input is uniform,
whatever the input. This is the random-oracle input of the signing
procedures' coupling: the honest and simulated signers' lines queries are
at different inputs, but both answers are uniform when fresh. -/

namespace SDitH.Proofs.FreshHashUniform

open Spec.RandomOracle
open scoped Classical ENNReal

noncomputable section

variable {Input Output : Type*} [DecidableEq Input] [Fintype Output] [Nonempty Output]

/-- At an absent input the answer is uniform. -/
theorem query_fresh_uniform (table : Input → Option Output) (input : Input) (h : table input = none) :
    (query table input).map Prod.fst = PMF.uniformOfFintype Output := by
  unfold query
  rw [h]
  simp only [PMF.map_comp]
  exact PMF.map_id _

/-- At a present input the answer is the stored digest. -/
theorem query_stored (table : Input → Option Output) (input : Input) (answer : Output) (h : table input = some answer) :
    (query table input).map Prod.fst = PMF.pure answer := by
  unfold query
  rw [h, PMF.pure_map]

/-- At an absent input the resulting table stores the answer at the input. -/
theorem query_fresh_table (table : Input → Option Output) (input : Input) (h : table input = none)
    (result : Output × (Input → Option Output)) (hr : result ∈ (query table input).support) :
    result.2 = Function.update table input (some result.1) := by
  unfold query at hr
  rw [h] at hr
  obtain ⟨answer, _, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  subst hres
  rfl

/-- Two absent inputs' answers have the same distribution, whatever the inputs. -/
theorem query_fresh_congr (table table' : Input → Option Output) (input input' : Input) (h : table input = none)
    (h' : table' input' = none) :
    (query table input).map Prod.fst = (query table' input').map Prod.fst := by
  rw [query_fresh_uniform table input h, query_fresh_uniform table' input' h']

end
end SDitH.Proofs.FreshHashUniform
