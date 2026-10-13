import SDitH.Proofs.LeafSeedUniform
import SDitH.Proofs.IdealCipherJoint

/-! The leaf seed under the posterior family. The signing game answers
cipher queries from a family fixed at key generation; the joint-law
correspondence resamples that family uniformly among those consistent
with the history, so a query's answer is distributed as the lazy query's.
Under a fresh parent key and an output-uniform layout, the family's answer
to the leaf expansion, mapped through the layout's output, is uniform over
seeds; this is the per-call form used when the family is conditioned on the
history before the hidden leaf's expansion. -/

namespace SDitH.Proofs.PosteriorLeafUniform

open Spec.IdealCipher Spec.BAVCCipherProgram Spec.DomainSeparation FreshKeyUniform LeafSeedUniform
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat} {Key Block : Type*} [Fintype Key] [Fintype Block] [Nonempty Block]

omit [Nonempty Block] in
/-- The lazy query's answer is the posterior family's answer. -/
theorem query_fst_eq (world : World Key Block) (request : Query Key Block) :
    (query world request).map Prod.fst =
      (PMF.uniformOfFintype (Candidates world)).map (fun family => answer family.val request) := by
  unfold query
  rw [PMF.map_comp]
  rfl

/-- Under a fresh parent key, the posterior family's answer to the leaf
expansion, through an output-uniform layout, is a uniform seed. -/
theorem posterior_leaf_uniform (layout : Layout lambda Key Block) (hout : OutputUniform layout) (world : World Key Block)
    (parent tweak : Bits lambda) (hkey : FreshKey world (layout.key parent)) :
    (PMF.uniformOfFintype (Candidates world)).map
        (fun family => layout.output (answer family.val (.encrypt (layout.key parent) (layout.input tweak)))) =
      PMF.uniformOfFintype (Bits lambda) := by
  have h := leaf_uniform layout hout world parent tweak hkey
  rw [show (fun result : Block × World Key Block => layout.output result.1) = layout.output ∘ Prod.fst from rfl,
    ← PMF.map_comp, query_fst_eq, PMF.map_comp] at h
  exact h

end
end SDitH.Proofs.PosteriorLeafUniform
