import SDitH.Proofs.FreshKeyUniform
import SDitH.Spec.BAVCCipherProgram

/-! The leaf seed through the cipher layout. A seed's expansion is the
layout's output of the cipher's encryption, under the layout's key image of
the parent seed, of the layout's input image of the tweak; when the parent
key is fresh the encryption is uniform over blocks, and a layout whose
output map carries the uniform block to the uniform seed (the full layout
does so trivially) gives a uniform leaf seed. This is the per-call form of
the hidden leaf seed's uniformity; the accounting of the fresh-parent-key
event over the signing game remains separate. -/

namespace SDitH.Proofs.LeafSeedUniform

open Spec.IdealCipher Spec.BAVCCipherProgram Spec.DomainSeparation FreshKeyUniform
open scoped Classical ENNReal

noncomputable section

variable {lambda : Nat} {Key Block : Type*} [Fintype Key] [Fintype Block] [Nonempty Block]

/-- A layout whose output map sends the uniform block to the uniform seed. -/
def OutputUniform (layout : Layout lambda Key Block) : Prop :=
  (PMF.uniformOfFintype Block).map layout.output = PMF.uniformOfFintype (Bits lambda)

/-- The full layout's output is the identity, hence output-uniform. -/
theorem fullLayout_outputUniform : OutputUniform (fullLayout lambda) := by
  unfold OutputUniform fullLayout
  exact PMF.map_id _

/-- The expansion of a fresh parent key through an output-uniform layout is a
uniform seed: one encryption call's output image. -/
theorem leaf_uniform (layout : Layout lambda Key Block) (hout : OutputUniform layout) (world : World Key Block)
    (parent tweak : Bits lambda) (hkey : FreshKey world (layout.key parent)) :
    (query world (.encrypt (layout.key parent) (layout.input tweak))).map (fun result => layout.output result.1) =
      PMF.uniformOfFintype (Bits lambda) := by
  have h : (fun result : Block × World Key Block => layout.output result.1) = layout.output ∘ Prod.fst := rfl
  rw [h, ← PMF.map_comp, fresh_key_encrypt_uniform world (layout.key parent) hkey (layout.input tweak)]
  exact hout

end
end SDitH.Proofs.LeafSeedUniform
