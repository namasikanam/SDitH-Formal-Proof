import SDitH.Proofs.LeafSeedUniform
import SDitH.Proofs.UniformVectors

/-! The truncated layout is output-uniform. Category III expands 192-bit
seeds through a 256-bit cipher and keeps the first 192 bits of the output;
restricting a uniform bit vector to an injective set of coordinates is
uniform, so the projection carries the uniform block to the uniform seed.
Hence both submitted layouts are output-uniform and the fresh-parent leaf
seed is uniform for each. -/

namespace SDitH.Proofs.TruncatedLayoutUniform

open Spec.BAVCCipherProgram Spec.DomainSeparation Spec.IdealCipherSeed LeafSeedUniform
open scoped Classical ENNReal

noncomputable section

/-- The coordinate embedding of the first 192 positions. -/
def embed192 (i : Fin 192) : Fin 256 := ⟨i.val, by have := i.isLt; omega⟩

theorem embed192_injective : Function.Injective embed192 := by
  intro i j h
  have h' : (embed192 i).val = (embed192 j).val := congrArg Fin.val h
  exact Fin.ext h'

/-- The 192-bit projection of a uniform 256-bit block is uniform. -/
theorem project192_uniform :
    (PMF.uniformOfFintype (Bits 256)).map project192 = PMF.uniformOfFintype (Bits 192) :=
  UniformVectors.map_uniform_restrict embed192 embed192_injective

/-- The truncated layout is output-uniform. -/
theorem truncatedLayout_outputUniform : OutputUniform truncatedLayout :=
  project192_uniform

end
end SDitH.Proofs.TruncatedLayoutUniform
