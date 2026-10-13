import SDitH.Assumptions

namespace SDitH.Proofs

open Spec Assumptions

variable {F : Type*} [Field F] [Fintype F] {n k : Nat}

/-- The explicitly proposed planted-instance model samples solvable instances.
This concerns the mathematical model, not the seed-based key generator. -/
theorem plantedSD_has_solution (w : Nat) (errors : Finset (Fin n → F))
    (hne : errors.Nonempty) (hspace : ExactWeightSampleSpace w errors)
    (inst : SDInstance F n k) (hinst : inst ∈ (plantedSD errors hne).support) :
    ∃ x, SDSolution inst w x := by
  obtain ⟨H, _, hmap⟩ := (PMF.mem_support_bind_iff _ _ inst).mp hinst
  obtain ⟨x, hxmem, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmap
  rw [← heq]
  exact ⟨x, rfl, (hspace x).mp ((PMF.mem_support_uniformOfFinset_iff hne x).mp hxmem)⟩

end SDitH.Proofs
