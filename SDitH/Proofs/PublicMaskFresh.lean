import SDitH.Proofs.PublicHashFresh

/-! The shared world's public mask query at a fresh input answers with the
uniform mask: the product-valued oracle's fresh answer is uniform, and the
mask is its second component. Together with the digest case, every public
hash-side answer at an absent input is uniform in its component. -/

namespace SDitH.Proofs.PublicMaskFresh

open Spec.SharedScheme Spec.HashCipherTrace Spec.HashCipherProgram Spec.RandomOracle Spec.DomainSeparation
open Spec.SlopeConsistencyGame (Out)
open PublicHashFresh
open scoped ENNReal

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The public mask answer at an absent input is the uniform mask component. -/
theorem publicOracle_mask_fresh (input : List Bool) (world : World lambda s wit rnd)
    (h : world.hashTable input = none) :
    (publicOracle (.mask input) world).map Prod.fst =
      (PMF.uniformOfFintype (Out lambda s wit rnd)).map (fun pair => Answer.mask pair.2) := by
  unfold publicOracle
  rw [PMF.map_comp]
  have hrun := runProgram_single_hash input (fun answer => .done answer.2) (fun answer => ⟨answer.2, rfl⟩) world
  have hfresh := FreshHashUniform.query_fresh_uniform world.hashTable input h
  calc (runProgram 1 (.hash input fun answer => .done answer.2) world).map
        ((fun (r : Answer lambda s wit rnd × World lambda s wit rnd) => r.1) ∘ fun result =>
          (Answer.mask (match result.1 with | .done value => value | _ => 0), result.2))
      = ((runProgram 1 (.hash input fun answer => .done answer.2) world).map Prod.fst).map
          (fun p => Answer.mask (match p with | .done value => value | _ => 0)) := by
        rw [PMF.map_comp]
        rfl
    _ = ((query world.hashTable input).map Prod.fst).map (fun pair => Answer.mask pair.2) := by
        rw [hrun, PMF.map_comp, PMF.map_comp]
        rfl
    _ = _ := by rw [hfresh]

end
end SDitH.Proofs.PublicMaskFresh
