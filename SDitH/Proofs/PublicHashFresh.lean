import SDitH.Spec.SharedScheme
import SDitH.Proofs.FreshHashUniform

/-! The shared world's public hash query at a fresh input answers with a
uniform product value: the one-step run of the single-hash program is the
random oracle's query followed by the terminal state, so the public
oracle's digest answer at an absent input is the uniform digest, and the
mask answer the uniform mask. These are the random-oracle facts in the
shared world used by the coupling of the signing procedures. -/

namespace SDitH.Proofs.PublicHashFresh

open Spec.SharedScheme Spec.HashCipherTrace Spec.HashCipherProgram Spec.RandomOracle Spec.DomainSeparation
open Spec.SlopeConsistencyGame (Out)
open scoped ENNReal

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The one-step run of a single hash program is the oracle query followed by
the terminal state. -/
theorem runProgram_single_hash {A : Type*} (input : List Bool)
    (next : Out lambda s wit rnd → Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (hnext : ∀ answer, ∃ value, next answer = .done value) (world : World lambda s wit rnd) :
    (runProgram 1 (.hash input next) world).map Prod.fst =
      (query world.hashTable input).map (fun result => next result.1) := by
  unfold runProgram
  simp only [runFixed, procedure, PMF.pure_bind, PMF.map_bind]
  rw [show PMF.map (fun result : Out lambda s wit rnd × (List Bool → Option (Out lambda s wit rnd)) => next result.1)
      (query world.hashTable input) = (query world.hashTable input).bind (fun result => PMF.pure (next result.1)) from rfl]
  congr 1
  · congr
    exact Subsingleton.elim _ _
  · funext result
    obtain ⟨value, hv⟩ := hnext result.1
    simp [hv, PMF.pure_map, mark]

/-- The public hash answer at an absent input is the uniform digest. -/
theorem publicOracle_hash_fresh (input : List Bool) (world : World lambda s wit rnd)
    (h : world.hashTable input = none) :
    (publicOracle (.hash input) world).map Prod.fst =
      (PMF.uniformOfFintype (Out lambda s wit rnd)).map (fun pair => Answer.digest pair.1) := by
  unfold publicOracle
  rw [PMF.map_comp]
  have hrun := runProgram_single_hash input (fun answer => .done answer.1) (fun answer => ⟨answer.1, rfl⟩) world
  have hfresh := FreshHashUniform.query_fresh_uniform world.hashTable input h
  calc (runProgram 1 (.hash input fun answer => .done answer.1) world).map
        ((fun (r : Answer lambda s wit rnd × World lambda s wit rnd) => r.1) ∘ fun result =>
          (Answer.digest (match result.1 with | .done value => value | _ => fun _ => false), result.2))
      = ((runProgram 1 (.hash input fun answer => .done answer.1) world).map Prod.fst).map
          (fun p => Answer.digest (match p with | .done value => value | _ => fun _ => false)) := by
        rw [PMF.map_comp]
        rfl
    _ = ((query world.hashTable input).map Prod.fst).map (fun pair => Answer.digest pair.1) := by
        rw [hrun, PMF.map_comp, PMF.map_comp]
        rfl
    _ = _ := by rw [hfresh]

end
end SDitH.Proofs.PublicHashFresh
