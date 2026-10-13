import SDitH.Proofs.PublicHashFresh

/-! Single-step runs in the shared world. A finished program's run returns
its value and leaves the world unchanged; a single cipher query's run
returns the fixed family's answer deterministically and records the entry.
These are the elementary run facts used by the coupling of the signing
procedures, alongside the fresh hash answer. -/

namespace SDitH.Proofs.SingleStepRuns

open Spec.SharedScheme Spec.HashCipherTrace Spec.HashCipherProgram Spec.DomainSeparation
open Spec.SlopeConsistencyGame (Out)
open scoped ENNReal

noncomputable section

variable {lambda s wit rnd : Nat}

/-- A finished program's run is the finished state with the world unchanged. -/
theorem runProgram_done {A : Type*} (budget : Nat) (value : A) (world : World lambda s wit rnd) :
    runProgram budget (.done value) world = PMF.pure (.done value, world) := by
  unfold runProgram
  cases budget with
  | zero =>
    simp only [runFixed, PMF.pure_map]
  | succ budget =>
    simp only [runFixed, procedure, PMF.pure_bind, PMF.pure_map]

/-- A single cipher query's run returns the fixed family's answer and records
the entry. -/
theorem runProgram_single_cipher {A : Type*} (request : Spec.IdealCipher.Query (Bits lambda) (Bits lambda))
    (next : Bits lambda → Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (world : World lambda s wit rnd) :
    runProgram 1 (.cipher request next) world =
      PMF.pure (next (Spec.IdealCipher.answer world.family request),
        ⟨world.family, world.hashTable, world.hashHistory,
          Spec.IdealCipher.entry request (Spec.IdealCipher.answer world.family request) :: world.cipherHistory,
          world.trace⟩) := by
  unfold runProgram
  simp only [runFixed, procedure, PMF.pure_bind, PMF.pure_map]

end
end SDitH.Proofs.SingleStepRuns
