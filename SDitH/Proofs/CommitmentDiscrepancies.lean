import SDitH.Spec.CommitmentChecks
import Mathlib.Tactic

namespace SDitH.Proofs

open Spec

/-- Algorithm 9 rejects on its first non-sibling branch if the path has the
length required by Algorithm 8. This is independent of cipher/hash behavior. -/
theorem reconstruction_rejects_full_path
    (queueLength node nextNode Topen lambda : Nat)
    (hq : 2 ≤ queueLength) (hs : nextNode ≠ Nat.xor node 1) :
    reconstructSiblingAction queueLength node nextNode (paddedPathBits Topen lambda)
      Topen lambda = .reject := by
  simp [reconstructSiblingAction, paddedPathBits, hq, hs]

/-- A first-iteration instance for Table 4's Category-I short parameters.
The hidden index in repetition 10 is 1, and the other ten hidden indices are 0:
the two largest leaf addresses are 22549 and 22537, with ten queued nodes left.
This only certifies the specified branch, not an end-to-end signature execution. -/
theorem categoryI_first_reconstruction_branch_rejects :
    reconstructSiblingAction 10 22549 22537 (paddedPathBits 109 128) 109 128 =
      .reject := by decide

/-- Algorithms 10 and 12 hash distinct serialized inputs whenever the encoded
witness correction has positive length. This is NOT a claim of collision
resistance or of distinct outputs for every concrete hash. -/
theorem line_hash_inputs_differ {Byte : Type*}
    (haux plain base deltaWitness : List Byte) (h : deltaWitness.length > 0) :
    commitLinesInput haux plain base deltaWitness ≠
      reconstructLinesInput haux plain base := by
  intro heq
  have := congrArg List.length heq
  simp only [commitLinesInput, reconstructLinesInput, List.length_append] at this
  omega

end SDitH.Proofs
