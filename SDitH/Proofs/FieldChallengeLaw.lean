import SDitH.Proofs.FieldByteProbability
import SDitH.Spec.DetailedPIOPChallenges

/-! Connect the actual sequential byte sampler, with its explicit representation
order and consumption counts, to the two-vector law used by the detailed PIOP
probability proofs. This concerns uniform byte input, not a concrete XOF or a
Fiat-Shamir oracle. The equality holds for arbitrary subsequent computation.
-/

namespace SDitH.Proofs.FieldChallengeLaw

open Spec.DomainSeparation Spec.FieldRepresentation Spec.FieldBytes Spec.ByteSampling
open Spec.DetailedPIOPChallenges Spec.Batching

theorem batching_challenges_law (category : Category) (order : ByteOrder category)
    (r w count₁ count₂ : Nat)
    (h₁ : blockCount r (width category) * byteCount category ≤ count₁)
    (h₂ : w * byteCount category ≤ count₂) :
    (PMF.uniformOfFintype (Fin (count₁ + count₂) → Byte)).map
      (fun bytes => (Spec.FieldBytes.expandBatching category order (finiteReader bytes).stream
        (blockCount r (width category)) w count₁ count₂ h₁ h₂).value) =
      batchingChallenges (QuotientRing category) r w (width category) := by
  rw [FieldByteProbability.batching_uniform, batchingChallenges, UniformVectors.uniform_pair]

/-- Replacing only the first-stage uniform byte experiment by the derived
challenge law preserves every later randomized computation exactly. -/
theorem batching_continuation_law {A : Type*} (category : Category) (order : ByteOrder category)
    (r w count₁ count₂ : Nat)
    (h₁ : blockCount r (width category) * byteCount category ≤ count₁)
    (h₂ : w * byteCount category ≤ count₂)
    (next : Challenges (QuotientRing category) r w (width category) → PMF A) :
    (PMF.uniformOfFintype (Fin (count₁ + count₂) → Byte)).bind
      (fun bytes => next (Spec.FieldBytes.expandBatching category order (finiteReader bytes).stream
        (blockCount r (width category)) w count₁ count₂ h₁ h₂).value) =
      (batchingChallenges (QuotientRing category) r w (width category)).bind next := by
  rw [← batching_challenges_law category order r w count₁ count₂ h₁ h₂, PMF.bind_map]
  rfl

end SDitH.Proofs.FieldChallengeLaw
