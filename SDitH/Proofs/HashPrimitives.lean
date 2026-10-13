import SDitH.Spec.HashPrimitives
import SDitH.Proofs.SHAKE

namespace SDitH.Proofs.HashPrimitives

open Spec Spec.DomainSeparation Spec.FieldRepresentation Spec.HashPrimitives

theorem hash_bytes_enough (category : Category) :
    2 * width category ≤ 8 * ((2 * width category) / 8) := by
  cases category <;> decide

/-- Hash and XOF are the same SHAKE instance and input, with Hash selecting
exactly its specified 2*lambda-bit prefix. -/
theorem hash_from_reader (category : Category) (input : List Bool) :
    (ByteSampling.sampleBinary (SHAKE.reader category input) (2 * width category)
      ((2 * width category) / 8) (hash_bytes_enough category)).value = SHAKE.hash category input := by
  funext i
  have h := Proofs.SHAKE.sampleBinary_reader category input 0 (2 * width category)
    ((2 * width category) / 8) (hash_bytes_enough category) i
  simpa only [ByteSampling.advance, SHAKE.reader, Nat.add_zero, Nat.mul_zero, Nat.zero_add,
    SHAKE.hash] using h

theorem bavc_domain_hash (category : Category) (leafCount : Nat) (variant : Grinding)
    (encStar : Bits (width category) → Bits (width category) → Bits (width category))
    (payload : List Bool) :
    BAVC.hashBavc (bavcPrimitives category leafCount variant encStar) payload =
      domainHash category 1 payload := rfl

theorem bavc_commitment_hash (category : Category) (tau N : Nat) (variant : Grinding)
    (encStar : Bits (width category) → Bits (width category) → Bits (width category))
    (salt : Bits (width category)) (tree : BAVC.Tree (width category) tau N) :
    (BAVC.commitFromTree (bavcPrimitives category (tau * N) variant encStar) salt tree).hcom =
      domainHash category 1 (List.ofFn salt ++ BAVC.serializeArray (fun e : Fin tau =>
        domainHash category 1 (BAVC.serializeArray (fun i : Fin N =>
          SeedPrimitives.commitSeed (tau * N) variant encStar salt (tree (BAVC.leafNode e i))
            (SeedTree.leafOffset e i))))) := rfl

end SDitH.Proofs.HashPrimitives
