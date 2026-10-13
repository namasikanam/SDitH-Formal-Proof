import SDitH.Spec.IntegerSamplingVector

/-! Observable finite traces of the literal integer sampler. A trace retains
the result tag, all sampled values, cursor positions and the offending integer
at an undefined assignment. It omits the reader's unconsumed stream function.
This projection permits finite-output/stream correspondence without asserting
that different readers have equal infinite tails. It does not change sampling.
-/

namespace SDitH.Spec.IntegerSampling

inductive VectorTrace (m n : Nat) where
  | pending (values : List (Fin m)) (cursor : Nat)
  | undefinedAssignment (values : List (Fin m)) (cursor candidate nextCursor : Nat)
  | returned (values : Vector (Fin m) n) (cursor : Nat)

def vectorTrace {m n : Nat} : VectorObservation m n → VectorTrace m n
  | .pending state => .pending state.values state.next.position
  | .undefinedAssignment state candidate =>
      .undefinedAssignment state.values state.next.position candidate.value candidate.next.position
  | .returned values next => .returned values next.position

end SDitH.Spec.IntegerSampling
