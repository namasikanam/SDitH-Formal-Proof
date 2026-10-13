import SDitH.Spec.IntegerSampling

/-! The complete SampleIntegers loop, printed p. 18, with an explicit binding
for the undeclared natural-number variable B in its accepted assignment.
No default B=v substitution is made. An absent binding stops at that read;
the accepted candidate, accumulated prefix and exact reader remain visible.
Fuel observes four-byte attempts, not source rejection or timeout behavior.
-/

namespace SDitH.Spec.IntegerSampling

open DomainSeparation ByteSampling

structure PartialVector (m n : Nat) where
  values : List (Fin m)
  bounded : values.length ≤ n
  next : Reader

inductive VectorObservation (m n : Nat) where
  | pending (state : PartialVector m n)
  | undefinedAssignment (state : PartialVector m n) (candidate : Candidate)
  | returned (values : Vector (Fin m) n) (next : Reader)

/-- The existing output coordinates, without default filling or truncation. -/
def finishedVector {m n : Nat} (state : PartialVector m n) (complete : state.values.length = n) :
    Vector (Fin m) n :=
  Vector.ofFn fun j => state.values[j.val]'(by have hj := j.isLt; omega)

def vectorPending {m n : Nat} (state : PartialVector m n) : VectorObservation m n :=
  if complete : state.values.length = n then .returned (finishedVector state complete) state.next
  else .pending state

/-- Every accepted iteration reads the same source name B. An external binding
is a natural-number value, with no assertion relating it to candidate.value.
The continuation is the next observation of this same loop, not a supplied
sampler contract. Factoring one step keeps recursive equations small. -/
def vectorStep (m : Nat) (positive : 0 < m) (n : Nat) (binding : Option Nat)
    (resume : PartialVector m n → VectorObservation m n) (state : PartialVector m n) :
    VectorObservation m n :=
  if complete : state.values.length = n then .returned (finishedVector state complete) state.next
  else
    match attempt m state.next with
    | .rejected next => resume ⟨state.values, state.bounded, next⟩
    | .accepted candidate =>
      match binding with
      | none => .undefinedAssignment state candidate
      | some value => resume
        ⟨state.values ++ [⟨value % m, Nat.mod_lt _ positive⟩],
          by have hb := state.bounded; simp only [List.length_append, List.length_singleton]; omega,
          candidate.next⟩

def observeVector (m : Nat) (positive : 0 < m) (n : Nat) (binding : Option Nat) :
    Nat → PartialVector m n → VectorObservation m n
  | 0 => vectorPending
  | fuel + 1 => vectorStep m positive n binding (observeVector m positive n binding fuel)

/-- The specified initial i=1 corresponds to no completed output coordinates.
An empty request returns immediately even with no binding and zero fuel. -/
def sampleVectorWithBinding (m : Nat) (positive : 0 < m) (n : Nat) (binding : Option Nat)
    (fuel : Nat) (src : Reader) : VectorObservation m n :=
  observeVector m positive n binding fuel ⟨[], by simp, src⟩

def sampleVector (m : Nat) (positive : 0 < m) (n fuel : Nat) (src : Reader) :
    VectorObservation m n := sampleVectorWithBinding m positive n none fuel src

end SDitH.Spec.IntegerSampling
