import SDitH.Spec.ByteSampling
import Mathlib.Algebra.BigOperators.Fin

/-! SampleIntegers, printed p. 18, through the first accepted candidate.
The displayed assignment is f_i = B % m, but B is undefined: only the bytes
B_0,...,B_3 and assembled value v have been defined. This module stops before
that assignment. A found candidate is not a returned sampled integer, and v is
not silently substituted for B. PRG initialization and the source byte stream
remain explicit. Observation fuel is not a source rejection condition. -/

namespace SDitH.Spec.IntegerSampling

open DomainSeparation ByteSampling

def wordBound : Nat := 2 ^ 32
instance : NeZero wordBound := ⟨pow_ne_zero 32 (by decide)⟩
abbrev Word := Fin wordBound

/-- The four little-endian bytes form the source's value v. The finite
encoding's equality to B0+256*B1+256^2*B2+256^3*B3 is proved separately. -/
def wordEquiv : (Fin 4 → Byte) ≃ Word :=
  finFunctionFinEquiv.trans (finCongr (by decide : 256 ^ 4 = wordBound))

def word32 (bytes : Fin 4 → Byte) : Word := wordEquiv bytes

/-- Largest multiple of m no greater than the bound, as printed. The source
requires positive m; the natural-number expression is also total outside it. -/
def threshold (bound m : Nat) : Nat := bound / m * m

def sourceThreshold (m : Nat) : Nat := threshold wordBound m

structure Candidate where
  value : Nat
  next : Reader

/-- Lines 3–5, including consumption of all four bytes. -/
def readCandidate (src : Reader) : Candidate :=
  ⟨(word32 (readBytes src 4)).val, advance src 4⟩

inductive Attempt where
  | rejected (next : Reader)
  /-- Line 6 accepted v. Line 7's undefined B is deliberately not evaluated. -/
  | accepted (candidate : Candidate)

def attemptWith (limit : Nat) (read : Reader → Candidate) (src : Reader) : Attempt :=
  let candidate := read src
  if candidate.value < limit then .accepted candidate
  else .rejected candidate.next

def attempt (m : Nat) (src : Reader) : Attempt :=
  attemptWith (sourceThreshold m) readCandidate src

inductive Observation where
  | pending (next : Reader)
  /-- Stops at the first accepted candidate, before the undefined assignment. -/
  | found (candidate : Candidate)

/-- Observe the repeated rejection prefix for one requested integer. This is
not a completed implementation of SampleIntegers' output assignment or vector. -/
def observeWith (limit : Nat) (read : Reader → Candidate) : Nat → Reader → Observation
  | 0, src => .pending src
  | fuel + 1, src =>
      match attemptWith limit read src with
      | .rejected next => observeWith limit read fuel next
      | .accepted candidate => .found candidate

def observeCandidate (m : Nat) : Nat → Reader → Observation :=
  observeWith (sourceThreshold m) readCandidate

end SDitH.Spec.IntegerSampling
