import SDitH.Spec.Keccak
import SDitH.Spec.ByteSampling
import SDitH.Spec.FieldRepresentation

/-! FIPS 202 Algorithms 8–9 and §6.2; SDitH §3.2.1 and Table 1.
Inputs and outputs are bit strings of arbitrary length. `bitStream` expresses
the standard's infinite-output view, so output length never changes a bit.
This is a concrete deterministic function, not an ideal random oracle.
-/

namespace SDitH.Spec.SHAKE

open DomainSeparation

structure Rate where
  value : Nat
  positive : 0 < value
  le_width : value ≤ 1600

/-- Natural-number form of (-m-2) mod r, including the zero case. -/
def padZeros (r : Rate) (m : Nat) : Nat :=
  (r.value - (m + 2) % r.value) % r.value
def padding (r : Rate) (m : Nat) : List Bool :=
  true :: (List.replicate (padZeros r m) false ++ [true])
def padded (r : Rate) (input : List Bool) : List Bool :=
  input ++ padding r input.length
def block (r : Rate) (input : List Bool) (i : Nat) : Bits r.value :=
  fun j => input.getD (r.value * i + j.val) false

/-- XOR with the rate-bit block followed by zero capacity bits. -/
def inject (r : Rate) (s : Keccak.State) (p : Bits r.value) : Keccak.State :=
  Keccak.ofBits fun x y z => Keccak.bits s x y z ^^
    if h : (Keccak.stringIndex x y z).val < r.value then
      p ⟨(Keccak.stringIndex x y z).val, h⟩ else false
def absorbThrough (r : Rate) (input : List Bool) : Nat → Keccak.State
  | 0 => Keccak.zero
  | n + 1 => Keccak.keccak (inject r (absorbThrough r input n) (block r input n))
def absorb (r : Rate) (input : List Bool) : Keccak.State :=
  let p := padded r input
  absorbThrough r p (p.length / r.value)

def squeezeBit (r : Rate) (s : Keccak.State) (i : Nat) : Bool :=
  Keccak.toString (Keccak.keccak^[i / r.value] s)
    ⟨i % r.value, lt_of_lt_of_le (Nat.mod_lt _ r.positive) r.le_width⟩
/-- The append/permutation loop of Algorithm 8, stopped after n rate blocks.
The proofs relate every finite observation of this loop to squeezeBit. -/
def squeezeBlocks (r : Rate) (s : Keccak.State) : Nat → List Bool
  | 0 => []
  | n + 1 => (List.ofFn fun j : Fin r.value =>
      Keccak.toString s ⟨j.val, lt_of_lt_of_le j.isLt r.le_width⟩) ++
    squeezeBlocks r (Keccak.keccak s) n
def sponge (r : Rate) (input : List Bool) (d : Nat) : Bits d :=
  fun i => squeezeBit r (absorb r input) i.val

def rate128 : Rate := ⟨1344, by decide, by decide⟩
def rate256 : Rate := ⟨1088, by decide, by decide⟩
def suffix : List Bool := [true, true, true, true]
def shake128 (message : List Bool) (d : Nat) : Bits d :=
  sponge rate128 (message ++ suffix) d
def shake256 (message : List Bool) (d : Nat) : Bits d :=
  sponge rate256 (message ++ suffix) d

def categoryRate : FieldRepresentation.Category → Rate
  | .i => rate128
  | .iii => rate256
  | .v => rate256
def bitStream (category : FieldRepresentation.Category) (message : List Bool) : Nat → Bool :=
  squeezeBit (categoryRate category) (absorb (categoryRate category) (message ++ suffix))
def hash (category : FieldRepresentation.Category) (message : List Bool) :
    Bits (2 * FieldRepresentation.width category) := fun i => bitStream category message i.val

/-- Consecutive output bytes, low bit first within each byte. -/
def byteStream (category : FieldRepresentation.Category) (message : List Bool) : Nat → Byte :=
  fun i => (Keccak.word (fun j : Fin 8 => bitStream category message (8 * i + j.val))).toFin
def reader (category : FieldRepresentation.Category) (message : List Bool) : ByteSampling.Reader :=
  ⟨byteStream category message, 0⟩

end SDitH.Spec.SHAKE
