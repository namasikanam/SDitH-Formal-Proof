import SDitH.Spec.DomainSeparation
import Mathlib.Data.Matrix.Basic

/-! SampleFieldElements and the matrix/challenge sampling order, printed pp. 18–19.

The source permits a byte count n' at least as large as the requested data; it
does not give a general rule for choosing it or retaining unused bits. That count
is an explicit input. A reader advances by whole consumed bytes. Extension-field
decoding is a separate function input at the representation boundary. Neither
the byte source nor the decoder is presumed random, injective, or cryptographic.
-/

namespace SDitH.Spec.ByteSampling

open DomainSeparation

structure Reader where
  stream : Nat → Byte
  position : Nat

def advance (src : Reader) (count : Nat) : Reader :=
  { stream := src.stream, position := src.position + count }

def readBytes (src : Reader) (count : Nat) : Fin count → Byte :=
  fun j => src.stream (src.position + j.val)

/-- A finite byte sample viewed as a reader. The zero extension only makes the
stream total; uses of this model must stay within the supplied bytes. -/
def finiteReader {count : Nat} (bytes : Fin count → Byte) : Reader :=
  ⟨fun j => if h : j < count then bytes ⟨j, h⟩ else 0, 0⟩

structure Result (α : Type*) where
  value : α
  next : Reader

/-- Return the first n little-endian bits of the consumed bytes, in byte order.
Bool is the two-element representation here; no extension-field map is involved.
The bound also prevents a zero-byte read when a bit is requested. -/
def sampleBinary (src : Reader) (n count : Nat) (enough : n ≤ 8 * count) :
    Result (Bits n) :=
  { value := fun j =>
      (readBytes src count ⟨j.val / 8, by have hj := j.isLt; omega⟩).val.testBit (j.val % 8)
    next := advance src count }

/-- Return n consecutive packs of b bytes through the supplied field decoder.
For the source's F_(2^lambda), b is lambda/8. The caller must separately connect
the decoder to the specified polynomial basis. -/
def sampleExtension {F : Type*} (src : Reader) (b n count : Nat)
    (enough : n * b ≤ count) (decode : (Fin b → Byte) → F) :
    Result (Fin n → F) :=
  { value := fun i => decode (fun j => readBytes src count
      ⟨i.val * b + j.val, by
        have hi := i.isLt
        have hj := j.isLt
        have hmul : (i.val + 1) * b ≤ n * b := Nat.mul_le_mul_right b hi
        simp only [Nat.add_mul, Nat.one_mul] at hmul
        omega⟩)
    next := advance src count }

/-- The actual increasing-row sampling loop with one explicit byte count per
call. It is also the column-sampling loop of ExpandH before transposition. -/
def sampleRows (src : Reader) (cols count : Nat) (enough : cols ≤ 8 * count) :
    (rows : Nat) → Result (Matrix (Fin rows) (Fin cols) Bool)
  | 0 => { value := Fin.elim0, next := src }
  | rows + 1 =>
    let first := sampleBinary src cols count enough
    let tail := sampleRows first.next cols count enough rows
    { value := Fin.cons first.value tail.value, next := tail.next }

/-- ExpandConsistencyChallenge samples lambda+B rows, each of length ell.
The initialized XOF is supplied as its byte stream. -/
def expandConsistency (xof : Nat → Byte) (lambda B ell count : Nat)
    (enough : ell ≤ 8 * count) :
    Result (Matrix (Fin (lambda + B)) (Fin ell) Bool) :=
  sampleRows ⟨xof, 0⟩ ell count enough (lambda + B)

/-- The printed ExpandH pseudocode samples columns. This transcribes that order
without identifying it with the conflicting prose claim of row-wise sampling. -/
def expandHColumns (prg : Nat → Byte) (rows cols count : Nat)
    (enough : rows ≤ 8 * count) : Result (Matrix (Fin rows) (Fin cols) Bool) :=
  let columns := sampleRows ⟨prg, 0⟩ rows count enough cols
  { value := columns.value.transpose, next := columns.next }

/-- The batching routine samples gamma first, then gamma-prime, and returns
them in that order as in its pseudocode. The number of gamma coordinates is a
caller-supplied size to be instantiated with ceil((n-k)/lambda). -/
def expandBatching {F : Type*} (xof : Nat → Byte) (b gammaCount w count₁ count₂ : Nat)
    (enough₁ : gammaCount * b ≤ count₁) (enough₂ : w * b ≤ count₂)
    (decode : (Fin b → Byte) → F) : Result ((Fin gammaCount → F) × (Fin w → F)) :=
  let gamma := sampleExtension ⟨xof, 0⟩ b gammaCount count₁ enough₁ decode
  let gammaPrime := sampleExtension gamma.next b w count₂ enough₂ decode
  { value := (gamma.value, gammaPrime.value), next := gammaPrime.next }

end SDitH.Spec.ByteSampling
