import SDitH.Spec.CipherPrimitives
import SDitH.Spec.ByteSampling
import SDitH.Spec.Parameters
import Mathlib.Data.List.OfFn

/-! Algorithm 6, printed p. 17, with its source gaps kept visible.
The undefined nblock-bitsize is an explicit positive parameter, not silently
identified with lambda or the ciphertext width. Parse below means a complete
partition into bytes, with the number of bytes printed on line 5.

`run` is a partial transcription: none means a printed input/assignment could
not be given this exact meaning. It is NOT an error return specified by SDitH.
No salt defaults to zero as stated; a present salt without a tweak is unresolved.
The unconditional ciphertext stream is also exposed, independently of whether
the printed finite Parse assignment is well-formed for a category.
-/

namespace SDitH.Spec.PRG

open DomainSeparation FieldRepresentation

/-- A value supplied for the source's undefined denominator. This carries no
claim that the submission specifies this value. -/
structure BlockSize where
  bits : Nat
  positive : 0 < bits

def blockCount (size : BlockSize) (nbytes : Nat) : Nat :=
  (8 * nbytes + size.bits - 1) / size.bits

def shiftedTweak (tweak : Byte) : Tweak :=
  ⟨2 ^ 16 * tweak.val, by have h := tweak.isLt; change 65536 * tweak.val < 16777216; omega⟩

def prepareSalt (category : Category) (variant : Grinding)
    (salt : Option (Bits (width category))) (tweak : Option Byte) : Option (Bits (width category)) :=
  match salt, tweak with
  | none, _ => some (fun _ => false)
  | some s, some t => some (tweakSalt variant s (shiftedTweak t) false)
  | some _, none => none

/-- Fixed-width little-endian digits. Integers beyond the width have the
same low bits; counter uniqueness theorems explicitly require no wraparound. -/
def littleEndian (lambda counter : Nat) : Bits lambda :=
  fun j => counter.testBit j.val

def plaintext (category : Category) (salt : Bits (width category)) (counter : Nat) : Bits (width category) :=
  fun j => salt j ^^ littleEndian (width category) counter j

def block (category : Category) (seed salt : Bits (width category)) (counter : Nat) :
    Bits (CipherPrimitives.ciphertextWidth category) :=
  CipherPrimitives.enc category seed (plaintext category salt counter)

def ciphertextBytes (category : Category) : Nat := CipherPrimitives.ciphertextWidth category / 8

def byteInBlock (category : Category) (value : Bits (CipherPrimitives.ciphertextWidth category))
    (j : Fin (ciphertextBytes category)) : Byte :=
  (Keccak.word fun k : Fin 8 => value ⟨8 * j.val + k.val, by
    have hj := j.isLt
    have hk := k.isLt
    cases category <;> simp only [ciphertextBytes, CipherPrimitives.ciphertextWidth] at * <;> omega⟩).toFin

/-- Line 3's increasing counter loop and line 4's actual Table-1 Enc calls. -/
def blockArray (category : Category) (seed salt : Bits (width category)) (count : Nat) :
    Vector (Bits (CipherPrimitives.ciphertextWidth category)) count :=
  Vector.ofFn fun i => block category seed salt i.val

def byteArray (category : Category) (seed salt : Bits (width category)) (count : Nat) :
    Vector Byte (count * ciphertextBytes category) :=
  let blocks := blockArray category seed salt count
  Vector.ofFn fun j =>
    let i : Fin count := ⟨j.val / ciphertextBytes category,
      (Nat.div_lt_iff_lt_mul (by cases category <;> decide)).mpr j.isLt⟩
    byteInBlock category blocks[i]
      ⟨j.val % ciphertextBytes category, Nat.mod_lt _ (by cases category <;> decide)⟩

def declaredBytes (category : Category) (count : Nat) : Nat :=
  prgDeclaredParseBytes (width category) count

/-- Exact byte count on line 5. This is independently checkable and, for
positive counts in Category III, false. It is never assumed globally. -/
def ParseShape (category : Category) (count : Nat) : Prop :=
  count * ciphertextBytes category = declaredBytes category count

instance (category : Category) (count : Nat) : Decidable (ParseShape category count) :=
  inferInstanceAs (Decidable (_ = _))

/-- The finite output is defined only when both printed array assignments fit.
This guard records a source-elaboration obligation, not a submitted rejection. -/
def parseAndTake (category : Category) (count nbytes : Nat)
    (bytes : Vector Byte (count * ciphertextBytes category)) : Option (Vector Byte nbytes) :=
  if hs : ParseShape category count then
    if he : nbytes ≤ declaredBytes category count then
      some (Vector.ofFn fun i => bytes[i.val]'(by
        have hi := i.isLt
        unfold ParseShape at hs
        omega))
    else none
  else none

def run (category : Category) (variant : Grinding) (size : BlockSize)
    (seed : Bits (width category)) (salt : Option (Bits (width category)))
    (tweak : Option Byte) (nbytes : Nat) : Option (Vector Byte nbytes) := do
  let salt' ← prepareSalt category variant salt tweak
  let count := blockCount size nbytes
  parseAndTake category count nbytes (byteArray category seed salt' count)

/-- The infinite concatenation of actual ciphertext bytes. Relating a prefix
to Algorithm 6 requires a successful `run`; this is not a repair of its Parse. -/
def stream (category : Category) (seed salt : Bits (width category)) : Nat → Byte := fun i =>
  byteInBlock category (block category seed salt (i / ciphertextBytes category))
    ⟨i % ciphertextBytes category, Nat.mod_lt _ (by cases category <;> decide)⟩

def reader (category : Category) (seed salt : Bits (width category)) : ByteSampling.Reader :=
  ⟨stream category seed salt, 0⟩

/-- A direct append-loop presentation of the same bytes, for correspondence
with the concatenation on the right of the source's Parse assignment. -/
def byteLoop (category : Category) (seed salt : Bits (width category)) : Nat → List Byte
  | 0 => []
  | count + 1 => byteLoop category seed salt count ++
      List.ofFn (byteInBlock category (block category seed salt count))

end SDitH.Spec.PRG
