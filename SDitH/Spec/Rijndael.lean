import SDitH.Spec.RijndaelByte
import Mathlib.Data.Vector.Basic

/-! The two byte-oriented block ciphers selected by SDitH Table 1.
AES-128 is FIPS 197-upd1, Algorithms 1 and 2. Rijndael-256-256 is the
designers' version-2 proposal, §§4.1–4.4: both its key and block have 256 bits.
The latter is not AES-256. Only the two required profiles are introduced.
State byte r+4*c is row r, column c. No security property is imposed here.
-/

namespace SDitH.Spec.Rijndael

open RijndaelByte

inductive Profile where
  | aes128
  | rijndael256
  deriving DecidableEq, Repr

def columns : Profile → Nat
  | .aes128 => 4
  | .rijndael256 => 8

def rounds : Profile → Nat
  | .aes128 => 10
  | .rijndael256 => 14

abbrev State (p : Profile) := Vector Byte (4 * columns p)
abbrev Word := Vector Byte 4

def coordinate {p : Profile} (r : Fin 4) (c : Fin (columns p)) : Fin (4 * columns p) :=
  ⟨r.val + 4 * c.val, by omega⟩

def cell {p : Profile} (s : State p) (r : Fin 4) (c : Fin (columns p)) : Byte :=
  s[coordinate r c]

def ofCells {p : Profile} (s : Fin 4 → Fin (columns p) → Byte) : State p :=
  Vector.ofFn fun i => s ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩ ⟨i.val / 4, by omega⟩

def subBytes {p : Profile} (s : State p) : State p := s.map sbox

/-- Row zero stays fixed; the wide-block offsets are 1,3,4. -/
def shiftOffset (p : Profile) (r : Fin 4) : Nat :=
  match p with
  | .aes128 => r.val
  | .rijndael256 => if r.val = 0 then 0 else if r.val = 1 then 1 else if r.val = 2 then 3 else 4

def shiftRows {p : Profile} (s : State p) : State p := ofCells fun r c =>
  cell s r ⟨(c.val + shiftOffset p r) % columns p,
    Nat.mod_lt _ (by cases p <;> decide)⟩

/-- The circulant coefficient row in FIPS (5.6) and Rijndael §4.2.3. -/
def mixCoefficient (r j : Fin 4) : Byte :=
  if j = r then 0x02#8 else if j = r + 1 then 0x03#8 else 0x01#8

def mixColumn (a : Fin 4 → Byte) (r : Fin 4) : Byte :=
  mul (mixCoefficient r 0) (a 0) ^^^ mul (mixCoefficient r 1) (a 1) ^^^
    mul (mixCoefficient r 2) (a 2) ^^^ mul (mixCoefficient r 3) (a 3)

def mixColumns {p : Profile} (s : State p) : State p :=
  ofCells fun r c => mixColumn (fun j => cell s j c) r

def addRoundKey {p : Profile} (s k : State p) : State p :=
  Vector.ofFn fun i => s[i] ^^^ k[i]

def rotWord (w : Word) : Word := Vector.ofFn fun i => w[i + 1]
def subWord (w : Word) : Word := w.map sbox
def xorWord (v w : Word) : Word := Vector.ofFn fun i => v[i] ^^^ w[i]

/-- Key-expansion calls use j≥1; subtraction totalizes the unused zero case. -/
def rcon (j : Nat) : Word := #v[xtime^[j - 1] (1#8), 0#8, 0#8, 0#8]

def initialWords (p : Profile) (key : State p) : Vector Word (columns p) :=
  Vector.ofFn fun c => Vector.ofFn fun r => key[coordinate r c]

def scheduleTransform (p : Profile) (i : Nat) (previous : Word) : Word :=
  if i % columns p = 0 then xorWord (subWord (rotWord previous)) (rcon (i / columns p))
  else if 6 < columns p ∧ i % columns p = 4 then subWord previous
  else previous

/-- Append one word at a time. With Nb=Nk, the i−Nk read is exactly index n.
All reads are statically in bounds; no missing word is replaced by a default. -/
def expandedThrough (p : Profile) (key : State p) :
    (n : Nat) → Vector Word (columns p + n)
  | 0 => initialWords p key
  | n + 1 =>
    let previous := expandedThrough p key n
    let last : Fin (columns p + n) :=
      ⟨columns p + n - 1, by
        have : 0 < columns p := by cases p <;> decide
        omega⟩
    let old : Fin (columns p + n) :=
      ⟨n, by
        have : 0 < columns p := by cases p <;> decide
        omega⟩
    previous.push (xorWord previous[old]
      (scheduleTransform p (columns p + n) previous[last]))

def expandedKey (p : Profile) (key : State p) :
    Vector Word (columns p * (rounds p + 1)) :=
  (expandedThrough p key (columns p * rounds p)).cast (by cases p <;> decide)

def roundKey (p : Profile) (key : State p) (round : Fin (rounds p + 1)) : State p :=
  let expanded := expandedKey p key
  ofCells fun r c =>
    let i : Fin (columns p * (rounds p + 1)) :=
      ⟨columns p * round.val + c.val, by
        have hr := round.isLt
        have hc := c.isLt
        cases p <;> simp only [columns, rounds] at * <;> omega⟩
    expanded[i][r]

def round {p : Profile} (s key : State p) : State p :=
  addRoundKey (mixColumns (shiftRows (subBytes s))) key

def finalRound {p : Profile} (s key : State p) : State p :=
  addRoundKey (shiftRows (subBytes s)) key

/-- Rounds 1 through n, after the initial key addition. The explicit bound
prevents applying a round key beyond the expanded schedule. -/
def roundsThrough (p : Profile) (key plaintext : State p) :
    (n : Nat) → n < rounds p → State p
  | 0, _ => addRoundKey plaintext (roundKey p key ⟨0, by cases p <;> decide⟩)
  | n + 1, hn => round (roundsThrough p key plaintext n (by omega))
      (roundKey p key ⟨n + 1, by omega⟩)

def encrypt (p : Profile) (key plaintext : State p) : State p :=
  finalRound (roundsThrough p key plaintext (rounds p - 1) (by cases p <;> decide))
    (roundKey p key ⟨rounds p, Nat.lt_succ_self _⟩)

end SDitH.Spec.Rijndael
