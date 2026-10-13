import SDitH.Spec.DomainSeparation
import Mathlib.Data.BitVec
import Mathlib.Logic.Function.Iterate

/-! FIPS 202 (August 2015), §§3.1–3.3, specialized to b=1600, w=64,
and 24 rounds, as required by both SHAKE functions in SDitH Table 1.
The standard's bit equations and a materialized lane implementation are both
explicit. This file imposes no permutation or cryptographic security property.
The external reference PDF is pinned in `source/standards/index.json`.
-/

namespace SDitH.Spec.Keccak

abbrev BitState := Fin 5 → Fin 5 → Fin 64 → Bool
abbrev State := Vector (BitVec 64) 25

def coordinate (x y : Fin 5) : Fin 25 := ⟨5 * y.val + x.val, by omega⟩
def lane (s : State) (x y : Fin 5) : BitVec 64 := s[coordinate x y]
def ofLanes (a : Fin 5 → Fin 5 → BitVec 64) : State :=
  Vector.ofFn fun i => a ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
    ⟨i.val / 5, by omega⟩
def bits (s : State) : BitState := fun x y z => (lane s x y).getLsbD z.val
def word {n : Nat} (a : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn a)).cast (List.length_ofFn)
def ofBits (a : BitState) : State := ofLanes fun x y => word (a x y)
def zero : State := Vector.replicate 25 0

/-- The FIPS string index is 64*(5*y+x)+z. -/
def stringIndex (x y : Fin 5) (z : Fin 64) : Fin 1600 :=
  ⟨64 * (5 * y.val + x.val) + z.val, by omega⟩
def fromString (s : DomainSeparation.Bits 1600) : State :=
  ofBits fun x y z => s (stringIndex x y z)
def toString (s : State) : DomainSeparation.Bits 1600 := fun i =>
  bits s ⟨i.val / 64 % 5, Nat.mod_lt _ (by decide)⟩
    ⟨i.val / 320, by omega⟩ ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

def shiftBack (z : Fin 64) (offset : Nat) : Fin 64 :=
  ⟨(z.val + 64 - offset % 64) % 64, Nat.mod_lt _ (by decide)⟩

namespace Reference

def parity (a : BitState) (x : Fin 5) (z : Fin 64) : Bool :=
  a x 0 z ^^ a x 1 z ^^ a x 2 z ^^ a x 3 z ^^ a x 4 z
def theta (a : BitState) : BitState := fun x y z =>
  a x y z ^^ (parity a (x - 1) z ^^ parity a (x + 1) (shiftBack z 1))

/-- The 24-lane orbit in Algorithm 2, before updating the coordinates. -/
def rhoPosition : Nat → Fin 5 × Fin 5
  | 0 => (1, 0)
  | t + 1 => let p := rhoPosition t; (p.2, 2 * p.1 + 3 * p.2)
def rhoOffset (t : Nat) : Nat := (t + 1) * (t + 2) / 2

/-- A direct functional transcription of the sequential assignments. The
initial value is immaterial off (0,0), since the orbit covers the other lanes. -/
def rhoThrough (a : BitState) : Nat → BitState
  | 0 => a
  | t + 1 => fun x y z =>
    if (x, y) = rhoPosition t then a x y (shiftBack z (rhoOffset t))
    else rhoThrough a t x y z
def rho (a : BitState) : BitState := rhoThrough a 24
def pi (a : BitState) : BitState := fun x y z => a (x + 3 * y) x z
def chi (a : BitState) : BitState := fun x y z =>
  a x y z ^^ ((!a (x + 1) y z) && a (x + 2) y z)

/-- Algorithm 5's prepend-zero, four feedback assignments, and truncation.
Index 0 is the first bit of the printed string, hence the low bit here. -/
def rcStep (r : Fin 8 → Bool) : Fin 8 → Bool := fun j =>
  (if h : j.val = 0 then false else r ⟨j.val - 1, by omega⟩) ^^
    (if j.val = 0 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6 then r 7 else false)
def rc (t : Nat) : Bool :=
  (rcStep^[t % 255] (fun j => decide (j.val = 0))) 0
def roundConstant (ir : Nat) (z : Fin 64) : Bool :=
  if z.val = 0 then rc (7 * ir)
  else if z.val = 1 then rc (1 + 7 * ir)
  else if z.val = 3 then rc (2 + 7 * ir)
  else if z.val = 7 then rc (3 + 7 * ir)
  else if z.val = 15 then rc (4 + 7 * ir)
  else if z.val = 31 then rc (5 + 7 * ir)
  else if z.val = 63 then rc (6 + 7 * ir)
  else false
def iota (a : BitState) (ir : Nat) : BitState := fun x y z =>
  if x = 0 ∧ y = 0 then a x y z ^^ roundConstant ir z else a x y z
def round (a : BitState) (ir : Nat) : BitState := iota (chi (pi (rho (theta a)))) ir
def rounds (a : BitState) : Nat → BitState
  | 0 => a
  | n + 1 => round (rounds a n) n
def keccak (a : BitState) : BitState := rounds a 24

end Reference

/-- FIPS Table 2 in row order y=0..4, with x=0..4 within each row. -/
def rhoOffsets : Vector Nat 25 :=
  #v[0, 1, 190, 28, 91, 36, 300, 6, 55, 276, 3, 10, 171, 153, 231,
     105, 45, 15, 21, 136, 210, 66, 253, 120, 78]
def offset (x y : Fin 5) : Nat := rhoOffsets[coordinate x y]
def parity (s : State) (x : Fin 5) : BitVec 64 :=
  lane s x 0 ^^^ lane s x 1 ^^^ lane s x 2 ^^^ lane s x 3 ^^^ lane s x 4
def theta (s : State) : State := ofLanes fun x y =>
  lane s x y ^^^ (parity s (x - 1) ^^^ (parity s (x + 1)).rotateLeft 1)
def rho (s : State) : State :=
  ofLanes fun x y => (lane s x y).rotateLeft (offset x y)
def pi (s : State) : State := ofLanes fun x y => lane s (x + 3 * y) x
def chi (s : State) : State := ofLanes fun x y =>
  lane s x y ^^^ ((~~~lane s (x + 1) y) &&& lane s (x + 2) y)

def rcStep (r : BitVec 8) : BitVec 8 :=
  (r <<< 1) ^^^ (if r.getLsbD 7 then 0x71 else 0)
def rc (t : Nat) : Bool := ((rcStep^[t % 255]) 1).getLsbD 0
def roundConstant (ir : Nat) : BitVec 64 := word fun z =>
  if z.val = 0 then rc (7 * ir)
  else if z.val = 1 then rc (1 + 7 * ir)
  else if z.val = 3 then rc (2 + 7 * ir)
  else if z.val = 7 then rc (3 + 7 * ir)
  else if z.val = 15 then rc (4 + 7 * ir)
  else if z.val = 31 then rc (5 + 7 * ir)
  else if z.val = 63 then rc (6 + 7 * ir)
  else false
def iota (s : State) (ir : Nat) : State := ofLanes fun x y =>
  if x = 0 ∧ y = 0 then lane s x y ^^^ roundConstant ir else lane s x y
def round (s : State) (ir : Nat) : State := iota (chi (pi (rho (theta s)))) ir
def rounds (s : State) : Nat → State
  | 0 => s
  | n + 1 => round (rounds s n) n
def keccak (s : State) : State := rounds s 24

end SDitH.Spec.Keccak
