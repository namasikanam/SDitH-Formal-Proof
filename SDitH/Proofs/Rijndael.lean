import SDitH.Spec.Rijndael
import SDitH.Proofs.RijndaelByte
import Mathlib.Data.Matrix.Mul

namespace SDitH.Proofs.Rijndael

open Spec.Rijndael Spec.RijndaelByte
open scoped BigOperators Matrix

@[simp] theorem cell_ofCells {p : Profile} (a : Fin 4 → Fin (columns p) → Byte)
    (r : Fin 4) (c : Fin (columns p)) : cell (ofCells a) r c = a r c := by
  simp only [cell, ofCells, Fin.getElem_fin, Vector.getElem_ofFn, coordinate]
  have hr : (⟨(r.val + 4 * c.val) % 4, by omega⟩ : Fin 4) = r := by
    apply Fin.ext
    dsimp
    omega
  have hc : (⟨(r.val + 4 * c.val) / 4, by omega⟩ : Fin (columns p)) = c := by
    apply Fin.ext
    dsimp
    omega
  rw [hr, hc]

theorem cell_injective (p : Profile) : Function.Injective (cell (p := p)) := by
  intro s t h
  apply Vector.ext
  intro i hi
  have hh := congrFun (congrFun h ⟨i % 4, Nat.mod_lt _ (by decide)⟩) ⟨i / 4, by omega⟩
  simpa only [cell, coordinate, Fin.getElem_fin, Nat.mod_add_div] using hh

@[simp] theorem ofCells_cell {p : Profile} (s : State p) : ofCells (cell s) = s := by
  apply cell_injective p
  funext r c
  exact cell_ofCells _ _ _

theorem subBytes_bijective (p : Profile) : Function.Bijective (subBytes (p := p)) := by
  let inverse : State p → State p := fun s => s.map RijndaelByteCertificates.inverseSbox
  have hl : Function.LeftInverse inverse subBytes := by
    intro s
    apply Vector.ext
    intro i hi
    simp only [inverse, subBytes, Vector.getElem_map, RijndaelByteCertificates.inverse_sbox_checked]
  have hr : Function.RightInverse inverse subBytes := by
    intro s
    apply Vector.ext
    intro i hi
    simp only [inverse, subBytes, Vector.getElem_map, RijndaelByteCertificates.sbox_inverse_checked]
  exact ⟨hl.injective, hr.surjective⟩

def inverseShiftRows {p : Profile} (s : State p) : State p := ofCells fun r c =>
  cell s r ⟨(c.val + columns p - shiftOffset p r) % columns p,
    Nat.mod_lt _ (by cases p <;> decide)⟩

theorem inverse_shiftRows {p : Profile} (s : State p) : inverseShiftRows (shiftRows s) = s := by
  apply cell_injective p
  funext r c
  simp only [inverseShiftRows, shiftRows, cell_ofCells]
  apply congrArg (cell s r)
  apply Fin.ext
  change ((c.val + columns p - shiftOffset p r) % columns p + shiftOffset p r) % columns p = c.val
  have h : ∀ (r : Fin 4) (c : Fin (columns p)),
      ((c.val + columns p - shiftOffset p r) % columns p + shiftOffset p r) % columns p = c.val := by
    cases p <;> decide
  exact h r c

theorem shiftRows_inverse {p : Profile} (s : State p) : shiftRows (inverseShiftRows s) = s := by
  apply cell_injective p
  funext r c
  simp only [inverseShiftRows, shiftRows, cell_ofCells]
  apply congrArg (cell s r)
  apply Fin.ext
  change ((c.val + shiftOffset p r) % columns p + columns p - shiftOffset p r) % columns p = c.val
  have h : ∀ (r : Fin 4) (c : Fin (columns p)),
      ((c.val + shiftOffset p r) % columns p + columns p - shiftOffset p r) % columns p = c.val := by
    cases p <;> decide
  exact h r c

theorem shiftRows_bijective (p : Profile) : Function.Bijective (shiftRows (p := p)) :=
  ⟨Function.LeftInverse.injective inverse_shiftRows, Function.RightInverse.surjective shiftRows_inverse⟩

def applyColumn (coeff : Fin 4 → Fin 4 → Byte) (a : Fin 4 → Byte) (r : Fin 4) : Byte :=
  mul (coeff r 0) (a 0) ^^^ mul (coeff r 1) (a 1) ^^^
    mul (coeff r 2) (a 2) ^^^ mul (coeff r 3) (a 3)

noncomputable def decodedMatrix (coeff : Fin 4 → Fin 4 → Byte) : Matrix (Fin 4) (Fin 4) QuotientRing :=
  fun i j => decode (coeff i j)

theorem decode_applyColumn (coeff : Fin 4 → Fin 4 → Byte) (a : Fin 4 → Byte) :
    (fun r => decode (applyColumn coeff a r)) = decodedMatrix coeff *ᵥ (fun j => decode (a j)) := by
  funext r
  simp only [applyColumn, RijndaelByte.decode_xor, RijndaelByte.decode_mul,
    Matrix.mulVec, dotProduct, decodedMatrix, Fin.sum_univ_succ, Fin.sum_univ_zero]
  abel

/-- Inverse MixColumns coefficients, given also by Rijndael §2.2 and FIPS §5.3.3. -/
def inverseMixCoefficient (r j : Fin 4) : Byte :=
  if j = r then 0x0e#8 else if j = r + 1 then 0x0b#8
    else if j = r + 2 then 0x0d#8 else 0x09#8

theorem inverse_mix_coefficients : ∀ r j : Fin 4,
    applyColumn inverseMixCoefficient (fun k => mixCoefficient k j) r =
      if r = j then 1#8 else 0#8 := by decide +kernel

theorem mix_inverse_coefficients : ∀ r j : Fin 4,
    applyColumn mixCoefficient (fun k => inverseMixCoefficient k j) r =
      if r = j then 1#8 else 0#8 := by decide +kernel

theorem decodedMatrix_mul_eq_one (a b : Fin 4 → Fin 4 → Byte)
    (h : ∀ r j, applyColumn a (fun k => b k j) r = if r = j then 1#8 else 0#8) :
    decodedMatrix a * decodedMatrix b = 1 := by
  ext r j
  have he := congrFun (decode_applyColumn a (fun k => b k j)) r
  rw [h] at he
  have ht : decode (if r = j then 1#8 else 0#8) = (1 : Matrix (Fin 4) (Fin 4) QuotientRing) r j := by
    by_cases hr : r = j <;>
      simp [Matrix.one_apply, hr, RijndaelByte.decode_one, RijndaelByte.decode_zero]
  rw [ht] at he
  exact he.symm

theorem applyColumn_leftInverse (a b : Fin 4 → Fin 4 → Byte)
    (h : decodedMatrix a * decodedMatrix b = 1) (v : Fin 4 → Byte) :
    applyColumn a (applyColumn b v) = v := by
  have hv : (fun r => decode (applyColumn a (applyColumn b v) r)) = fun r => decode (v r) := by
    rw [decode_applyColumn, decode_applyColumn, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  funext r
  exact RijndaelByte.decode_bijective.injective (congrFun hv r)

def inverseMixColumns {p : Profile} (s : State p) : State p :=
  ofCells fun r c => applyColumn inverseMixCoefficient (fun j => cell s j c) r

theorem inverse_mixColumns {p : Profile} (s : State p) : inverseMixColumns (mixColumns s) = s := by
  apply cell_injective p
  funext r c
  simp only [inverseMixColumns, mixColumns, cell_ofCells]
  exact congrFun (applyColumn_leftInverse inverseMixCoefficient mixCoefficient
    (decodedMatrix_mul_eq_one _ _ inverse_mix_coefficients) (fun j => cell s j c)) r

theorem mixColumns_inverse {p : Profile} (s : State p) : mixColumns (inverseMixColumns s) = s := by
  apply cell_injective p
  funext r c
  simp only [inverseMixColumns, mixColumns, cell_ofCells]
  exact congrFun (applyColumn_leftInverse mixCoefficient inverseMixCoefficient
    (decodedMatrix_mul_eq_one _ _ mix_inverse_coefficients) (fun j => cell s j c)) r

theorem mixColumns_bijective (p : Profile) : Function.Bijective (mixColumns (p := p)) :=
  ⟨Function.LeftInverse.injective inverse_mixColumns, Function.RightInverse.surjective mixColumns_inverse⟩

theorem addRoundKey_involutive {p : Profile} (k : State p) : Function.Involutive (fun s => addRoundKey s k) := by
  intro s
  apply Vector.ext
  intro i hi
  simp only [addRoundKey, Vector.getElem_ofFn, Fin.getElem_fin,
    BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem round_bijective {p : Profile} (k : State p) : Function.Bijective (fun s => Spec.Rijndael.round s k) :=
  (addRoundKey_involutive k).bijective.comp
    ((mixColumns_bijective p).comp ((shiftRows_bijective p).comp (subBytes_bijective p)))

theorem finalRound_bijective {p : Profile} (k : State p) : Function.Bijective (fun s => finalRound s k) :=
  (addRoundKey_involutive k).bijective.comp ((shiftRows_bijective p).comp (subBytes_bijective p))

theorem roundsThrough_bijective (p : Profile) (key : State p) (n : Nat) (hn : n < rounds p) :
    Function.Bijective (fun plaintext => roundsThrough p key plaintext n hn) := by
  induction n with
  | zero =>
    change Function.Bijective (fun s => addRoundKey s (roundKey p key ⟨0, by cases p <;> decide⟩))
    exact (addRoundKey_involutive (p := p) (roundKey p key ⟨0, by cases p <;> decide⟩)).bijective
  | succ n ih => exact (round_bijective _).comp (ih (by omega))

/-- Each fixed key gives a permutation of the full 128- or 256-bit block.
This deterministic fact does not assert an ideal-cipher security property or
bijectivity of Category III's 192-bit truncation. -/
theorem encrypt_bijective (p : Profile) (key : State p) : Function.Bijective (encrypt p key) :=
  (finalRound_bijective _).comp
    (roundsThrough_bijective p key (rounds p - 1) (by cases p <;> decide))

end SDitH.Proofs.Rijndael
