import SDitH.Spec.Keccak
import Mathlib.Tactic

/-! Bit-for-bit refinement of the concrete lanes to FIPS 202 Algorithms 1–7.
No security property or ideal-permutation model is asserted by these results. -/

namespace SDitH.Proofs.Keccak

open Spec.Keccak

@[simp] theorem lane_ofLanes (a : Fin 5 → Fin 5 → BitVec 64) (x y : Fin 5) :
    lane (ofLanes a) x y = a x y := by
  simp only [lane, ofLanes, Fin.getElem_fin, Vector.getElem_ofFn, coordinate]
  have hx : (⟨(5 * y.val + x.val) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = x := by
    apply Fin.ext
    dsimp
    omega
  have hy : (⟨(5 * y.val + x.val) / 5, by omega⟩ : Fin 5) = y := by
    apply Fin.ext
    dsimp
    omega
  rw [hx, hy]

@[simp] theorem word_bit {n : Nat} (a : Fin n → Bool) (i : Fin n) :
    (word a).getLsbD i.val = a i := by
  simp only [word, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

@[simp] theorem bits_ofBits (a : BitState) : bits (ofBits a) = a := by
  funext x y z
  simp only [bits, ofBits, lane_ofLanes, word_bit]

theorem bits_injective : Function.Injective bits := by
  intro s t h
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hh := congrFun (congrFun (congrFun h
    ⟨i % 5, Nat.mod_lt _ (by decide)⟩) ⟨i / 5, by omega⟩) ⟨j, hj⟩
  simpa [bits, lane, coordinate, Nat.div_add_mod, Nat.mul_comm] using hh

@[simp] theorem ofBits_bits (s : State) : ofBits (bits s) = s := by
  apply bits_injective
  simp

theorem toString_index (s : State) (x y : Fin 5) (z : Fin 64) :
    toString s (stringIndex x y z) = bits s x y z := by
  unfold Spec.Keccak.toString stringIndex
  have hx : (⟨(64 * (5 * y.val + x.val) + z.val) / 64 % 5, by omega⟩ : Fin 5) = x := by
    apply Fin.ext
    dsimp
    omega
  have hy : (⟨(64 * (5 * y.val + x.val) + z.val) / 320, by omega⟩ : Fin 5) = y := by
    apply Fin.ext
    dsimp
    omega
  have hz : (⟨(64 * (5 * y.val + x.val) + z.val) % 64, by omega⟩ : Fin 64) = z := by
    apply Fin.ext
    dsimp
    omega
  rw [hx, hy, hz]

@[simp] theorem toString_fromString (s : Spec.DomainSeparation.Bits 1600) :
    toString (fromString s) = s := by
  funext i
  simp only [Spec.Keccak.toString, fromString, bits_ofBits, stringIndex]
  apply congrArg s
  apply Fin.ext
  dsimp
  omega

@[simp] theorem fromString_toString (s : State) : fromString (toString s) = s := by
  apply bits_injective
  funext x y z
  simp only [fromString, bits_ofBits, toString_index]

theorem toString_injective : Function.Injective toString := by
  intro s t h
  simpa only [fromString_toString] using congrArg fromString h

theorem rotate_bit (w : BitVec 64) (z : Fin 64) (n : Nat) :
    (w.rotateLeft n).getLsbD z.val = w.getLsbD (shiftBack z n).val := by
  rw [BitVec.getLsbD_rotateLeft]
  have hn := Nat.mod_lt n (by decide : 0 < 64)
  have hz := z.isLt
  by_cases h : z.val < n % 64
  · have he : 64 - n % 64 + z.val = (z.val + 64 - n % 64) % 64 := by omega
    simpa only [h, decide_true, cond_true, shiftBack] using congrArg w.getLsbD he
  · have he : z.val - n % 64 = (z.val + 64 - n % 64) % 64 := by omega
    simpa only [h, decide_false, cond_false, hz, decide_true, Bool.true_and, shiftBack]
      using congrArg w.getLsbD he

theorem theta_refines (s : State) : bits (theta s) = Reference.theta (bits s) := by
  funext x y z
  simp only [theta, bits, lane_ofLanes, BitVec.getLsbD_xor, rotate_bit,
    parity, Reference.theta, Reference.parity]

theorem pi_refines (s : State) : bits (pi s) = Reference.pi (bits s) := by
  funext x y z
  simp [bits, pi, Reference.pi]

theorem chi_refines (s : State) : bits (chi s) = Reference.chi (bits s) := by
  funext x y z
  simp [bits, chi, Reference.chi, z.isLt]

/-- Every nonzero lane is assigned once by the 24-step orbit. -/
theorem rho_orbit :
    (∀ t : Fin 24, Reference.rhoPosition t.val ≠ (0, 0)) ∧
    Function.Injective (fun t : Fin 24 => Reference.rhoPosition t.val) ∧
    (∀ x y : Fin 5, (x, y) ≠ (0, 0) →
      ∃ t : Fin 24, Reference.rhoPosition t.val = (x, y)) := by decide

theorem rho_table :
    offset 0 0 = 0 ∧
    ∀ t : Fin 24, offset (Reference.rhoPosition t.val).1
      (Reference.rhoPosition t.val).2 = Reference.rhoOffset t.val := by decide

theorem rho_reference_table (a : BitState) (x y : Fin 5) (z : Fin 64) :
    Reference.rho a x y z = a x y (shiftBack z (offset x y)) := by
  fin_cases x <;> fin_cases y <;>
    simp [Reference.rho, Reference.rhoThrough, Reference.rhoPosition,
      Reference.rhoOffset, offset, rhoOffsets, coordinate, shiftBack, Nat.mod_eq_of_lt z.isLt]

theorem rho_refines (s : State) : bits (rho s) = Reference.rho (bits s) := by
  funext x y z
  rw [rho_reference_table]
  simp only [rho, bits, lane_ofLanes, rotate_bit]

theorem rcStep_refines (r : BitVec 8) (j : Fin 8) :
    (rcStep r).getLsbD j.val = Reference.rcStep (fun i => r.getLsbD i.val) j := by
  fin_cases j <;> cases h : r[7] <;>
    simp [rcStep, Reference.rcStep, h]

theorem rc_iterate_refines (n : Nat) (r : BitVec 8) :
    (fun i : Fin 8 => (rcStep^[n] r).getLsbD i.val) =
      Reference.rcStep^[n] (fun i => r.getLsbD i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    funext i
    rw [rcStep_refines, ih]

theorem rc_refines (t : Nat) : rc t = Reference.rc t := by
  have h := congrFun (rc_iterate_refines (t % 255) 1) 0
  have init : (fun i : Fin 8 => (1 : BitVec 8).getLsbD i.val) =
      (fun j => decide (j.val = 0)) := by
    funext i
    fin_cases i <;> decide
  simpa only [rc, Reference.rc, init] using h

theorem roundConstant_position_lt (j : Fin 7) : 2 ^ j.val - 1 < 64 := by
  fin_cases j <;> decide

theorem roundConstant_at (ir : Nat) (j : Fin 7) :
    Reference.roundConstant ir ⟨2 ^ j.val - 1, roundConstant_position_lt j⟩ =
      Reference.rc (j.val + 7 * ir) := by
  fin_cases j <;> simp [Reference.roundConstant]

theorem roundConstant_else (ir : Nat) (z : Fin 64)
    (h : ∀ j : Fin 7, z.val ≠ 2 ^ j.val - 1) :
    Reference.roundConstant ir z = false := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  have hz0 : z.val ≠ 0 := by
    intro hz
    exact h0 (Fin.ext hz)
  simp only [Reference.roundConstant, hz0, h1, h2, h3, h4, h5, h6, if_false]

theorem roundConstant_refines (ir : Nat) (z : Fin 64) :
    (roundConstant ir).getLsbD z.val = Reference.roundConstant ir z := by
  simp only [roundConstant, word_bit, Reference.roundConstant, rc_refines]

theorem iota_refines (s : State) (ir : Nat) :
    bits (iota s ir) = Reference.iota (bits s) ir := by
  funext x y z
  simp only [iota, bits, lane_ofLanes, Reference.iota]
  split_ifs <;> simp only [BitVec.getLsbD_xor, roundConstant_refines]

theorem round_refines (s : State) (ir : Nat) :
    bits (round s ir) = Reference.round (bits s) ir := by
  simp only [Spec.Keccak.round, Reference.round, iota_refines, chi_refines, pi_refines,
    rho_refines, theta_refines]

theorem rounds_refine (s : State) (n : Nat) :
    bits (rounds s n) = Reference.rounds (bits s) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rounds, Reference.rounds, round_refines, ih]

theorem keccak_refines (s : State) : bits (keccak s) = Reference.keccak (bits s) :=
  rounds_refine s 24

end SDitH.Proofs.Keccak
