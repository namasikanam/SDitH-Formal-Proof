import SDitH.Spec.ByteSampling
import Mathlib.Tactic

namespace SDitH.Proofs.ByteSampling

open Spec.DomainSeparation Spec.ByteSampling

set_option maxRecDepth 4096 in
/-- The exact byte decomposition printed in the sampling rule. Exhaustive
finite reduction is checked by Lean's kernel; no native evaluator is trusted. -/
theorem byte_decomposition : ∀ byte : Byte,
    byte.val = ∑ j : Fin 8, 2 ^ j.val * (byte.val.testBit j.val).toNat := by
  decide

theorem byte_bits_injective (a b : Byte)
    (h : ∀ j : Fin 8, a.val.testBit j.val = b.val.testBit j.val) : a = b := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · exact h ⟨j, hj⟩
  · have hp : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hp),
      Nat.testBit_lt_two_pow (b.isLt.trans_le hp)]

theorem sampleBinary_coordinate (src : Reader) (n count : Nat) (enough : n ≤ 8 * count)
    (j : Fin n) :
    (sampleBinary src n count enough).value j =
      (src.stream (src.position + j.val / 8)).val.testBit (j.val % 8) := rfl

/-- Consuming extra bytes cannot change this call's returned bits. It can change
subsequent calls, because their starting cursor is correspondingly advanced. -/
theorem sampleBinary_value_independent_of_count (src : Reader) (n count₁ count₂ : Nat)
    (h₁ : n ≤ 8 * count₁) (h₂ : n ≤ 8 * count₂) :
    (sampleBinary src n count₁ h₁).value = (sampleBinary src n count₂ h₂).value := rfl

theorem sampleBinary_cursor (src : Reader) (n count : Nat) (enough : n ≤ 8 * count) :
    (sampleBinary src n count enough).next.position = src.position + count := rfl

/-- A whole number of sampled bytes is recoverable from the returned bit
vector. This is a representation theorem, not a distribution assumption. -/
theorem sampleBinary_captures_bytes (src₁ src₂ : Reader) (count : Nat)
    (h : (sampleBinary src₁ (8 * count) count le_rfl).value =
      (sampleBinary src₂ (8 * count) count le_rfl).value) (i : Fin count) :
    src₁.stream (src₁.position + i.val) = src₂.stream (src₂.position + i.val) := by
  apply byte_bits_injective
  intro j
  have hb : 8 * i.val + j.val < 8 * count := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  have he := congrFun h ⟨8 * i.val + j.val, hb⟩
  simp only [sampleBinary_coordinate] at he
  have hd : (8 * i.val + j.val) / 8 = i.val := by have hj := j.isLt; omega
  have hm : (8 * i.val + j.val) % 8 = j.val := by have hj := j.isLt; omega
  simpa only [hd, hm] using he

theorem sampleExtension_coordinate {F : Type*} (src : Reader) (b n count : Nat)
    (enough : n * b ≤ count) (decode : (Fin b → Byte) → F) (i : Fin n) :
    (sampleExtension src b n count enough decode).value i =
      decode (fun j => src.stream (src.position + (i.val * b + j.val))) := rfl

theorem sampleExtension_value_independent_of_count {F : Type*} (src : Reader)
    (b n count₁ count₂ : Nat) (h₁ : n * b ≤ count₁) (h₂ : n * b ≤ count₂)
    (decode : (Fin b → Byte) → F) :
    (sampleExtension src b n count₁ h₁ decode).value =
      (sampleExtension src b n count₂ h₂ decode).value := rfl

/-- At byte-aligned lengths, sequential binary calls select the same bytes as
one combined call. This does not assert a buffering convention for other lengths. -/
theorem sampleBinary_aligned_second (src : Reader) (firstBytes secondBytes : Nat)
    (j : Fin (8 * secondBytes)) :
    (sampleBinary (sampleBinary src (8 * firstBytes) firstBytes le_rfl).next
      (8 * secondBytes) secondBytes le_rfl).value j =
    (sampleBinary src (8 * (firstBytes + secondBytes)) (firstBytes + secondBytes) le_rfl).value
      ⟨8 * firstBytes + j.val, by have hj := j.isLt; omega⟩ := by
  change (src.stream (src.position + firstBytes + j.val / 8)).val.testBit (j.val % 8) =
    (src.stream (src.position + (8 * firstBytes + j.val) / 8)).val.testBit
      ((8 * firstBytes + j.val) % 8)
  have hd : (8 * firstBytes + j.val) / 8 = firstBytes + j.val / 8 := by omega
  have hm : (8 * firstBytes + j.val) % 8 = j.val % 8 := by omega
  rw [hd, hm, Nat.add_assoc]

theorem sampleRows_next (src : Reader) (cols count : Nat) (enough : cols ≤ 8 * count)
    (rows : Nat) :
    (sampleRows src cols count enough rows).next = advance src (rows * count) := by
  induction rows generalizing src with
  | zero => cases src; simp [sampleRows, advance]
  | succ rows ih =>
    simp only [sampleRows, ih, sampleBinary, advance, Nat.add_mul, Nat.one_mul]
    congr 1
    omega

/-- The loop's flat stream layout, proved from its recursive execution. -/
theorem sampleRows_coordinate (src : Reader) (cols count : Nat) (enough : cols ≤ 8 * count)
    (rows : Nat) (i : Fin rows) (j : Fin cols) :
    (sampleRows src cols count enough rows).value i j =
      (src.stream (src.position + i.val * count + j.val / 8)).val.testBit (j.val % 8) := by
  induction rows generalizing src with
  | zero => exact Fin.elim0 i
  | succ rows ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [sampleRows, sampleBinary_coordinate]
    · simp only [sampleRows, Fin.cons_succ, ih, sampleBinary, advance, Fin.val_succ]
      have he : src.position + count + k.val * count + j.val / 8 =
          src.position + (k.val + 1) * count + j.val / 8 := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [he]

theorem expandConsistency_coordinate (xof : Nat → Byte) (lambda B ell count : Nat)
    (enough : ell ≤ 8 * count) (i : Fin (lambda + B)) (j : Fin ell) :
    (expandConsistency xof lambda B ell count enough).value i j =
      (xof (i.val * count + j.val / 8)).val.testBit (j.val % 8) := by
  simpa [expandConsistency] using
    sampleRows_coordinate ⟨xof, 0⟩ ell count enough (lambda + B) i j

theorem expandHColumns_coordinate (prg : Nat → Byte) (rows cols count : Nat)
    (enough : rows ≤ 8 * count) (i : Fin rows) (j : Fin cols) :
    (expandHColumns prg rows cols count enough).value i j =
      (prg (j.val * count + i.val / 8)).val.testBit (i.val % 8) := by
  simpa [expandHColumns, Matrix.transpose_apply] using
    sampleRows_coordinate ⟨prg, 0⟩ rows count enough cols j i

theorem expandBatching_layout {F : Type*} (xof : Nat → Byte)
    (b gammaCount w count₁ count₂ : Nat)
    (enough₁ : gammaCount * b ≤ count₁) (enough₂ : w * b ≤ count₂)
    (decode : (Fin b → Byte) → F) :
    (expandBatching xof b gammaCount w count₁ count₂ enough₁ enough₂ decode).value =
      ((fun i => decode (fun j => xof (i.val * b + j.val))),
       (fun i => decode (fun j => xof (count₁ + (i.val * b + j.val))))) ∧
    (expandBatching xof b gammaCount w count₁ count₂ enough₁ enough₂ decode).next.position =
      count₁ + count₂ := by
  simp [expandBatching, sampleExtension, readBytes, advance]

end SDitH.Proofs.ByteSampling
