import SDitH.Spec.SHAKE
import SDitH.Proofs.Keccak

/-! Padding, absorption, squeezing, and concrete byte-reader correspondence.
These are deterministic functional properties; no uniformity law is asserted. -/

namespace SDitH.Proofs.SHAKE

open Spec.SHAKE

theorem padZeros_lt (r : Rate) (m : Nat) : padZeros r m < r.value :=
  Nat.mod_lt _ r.positive

theorem padZeros_integer (r : Rate) (m : Nat) :
    (padZeros r m : Int) = (-(m : Int) - 2) % r.value := by
  unfold padZeros
  rw [Int.natCast_mod, Int.natCast_sub (Nat.le_of_lt (Nat.mod_lt _ r.positive)),
    Int.natCast_mod, Int.sub_emod_emod, Int.sub_emod_left]
  congr 1
  push_cast
  ring

@[simp] theorem padding_length (r : Rate) (m : Nat) :
    (padding r m).length = padZeros r m + 2 := by simp [padding]

theorem padded_length (r : Rate) (input : List Bool) :
    (padded r input).length = input.length + padZeros r input.length + 2 := by
  simp [padded, Nat.add_assoc]

theorem padded_positive (r : Rate) (input : List Bool) : 0 < (padded r input).length := by
  rw [padded_length]
  omega

theorem padded_divisible (r : Rate) (input : List Bool) :
    r.value ∣ (padded r input).length := by
  rw [Nat.dvd_iff_mod_eq_zero, padded_length]
  unfold padZeros
  have h := Nat.mod_lt (input.length + 2) r.positive
  have he : input.length + (r.value - (input.length + 2) % r.value) % r.value + 2 =
      (input.length + 2) + (r.value - (input.length + 2) % r.value) % r.value := by omega
  rw [he, Nat.add_mod_mod, ← Nat.mod_add_mod (input.length + 2)]
  rw [Nat.add_sub_of_le (Nat.le_of_lt h), Nat.mod_self]

theorem block_index_lt (r : Rate) (input : List Bool)
    (i : Fin (input.length / r.value)) (j : Fin r.value) :
    r.value * i.val + j.val < input.length := by
  have hi : (i.val + 1) * r.value ≤ input.length :=
    (Nat.le_div_iff_mul_le r.positive).mp i.isLt
  have hj := j.isLt
  nlinarith

theorem block_in_bounds (r : Rate) (input : List Bool)
    (i : Fin (input.length / r.value)) (j : Fin r.value) :
    block r input i.val j = input[r.value * i.val + j.val]'(block_index_lt r input i j) := by
  simp [block, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (block_index_lt r input i j)]

theorem ofFn_getD {α : Type*} (input : List α) (fallback : α) (n : Nat)
    (h : n = input.length) :
    List.ofFn (fun i : Fin n => input.getD i.val fallback) = input := by
  subst n
  calc
    _ = List.ofFn (fun i : Fin input.length => input[i.val]) := by
      apply congrArg List.ofFn
      funext i
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some]
    _ = input := List.ofFn_getElem input

/-- The rate blocks consume the whole padded string, with no discarded tail. -/
theorem blocks_reassemble (r : Rate) (input : List Bool) (h : r.value ∣ input.length) :
    (List.ofFn fun i : Fin (input.length / r.value) => List.ofFn (block r input i.val)).flatten =
      input := by
  have he := ofFn_getD input false ((input.length / r.value) * r.value) (Nat.div_mul_cancel h)
  rw [List.ofFn_mul] at he
  simpa only [block, Nat.mul_comm] using he

theorem padded_blocks_reassemble (r : Rate) (input : List Bool) :
    (List.ofFn fun i : Fin ((padded r input).length / r.value) =>
      List.ofFn (block r (padded r input) i.val)).flatten = padded r input :=
  blocks_reassemble r (padded r input) (padded_divisible r input)

theorem inject_bits (r : Rate) (s : Spec.Keccak.State) (p : Spec.DomainSeparation.Bits r.value)
    (x y : Fin 5) (z : Fin 64) :
    Spec.Keccak.bits (inject r s p) x y z = (Spec.Keccak.bits s x y z ^^
      if h : (Spec.Keccak.stringIndex x y z).val < r.value then
        p ⟨(Spec.Keccak.stringIndex x y z).val, h⟩ else false) := by
  simp only [inject, Keccak.bits_ofBits]

theorem inject_capacity (r : Rate) (s : Spec.Keccak.State)
    (p : Spec.DomainSeparation.Bits r.value) (x y : Fin 5) (z : Fin 64)
    (h : r.value ≤ (Spec.Keccak.stringIndex x y z).val) :
    Spec.Keccak.bits (inject r s p) x y z = Spec.Keccak.bits s x y z := by
  simp [inject_bits, Nat.not_lt.mpr h]

theorem absorbThrough_fold (r : Rate) (input : List Bool) (n : Nat) :
    absorbThrough r input n = (List.range n).foldl
      (fun s i => Spec.Keccak.keccak (inject r s (block r input i))) Spec.Keccak.zero := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [absorbThrough, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih]

theorem squeeze_first (r : Rate) (s : Spec.Keccak.State) (j : Fin r.value) :
    squeezeBit r s j.val = Spec.Keccak.toString s ⟨j.val, lt_of_lt_of_le j.isLt r.le_width⟩ := by
  simp [squeezeBit, Nat.div_eq_of_lt j.isLt, Nat.mod_eq_of_lt j.isLt]

theorem squeeze_next (r : Rate) (s : Spec.Keccak.State) (i : Nat) :
    squeezeBit r s (r.value + i) = squeezeBit r (Spec.Keccak.keccak s) i := by
  have hd : (r.value + i) / r.value = i / r.value + 1 := by
    rw [Nat.add_div_left _ r.positive]
  have hm : (r.value + i) % r.value = i % r.value := by simp
  simp only [squeezeBit, hd, hm, Function.iterate_succ_apply]

theorem squeezeBlocks_length (r : Rate) (s : Spec.Keccak.State) (n : Nat) :
    (squeezeBlocks r s n).length = r.value * n := by
  induction n generalizing s with
  | zero => simp [squeezeBlocks]
  | succ n ih => simp [squeezeBlocks, ih, Nat.mul_succ, Nat.add_comm]

theorem squeezeBlocks_ofFn (r : Rate) (s : Spec.Keccak.State) (n : Nat) :
    squeezeBlocks r s n = List.ofFn (fun i : Fin (r.value * n) => squeezeBit r s i.val) := by
  induction n generalizing s with
  | zero => simp [squeezeBlocks]
  | succ n ih =>
    simp only [squeezeBlocks, ih, Nat.mul_succ, Nat.add_comm (r.value * n) r.value,
      List.ofFn_add]
    apply congrArg₂ List.append
    · apply congrArg List.ofFn
      funext i
      exact (squeeze_first r s i).symm
    · apply congrArg List.ofFn
      funext i
      exact (squeeze_next r s i.val).symm

/-- Every requested output prefix agrees with the finite append/permutation
loop as soon as that loop has accumulated enough bits. -/
theorem squeezeBlocks_prefix (r : Rate) (s : Spec.Keccak.State) (n d : Nat)
    (h : d ≤ r.value * n) :
    (squeezeBlocks r s n).take d = List.ofFn (fun i : Fin d => squeezeBit r s i.val) := by
  rw [squeezeBlocks_ofFn]
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i hleft hright
    simp only [List.getElem_take, List.getElem_ofFn]

theorem sponge_prefix (r : Rate) (input : List Bool) {d e : Nat} (h : d ≤ e)
    (i : Fin d) : sponge r input e (Fin.castLE h i) = sponge r input d i := rfl

theorem shake128_prefix (message : List Bool) {d e : Nat} (h : d ≤ e) (i : Fin d) :
    shake128 message e (Fin.castLE h i) = shake128 message d i := rfl
theorem shake256_prefix (message : List Bool) {d e : Nat} (h : d ≤ e) (i : Fin d) :
    shake256 message e (Fin.castLE h i) = shake256 message d i := rfl

theorem hash_i (message : List Bool) : hash .i message = shake128 message 256 := rfl
theorem hash_iii (message : List Bool) : hash .iii message = shake256 message 384 := rfl
theorem hash_v (message : List Bool) : hash .v message = shake256 message 512 := rfl

theorem byteStream_bit (category : Spec.FieldRepresentation.Category) (message : List Bool)
    (i : Nat) (j : Fin 8) :
    (byteStream category message i).val.testBit j.val = bitStream category message (8 * i + j.val) := by
  change (Spec.Keccak.word (fun j : Fin 8 => bitStream category message (8 * i + j.val))).getLsbD
    j.val = _
  exact Keccak.word_bit _ j

/-- The existing binary sampler reads precisely the requested SHAKE bits.
The explicit consumed byte count can exceed the requested bit length. -/
theorem sampleBinary_reader (category : Spec.FieldRepresentation.Category) (message : List Bool)
    (position n count : Nat) (enough : n ≤ 8 * count) (j : Fin n) :
    (Spec.ByteSampling.sampleBinary
      (Spec.ByteSampling.advance (reader category message) position) n count enough).value j =
      bitStream category message (8 * position + j.val) := by
  simp only [Spec.ByteSampling.sampleBinary, Spec.ByteSampling.readBytes,
    Spec.ByteSampling.advance, reader, Nat.zero_add]
  rw [byteStream_bit category message _ ⟨j.val % 8, Nat.mod_lt _ (by decide)⟩]
  congr 1
  dsimp
  omega

end SDitH.Proofs.SHAKE
