import SDitH.Proofs.FieldByteProbability

/-! The binary branch of SampleFieldElements has the uniform law under an
explicit uniform-byte sample, including partial final bytes and extra consumed
bytes. Its little-endian bit order is stated in the PDF, unlike the extension
field's byte-to-coefficient ordering. -/

namespace SDitH.Proofs.BinarySamplingProbability

open Spec.DomainSeparation Spec.ByteSampling Spec.FieldBytes
open IntegerSamplingProbability
open scoped Classical

private theorem byte_bits_bijective :
    Function.Bijective (fun byte : Byte => fun j : Fin 8 => byte.val.testBit j.val) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    exact ByteSampling.byte_bits_injective a b (fun j => congrFun h j)
  · norm_num [Fintype.card_fun, Byte]

noncomputable def byteBitsEquiv : Byte ≃ (Fin 8 → Bool) :=
  Equiv.ofBijective _ byte_bits_bijective

private def bitPosition (count : Nat) : Fin (8 * count) ≃ Fin count × Fin 8 :=
  (finCongr (Nat.mul_comm 8 count)).trans finProdFinEquiv.symm

noncomputable def allBitsEquiv (count : Nat) : (Fin count → Byte) ≃ Bits (8 * count) where
  toFun bytes i := byteBitsEquiv (bytes (bitPosition count i).1) (bitPosition count i).2
  invFun bits j := byteBitsEquiv.symm (fun k => bits ((bitPosition count).symm (j, k)))
  left_inv bytes := by
    funext j
    apply byteBitsEquiv.injective
    rw [Equiv.apply_symm_apply]
    funext k
    simp
  right_inv bits := by
    funext i
    change byteBitsEquiv (byteBitsEquiv.symm
      (fun k => bits ((bitPosition count).symm ((bitPosition count i).1, k))))
      (bitPosition count i).2 = bits i
    simp

theorem allBitsEquiv_coordinate (count : Nat) (bytes : Fin count → Byte)
    (i : Fin (8 * count)) :
    allBitsEquiv count bytes i =
      (bytes ⟨i.val / 8, by have hi := i.isLt; omega⟩).val.testBit (i.val % 8) := rfl

private theorem sampleBinary_finiteReader (n count : Nat) (enough : n ≤ 8 * count)
    (bytes : Fin count → Byte) :
    (sampleBinary (finiteReader bytes) n count enough).value =
      fun j => allBitsEquiv count bytes (Fin.castLE enough j) := by
  funext j
  rw [ByteSampling.sampleBinary_coordinate, allBitsEquiv_coordinate]
  have hj : j.val / 8 < count := by have hi := j.isLt; omega
  simp [finiteReader, hj]

/-- The full requested bit vector is uniform, including when its length is
not a multiple of eight. Discarding the unused bits does not bias this call. -/
theorem sampleBinary_uniform (n count : Nat) (enough : n ≤ 8 * count) :
    (PMF.uniformOfFintype (Fin count → Byte)).map
      (fun bytes => (sampleBinary (finiteReader bytes) n count enough).value) =
      PMF.uniformOfFintype (Bits n) := by
  simp_rw [sampleBinary_finiteReader]
  change (PMF.uniformOfFintype (Fin count → Byte)).map
    ((fun v j => v (Fin.castLE enough j)) ∘ allBitsEquiv count) = _
  rw [← PMF.map_comp, map_uniform_equiv (allBitsEquiv count)]
  exact UniformVectors.map_uniform_restrict (Fin.castLE enough) (Fin.castLE_injective enough)

private noncomputable def bitFieldEquiv : Bool ≃ ZMod 2 :=
  Equiv.ofBijective bitCoefficient
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨FieldBytes.bitCoefficient_injective, by simp [ZMod.card]⟩)

/-- Reading those Boolean bits as elements of F2 gives the same joint uniform
law on the binary field vector used by the arithmetic algorithms. -/
theorem sampleBinary_field_uniform (n count : Nat) (enough : n ≤ 8 * count) :
    (PMF.uniformOfFintype (Fin count → Byte)).map
      (fun bytes j => bitCoefficient ((sampleBinary (finiteReader bytes) n count enough).value j)) =
      PMF.uniformOfFintype (Fin n → ZMod 2) := by
  let e : Bits n ≃ (Fin n → ZMod 2) := Equiv.piCongrRight (fun _ => bitFieldEquiv)
  change (PMF.uniformOfFintype (Fin count → Byte)).map
    (e ∘ (fun bytes => (sampleBinary (finiteReader bytes) n count enough).value)) = _
  rw [← PMF.map_comp, sampleBinary_uniform]
  exact map_uniform_equiv e

end SDitH.Proofs.BinarySamplingProbability
