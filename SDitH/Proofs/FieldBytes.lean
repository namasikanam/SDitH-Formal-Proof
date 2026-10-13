import SDitH.Spec.FieldBytes
import SDitH.Proofs.FieldIsomorphism
import SDitH.Proofs.ByteSampling

namespace SDitH.Proofs.FieldBytes

open Spec.DomainSeparation Spec.FieldRepresentation Spec.FieldBytes
open scoped Classical BigOperators

theorem byte_width (category : Category) : byteCount category * 8 = width category := by
  cases category <;> decide

/-- One explicitly named ordering, useful for comparison. The source does not
choose this ordering for extension elements, so it is never installed as a default. -/
def littleEndianOrder (category : Category) : ByteOrder category :=
  (finCongr (byte_width category).symm).trans finProdFinEquiv.symm

theorem littleEndianOrder_byte (category : Category) (i : Fin (width category)) :
    ((littleEndianOrder category) i).1.val = i.val / 8 := rfl

theorem littleEndianOrder_bit (category : Category) (i : Fin (width category)) :
    ((littleEndianOrder category) i).2.val = i.val % 8 := rfl

theorem bitCoefficient_injective : Function.Injective bitCoefficient := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitCoefficient]

theorem byteCoefficients_bijective : Function.Bijective byteCoefficients := by
  apply (Fintype.bijective_iff_injective_and_card byteCoefficients).mpr
  constructor
  · intro a b hab
    apply ByteSampling.byte_bits_injective
    intro j
    exact bitCoefficient_injective (congrFun hab j)
  · norm_num [Fintype.card_fun, ZMod.card, Byte]

noncomputable def byteEquiv : Byte ≃ (Fin 8 → ZMod 2) :=
  Equiv.ofBijective byteCoefficients byteCoefficients_bijective

noncomputable def coefficientPackEquiv (category : Category) (order : ByteOrder category) :
    (Fin (byteCount category) → Byte) ≃ (Fin (width category) → ZMod 2) where
  toFun := coefficients category order
  invFun v := fun j => byteEquiv.symm (fun k => v (order.symm (j, k)))
  left_inv bytes := by
    funext j
    apply byteEquiv.injective
    simp only [Equiv.apply_symm_apply]
    funext k
    simp [coefficients, byteEquiv]
  right_inv v := by
    funext i
    change byteEquiv (byteEquiv.symm (fun k => v (order.symm ((order i).1, k))))
      (order i).2 = v i
    simp

/-- Every byte pack maps to one field element and every field element has
exactly one byte pack for the explicitly supplied ordering. -/
noncomputable def packEquiv (category : Category) (order : ByteOrder category) :
    (Fin (byteCount category) → Byte) ≃ QuotientRing category :=
  (coefficientPackEquiv category order).trans (FieldIsomorphism.coefficientEquiv category).toEquiv

theorem packEquiv_apply (category : Category) (order : ByteOrder category)
    (bytes : Fin (byteCount category) → Byte) :
    packEquiv category order bytes = decode category order bytes :=
  FieldIsomorphism.coefficientEquiv_apply category _

theorem decode_bijective (category : Category) (order : ByteOrder category) :
    Function.Bijective (decode category order) := by
  have he : decode category order = packEquiv category order := by
    funext bytes
    exact (packEquiv_apply category order bytes).symm
  rw [he]
  exact (packEquiv category order).bijective

theorem decode_recover (category : Category) (order : ByteOrder category)
    (x : QuotientRing category) :
    decode category order ((packEquiv category order).symm x) = x := by
  rw [← packEquiv_apply, Equiv.apply_symm_apply]

theorem recover_decode (category : Category) (order : ByteOrder category)
    (bytes : Fin (byteCount category) → Byte) :
    (packEquiv category order).symm (decode category order bytes) = bytes := by
  rw [← packEquiv_apply, Equiv.symm_apply_apply]

/-- Exact power-sum formula for the selected decoder; no byte-to-field map is
left opaque in this family. The order remains a visible argument. -/
theorem decode_formula (category : Category) (order : ByteOrder category)
    (bytes : Fin (byteCount category) → Byte) :
    decode category order bytes = ∑ i : Fin (width category),
      algebraMap (ZMod 2) (QuotientRing category)
        (bitCoefficient ((bytes (order i).1).val.testBit (order i).2.val)) *
        generator category ^ i.val := rfl

theorem sample_coordinate (category : Category) (order : ByteOrder category)
    (src : Spec.ByteSampling.Reader) (n count : Nat)
    (enough : n * byteCount category ≤ count) (i : Fin n) :
    (sample category order src n count enough).value i =
      decode category order (fun j => src.stream
        (src.position + (i.val * byteCount category + j.val))) := rfl

/-- Equality of the sampled field vector determines every used byte.
Extra consumed bytes beyond those packs are not claimed to be recoverable. -/
theorem sample_recovers_used_bytes (category : Category) (order : ByteOrder category)
    (src₁ src₂ : Spec.ByteSampling.Reader) (n count₁ count₂ : Nat)
    (h₁ : n * byteCount category ≤ count₁) (h₂ : n * byteCount category ≤ count₂)
    (heq : (sample category order src₁ n count₁ h₁).value =
      (sample category order src₂ n count₂ h₂).value)
    (i : Fin n) (j : Fin (byteCount category)) :
    src₁.stream (src₁.position + (i.val * byteCount category + j.val)) =
      src₂.stream (src₂.position + (i.val * byteCount category + j.val)) := by
  have hi := congrFun heq i
  simp only [sample_coordinate] at hi
  exact congrFun ((decode_bijective category order).injective hi) j

theorem batching_layout (category : Category) (order : ByteOrder category)
    (xof : Nat → Byte) (gammaCount w count₁ count₂ : Nat)
    (enough₁ : gammaCount * byteCount category ≤ count₁)
    (enough₂ : w * byteCount category ≤ count₂) :
    (expandBatching category order xof gammaCount w count₁ count₂ enough₁ enough₂).value =
      ((fun i => decode category order (fun j => xof (i.val * byteCount category + j.val))),
       (fun i => decode category order (fun j => xof (count₁ +
         (i.val * byteCount category + j.val))))) ∧
    (expandBatching category order xof gammaCount w count₁ count₂ enough₁ enough₂).next.position =
      count₁ + count₂ :=
  ByteSampling.expandBatching_layout xof (byteCount category) gammaCount w count₁ count₂
    enough₁ enough₂ (decode category order)

end SDitH.Proofs.FieldBytes
