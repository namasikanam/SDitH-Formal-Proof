import SDitH.Spec.KeySizeBoundary
import SDitH.Proofs.VariantParameters
import Mathlib.SetTheory.Cardinal.Finite

namespace SDitH.Proofs.KeySizeBoundary

open Spec Spec.DomainSeparation Spec.KeyGeneration Spec.KeySizeBoundary

def publicKeyEquiv (lambda r : Nat) : PublicKey lambda r ≃
    (Bits lambda × (Fin r → ZMod 2)) where
  toFun key := (key.seed, key.syndrome)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sizedSecretEquiv (lambda r witnessBits : Nat) : SizedSecretKey lambda r witnessBits ≃
    (PublicKey lambda r × (Fin witnessBits → ZMod 2)) where
  toFun key := (key.val.publicPart, fun i => key.val.witness[i.val]'(by
    rw [key.property]
    exact i.isLt))
  invFun pair := ⟨⟨pair.1, List.ofFn pair.2⟩, by simp⟩
  left_inv key := by
    apply Subtype.ext
    rcases key with ⟨⟨publicPart, witness⟩, hw⟩
    dsimp only
    subst witnessBits
    simp only [List.ofFn_getElem]
  right_inv pair := by
    rcases pair with ⟨publicPart, witness⟩
    simp

/-- Cardinalities concern all parsed typed values. They are not laws for the
seed-expanded key distribution or counts of valid secret SD witnesses. -/
theorem public_key_card (lambda r : Nat) : Nat.card (PublicKey lambda r) = 2 ^ (lambda + r) := by
  rw [Nat.card_congr (publicKeyEquiv lambda r)]
  simp [Bits, Nat.card_eq_fintype_card, pow_add]

theorem sized_secret_card (lambda r witnessBits : Nat) :
    Nat.card (SizedSecretKey lambda r witnessBits) = 2 ^ (lambda + r + witnessBits) := by
  rw [Nat.card_congr (sizedSecretEquiv lambda r witnessBits), Nat.card_prod, public_key_card]
  simp [Nat.card_eq_fintype_card, pow_add]

/-- Any injective encoder whose outputs all have the stated bit length has
at most one source value per possible bit string. No codec is selected. -/
theorem fixed_length_capacity {A : Type*} (encoding : A → List Bool) (bits : Nat)
    (hlength : HasBitLength encoding bits) (hinj : Function.Injective encoding) :
    Nat.card A ≤ 2 ^ bits := by
  let fixed : A → (Fin bits → Bool) :=
    fun value i => (encoding value)[i.val]'(by rw [hlength value]; exact i.isLt)
  have hrecover (value : A) : List.ofFn (fixed value) = encoding value := by
    unfold fixed
    have he := hlength value
    subst bits
    exact List.ofFn_getElem _
  have hf : Function.Injective fixed := by
    intro a b he
    apply hinj
    rw [← hrecover a, ← hrecover b, he]
  have hc := Nat.card_le_card_of_injective fixed hf
  simpa [Nat.card_fun, Nat.card_eq_fintype_card] using hc

theorem ceilBytes_le_iff (bits bytes : Nat) : ceilBytes bits ≤ bytes ↔ bits ≤ 8 * bytes := by
  constructor
  · intro h
    have hc := VariantParameters.ceilMultiple_covers 8 bits (by decide)
    rw [VariantParameters.ceilMultiple_eight] at hc
    unfold ceil8 at hc
    omega
  · intro h
    have hm := VariantParameters.ceilMultiple_minimal 8 bits bytes (by decide) h
    rw [VariantParameters.ceilMultiple_eight] at hm
    unfold ceil8 at hm
    omega

/-- A fixed-width injective encoding of the actual public-key type cannot
use fewer bits than its seed and binary syndrome together. -/
theorem public_encoding_bit_lower_bound {lambda r : Nat}
    (encoding : PublicKey lambda r → List Bool) (bits : Nat)
    (hlength : HasBitLength encoding bits) (hinj : Function.Injective encoding) :
    lambda + r ≤ bits := by
  have hc := fixed_length_capacity encoding bits hlength hinj
  rw [public_key_card] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

theorem secret_encoding_bit_lower_bound {lambda r witnessBits : Nat}
    (encoding : SizedSecretKey lambda r witnessBits → List Bool) (bits : Nat)
    (hlength : HasBitLength encoding bits) (hinj : Function.Injective encoding) :
    lambda + r + witnessBits ≤ bits := by
  have hc := fixed_length_capacity encoding bits hlength hinj
  rw [sized_secret_card] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

/-- Necessary bounds on the existing Serialize interface. These hypotheses
are deliberately not installed as a codec contract in Specification/Assumptions.
In particular they prove no parser round trip or concrete byte correspondence. -/
theorem public_serialization_byte_lower_bound {lambda r : Nat}
    (encoding : Serialization lambda r) (bytes : Nat)
    (hlength : HasBitLength encoding.encodePublic (8 * bytes))
    (hinj : Function.Injective encoding.encodePublic) : ceilBytes (lambda + r) ≤ bytes := by
  apply (ceilBytes_le_iff _ _).mpr
  exact public_encoding_bit_lower_bound encoding.encodePublic _ hlength hinj

theorem secret_serialization_byte_lower_bound {lambda r witnessBits : Nat}
    (encoding : Serialization lambda r) (bytes : Nat)
    (hlength : HasBitLength
      (fun key : SizedSecretKey lambda r witnessBits => encoding.encodeSecret key.val) (8 * bytes))
    (hinj : Function.Injective
      (fun key : SizedSecretKey lambda r witnessBits => encoding.encodeSecret key.val)) :
    ceilBytes (lambda + r + witnessBits) ≤ bytes := by
  apply (ceilBytes_le_iff _ _).mpr
  exact secret_encoding_bit_lower_bound _ _ hlength hinj

/-- Exact declared bit payloads and unavoidable byte-capacity slack. The
four spare Category-III bits do not determine a padding value or position. -/
theorem submitted_payload_and_slack :
    (RSDParameters.categoryI.lambda + RSDParameters.categoryI.codimension,
      RSDParameters.categoryI.witnessBits,
      8 * secretKeyBytes RSDParameters.categoryI -
        (RSDParameters.categoryI.lambda + RSDParameters.categoryI.codimension +
          RSDParameters.categoryI.witnessBits)) = (560, 616, 0) ∧
    (RSDParameters.categoryIII.lambda + RSDParameters.categoryIII.codimension,
      RSDParameters.categoryIII.witnessBits,
      8 * secretKeyBytes RSDParameters.categoryIII -
        (RSDParameters.categoryIII.lambda + RSDParameters.categoryIII.codimension +
          RSDParameters.categoryIII.witnessBits)) = (784, 876, 4) ∧
    (RSDParameters.categoryV.lambda + RSDParameters.categoryV.codimension,
      RSDParameters.categoryV.witnessBits,
      8 * secretKeyBytes RSDParameters.categoryV -
        (RSDParameters.categoryV.lambda + RSDParameters.categoryV.codimension +
          RSDParameters.categoryV.witnessBits)) = (1056, 1144, 0) := by decide

end SDitH.Proofs.KeySizeBoundary
