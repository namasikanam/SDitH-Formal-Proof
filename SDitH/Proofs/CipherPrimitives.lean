import SDitH.Spec.CipherPrimitives
import SDitH.Proofs.Rijndael
import SDitH.Proofs.Keccak
import SDitH.Proofs.SeedPrimitives

namespace SDitH.Proofs.CipherPrimitives

open Spec.DomainSeparation Spec.FieldRepresentation Spec.CipherPrimitives

theorem fromBits_bit (p : Spec.Rijndael.Profile) (input : Bits (32 * Spec.Rijndael.columns p))
    (byte : Fin (4 * Spec.Rijndael.columns p)) (bit : Fin 8) :
    ((fromBits p input)[byte]).getLsbD bit.val = input ⟨8 * byte.val + bit.val, by omega⟩ := by
  simp only [fromBits, Fin.getElem_fin, Vector.getElem_ofFn, Keccak.word_bit]

@[simp] theorem toBits_fromBits (p : Spec.Rijndael.Profile)
    (input : Bits (32 * Spec.Rijndael.columns p)) : toBits p (fromBits p input) = input := by
  funext i
  unfold toBits
  rw [fromBits_bit p input _ ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩]
  apply congrArg input
  apply Fin.ext
  dsimp
  omega

@[simp] theorem fromBits_toBits (p : Spec.Rijndael.Profile) (s : Spec.Rijndael.State p) :
    fromBits p (toBits p s) = s := by
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := fromBits_bit p (toBits p s) ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Fin.getElem_fin] at h
  rw [h]
  unfold toBits
  have hb : (⟨(8 * i + j) / 8, by omega⟩ : Fin (4 * Spec.Rijndael.columns p)) = ⟨i, hi⟩ := by
    apply Fin.ext
    dsimp
    omega
  have hj' : (8 * i + j) % 8 = j := by omega
  simp only [hb, hj', Fin.getElem_fin]

def bitStateEquiv (p : Spec.Rijndael.Profile) :
    Bits (32 * Spec.Rijndael.columns p) ≃ Spec.Rijndael.State p where
  toFun := fromBits p
  invFun := toBits p
  left_inv := toBits_fromBits p
  right_inv := fromBits_toBits p

theorem fipsBitIndex_involutive (p : Spec.Rijndael.Profile) : Function.Involutive (fipsBitIndex p) := by
  intro i
  apply Fin.ext
  dsimp [fipsBitIndex]
  omega

/-- The byte with displayed FIPS bit order has its highest coefficient first. -/
theorem fromFipsBits_bit (p : Spec.Rijndael.Profile)
    (input : Bits (32 * Spec.Rijndael.columns p))
    (byte : Fin (4 * Spec.Rijndael.columns p)) (bit : Fin 8) :
    ((fromFipsBits p input)[byte]).getLsbD bit.val =
      input ⟨8 * byte.val + (7 - bit.val), by omega⟩ := by
  rw [fromFipsBits, fromBits_bit]
  apply congrArg input
  apply Fin.ext
  dsimp [fipsBitIndex]
  omega

theorem encryptBits_bijective (p : Spec.Rijndael.Profile) (key : Bits (32 * Spec.Rijndael.columns p)) :
    Function.Bijective (encryptBits p key) :=
  (bitStateEquiv p).symm.bijective.comp
    ((Rijndael.encrypt_bijective p (fromBits p key)).comp (bitStateEquiv p).bijective)

theorem pad192_injective : Function.Injective Spec.SeedPrimitives.pad192 := by
  intro a b h
  funext i
  have hi := congrFun h ⟨i.val, by omega⟩
  simpa only [SeedPrimitives.pad192_preserves] using hi

/-- Enc is injective in its plaintext in all categories. Category III maps
192-bit plaintexts into 256-bit ciphertexts, without asserting surjectivity. -/
theorem enc_injective (category : Category) (key : Bits (width category)) :
    Function.Injective (enc category key) := by
  cases category with
  | i => exact (encryptBits_bijective .aes128 key).injective
  | iii => exact (encryptBits_bijective .rijndael256 (Spec.SeedPrimitives.pad192 key)).injective.comp pad192_injective
  | v => exact (encryptBits_bijective .rijndael256 key).injective

theorem encStarIII_prefix (key plaintext : Bits 192) (i : Fin 192) :
    encStar .iii key plaintext i = enc .iii key plaintext ⟨i.val, by
      change i.val < 256
      omega⟩ := rfl

theorem encStarI_permutation (key : Bits 128) : Function.Bijective (encStar .i key) :=
  encryptBits_bijective .aes128 key

theorem encStarV_permutation (key : Bits 256) : Function.Bijective (encStar .v key) :=
  encryptBits_bijective .rijndael256 key

theorem bavc_expandSeed (category : Category) (leafCount : Nat) (variant : Grinding)
    (salt : Bits (width category)) (address : Nat) (seed : Bits (width category)) :
    (bavcPrimitives category leafCount variant).expandSeed salt address seed =
      (encStar category seed (Spec.SeedPrimitives.cipherInput variant salt address false),
       encStar category seed (Spec.SeedPrimitives.cipherInput variant salt address true)) := rfl

theorem bavc_hash (category : Category) (leafCount : Nat) (variant : Grinding) :
    (bavcPrimitives category leafCount variant).hash = Spec.SHAKE.hash category := rfl

end SDitH.Proofs.CipherPrimitives
