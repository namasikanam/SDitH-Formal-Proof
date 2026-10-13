import SDitH.Proofs.IdealCipherFresh
import SDitH.Proofs.IntegerSamplingProbability

/-! A fresh key's encryption is uniform over all blocks. The ideal cipher's
fresh-input encryption is uniform over the key's unused outputs; when the
key has never been used, every output is unused, so the encryption of any
input under that key is uniform over all blocks. This is the ideal-cipher
input of the hidden leaf seed's uniformity: the hidden leaf is the
encryption, under its parent seed, of a fixed tweak, so it is uniform
whenever the parent seed was never used as a key. -/

namespace SDitH.Proofs.FreshKeyUniform

open Spec.IdealCipher IdealCipherFresh
open scoped Classical ENNReal

noncomputable section

variable {Key Block : Type*}

/-- A key never used in the history. -/
def FreshKey (world : World Key Block) (key : Key) : Prop :=
  ∀ e ∈ world.history, e.key ≠ key

theorem freshInput_of_freshKey (world : World Key Block) (key : Key) (hkey : FreshKey world key) (input : Block) :
    FreshInput world key input := by
  intro e he hk
  exact absurd hk (hkey e he)

theorem freshOutput_of_freshKey (world : World Key Block) (key : Key) (hkey : FreshKey world key) (output : Block) :
    FreshOutput world key output := by
  intro e he hk
  exact absurd hk (hkey e he)

variable [Fintype Key] [Fintype Block] [Nonempty Block]

/-- For a fresh key, the unused outputs are all blocks. -/
def unusedEquiv (world : World Key Block) (key : Key) (hkey : FreshKey world key) : UnusedOutput world key ≃ Block :=
  Equiv.subtypeUnivEquiv (freshOutput_of_freshKey world key hkey)

/-- Encryption under a fresh key is uniform over all blocks. -/
theorem fresh_key_encrypt_uniform (world : World Key Block) (key : Key) (hkey : FreshKey world key) (input : Block) :
    (query world (.encrypt key input)).map Prod.fst = PMF.uniformOfFintype Block := by
  have hfresh := freshInput_of_freshKey world key hkey input
  haveI : Nonempty (UnusedOutput world key) := unusedOutput_nonempty world key input hfresh
  rw [fresh_encrypt_uniform world key input hfresh]
  have h : (Subtype.val : UnusedOutput world key → Block) = unusedEquiv world key hkey := rfl
  rw [h]
  exact IntegerSamplingProbability.map_uniform_equiv (unusedEquiv world key hkey)

end
end SDitH.Proofs.FreshKeyUniform
