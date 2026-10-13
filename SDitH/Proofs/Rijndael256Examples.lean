import SDitH.Spec.Rijndael
import Mathlib.Tactic

/-! The Design of Rijndael (2002), Appendix D.3, printed pp. 217 and 219.
The first vector encrypts an all-zero block under an all-zero key. The second
encrypts the first ciphertext under the same key. Both block and key have
256 bits. These are designer-published test vectors, not AES-256 vectors. -/

namespace SDitH.Proofs.Rijndael256Examples

open Spec.Rijndael
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async false

def zeroBlock : State .rijndael256 := Vector.replicate 32 (0#8)

def ciphertext1 : State .rijndael256 := #v[0xc6#8, 0x22#8, 0x7e#8, 0x77#8, 0x40#8, 0xb7#8, 0xe5#8, 0x3b#8, 0x5c#8, 0xb7#8, 0x78#8, 0x65#8, 0x27#8, 0x8e#8, 0xab#8, 0x07#8, 0x26#8, 0xf6#8, 0x23#8, 0x66#8, 0xd9#8, 0xaa#8, 0xba#8, 0xd9#8, 0x08#8, 0x93#8, 0x61#8, 0x23#8, 0xa1#8, 0xfc#8, 0x8a#8, 0xf3#8]

def ciphertext2 : State .rijndael256 := #v[0x98#8, 0x43#8, 0xe8#8, 0x07#8, 0x31#8, 0x9c#8, 0x32#8, 0xad#8, 0x1e#8, 0xa3#8, 0x93#8, 0x5e#8, 0xf5#8, 0x6a#8, 0x2b#8, 0xa9#8, 0x6e#8, 0x4b#8, 0xf1#8, 0x9c#8, 0x30#8, 0xe4#8, 0x7d#8, 0x88#8, 0xa2#8, 0xb9#8, 0x7c#8, 0xbb#8, 0xf2#8, 0xe1#8, 0x59#8, 0xe7#8]

theorem first_encrypt_checked : encrypt .rijndael256 zeroBlock zeroBlock = ciphertext1 := by
  decide +kernel

theorem second_encrypt_checked : encrypt .rijndael256 zeroBlock ciphertext1 = ciphertext2 := by
  decide +kernel

end SDitH.Proofs.Rijndael256Examples
