import SDitH.Spec.KeyGeneration
import SDitH.Spec.Parameters

/-! The typed key-space and length boundary in Algorithms 2–4 and §4.2.
The source names Serialize/Deserialize and orders their fields, but does not
give a byte codec or padding policy. This file selects neither. The fixed-size
secret-key view uses the witness length expected by Algorithm 3's parser,
without asserting that an arbitrary raw key has that length or is a valid SD
witness. A length predicate is not an assertion about an implemented codec.
-/

namespace SDitH.Spec.KeySizeBoundary

abbrev SizedSecretKey (lambda r witnessBits : Nat) :=
  {key : KeyGeneration.SecretKey lambda r // key.witness.length = witnessBits}

def HasBitLength {A : Type*} (encoding : A → List Bool) (bits : Nat) : Prop :=
  ∀ value, (encoding value).length = bits

end SDitH.Spec.KeySizeBoundary
