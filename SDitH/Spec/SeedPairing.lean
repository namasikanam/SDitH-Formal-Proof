import SDitH.Spec.SeedPrimitives

/-! The companion plaintext in the source two-call seed construction. This
operation toggles the lowest bit; its correspondence with the two actual
tweaks, and its compatibility with Category-III padding, are proved separately. -/

namespace SDitH.Spec.SeedPairing

open DomainSeparation

def companion {n : Nat} (input : Bits n) : Bits n :=
  fun i => if i.val = 0 then !input i else input i

end SDitH.Spec.SeedPairing
