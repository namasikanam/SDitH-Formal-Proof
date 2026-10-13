import SDitH.Proofs.LinesMention

/-! Distinct byte prefixes separate the chain's queries. The byte-bit
encoding is injective, and two lists with different eight-bit prefixes
differ; so the lines query (prefix three) never coincides with the
auxiliary query (prefix two), the outer string or a row query (prefix one),
nor with the mask input (by length). These separate the tail's lines query
from every query the prefix makes. -/

namespace SDitH.Proofs.QueryPrefixes

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCHashChain
open SDitH.Proofs.BAVCChainInputs

variable {lambda tau N : Nat}

/-- The byte-bit encoding is injective. -/
theorem byteBits_injective : Function.Injective byteBits := by
  intro b b' h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 8
  · have hfun := List.ofFn_injective h
    exact congrFun hfun ⟨j, hj⟩
  · have hpow : (256 : ℕ) ≤ 2 ^ j := by
      calc (256 : ℕ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb : b.val < 2 ^ j := lt_of_lt_of_le b.isLt hpow
    have hb' : b'.val < 2 ^ j := lt_of_lt_of_le b'.isLt hpow
    rw [Nat.testBit_lt_two_pow hb, Nat.testBit_lt_two_pow hb']

/-- Lists with different byte prefixes differ. -/
theorem prefix_ne (b b' : Byte) (hb : b ≠ b') (x y : List Bool) : byteBits b ++ x ≠ byteBits b' ++ y := by
  intro h
  have hlen : (byteBits b).length = (byteBits b').length := by rw [byteBits_length, byteBits_length]
  exact hb (byteBits_injective (List.append_inj_left h hlen))

theorem linesQuery_ne_auxQuery (auxiliary root : Digest lambda) (tail tail' : List Bool) :
    linesQuery auxiliary tail ≠ auxQuery root tail' :=
  prefix_ne 3 2 (by decide) _ _

theorem linesQuery_ne_outerString (auxiliary : Digest lambda) (tail : List Bool) (salt : Seed lambda)
    (rowHashes : Fin tau → Digest lambda) : linesQuery auxiliary tail ≠ outerString salt rowHashes :=
  prefix_ne 3 1 (by decide) _ _

theorem linesQuery_ne_rowQuery (auxiliary : Digest lambda) (tail : List Bool) (commits : Spec.BAVCBinding.Commitments lambda tau N)
    (e : Fin tau) : linesQuery auxiliary tail ≠ Spec.BAVCBinding.rowQuery commits e :=
  prefix_ne 3 1 (by decide) _ _

end SDitH.Proofs.QueryPrefixes
