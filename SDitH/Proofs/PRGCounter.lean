import SDitH.Proofs.PRG

namespace SDitH.Proofs.PRGCounter

open Spec.DomainSeparation Spec.FieldRepresentation Spec.PRG

theorem width_ge_26 (category : Category) : 26 ≤ width category := by cases category <;> decide

theorem littleEndian_mod (lambda counter : Nat) :
    littleEndian lambda (counter % 2 ^ lambda) = littleEndian lambda counter := by
  funext j
  simp only [littleEndian, Nat.testBit_mod_two_pow, j.isLt, decide_true, Bool.true_and]

theorem littleEndian_injective_below {lambda a b : Nat} (ha : a < 2 ^ lambda) (hb : b < 2 ^ lambda)
    (h : littleEndian lambda a = littleEndian lambda b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < lambda
  · exact congrFun h ⟨j, hj⟩
  · have hp : 2 ^ lambda ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]

theorem littleEndian_eq_iff_mod (lambda a b : Nat) :
    littleEndian lambda a = littleEndian lambda b ↔ a % 2 ^ lambda = b % 2 ^ lambda := by
  constructor
  · intro h
    apply littleEndian_injective_below (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
    simpa only [littleEndian_mod] using h
  · intro h
    rw [← littleEndian_mod lambda a, ← littleEndian_mod lambda b, h]

theorem plaintext_eq_iff (category : Category) (salt : Bits (width category)) (a b : Nat) :
    plaintext category salt a = plaintext category salt b ↔
      littleEndian (width category) a = littleEndian (width category) b := by
  constructor
  · intro h
    funext j
    exact Bool.xor_right_inj.mp (congrFun h j)
  · intro h
    funext j
    exact congrArg (salt j ^^ ·) (congrFun h j)

/-- The actual Enc permutation/injection connects counter encoding to block
equality. The condition is modulo the fixed plaintext width in every category. -/
theorem block_eq_iff_mod (category : Category) (seed salt : Bits (width category)) (a b : Nat) :
    block category seed salt a = block category seed salt b ↔
      a % 2 ^ width category = b % 2 ^ width category := by
  rw [← littleEndian_eq_iff_mod, ← plaintext_eq_iff category salt]
  exact (CipherPrimitives.enc_injective category seed).eq_iff

theorem block_injective_below (category : Category) (seed salt : Bits (width category))
    {a b : Nat} (ha : a < 2 ^ width category) (hb : b < 2 ^ width category)
    (h : block category seed salt a = block category seed salt b) : a = b := by
  have he := (block_eq_iff_mod category seed salt a b).mp h
  simpa only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using he

theorem block_period (category : Category) (seed salt : Bits (width category)) (counter : Nat) :
    block category seed salt (counter + 2 ^ width category) = block category seed salt counter := by
  rw [block_eq_iff_mod]
  exact Nat.add_mod_right _ _

theorem stream_period (category : Category) (seed salt : Bits (width category)) (position : Nat) :
    stream category seed salt (position + 2 ^ width category * ciphertextBytes category) =
      stream category seed salt position := by
  simp only [stream,
    Nat.add_mul_div_right _ _ (PRG.ciphertextBytes_positive category),
    Nat.add_mul_mod_self_right, block_period]

theorem shiftedTweak_low (tweak : Byte) (j : Nat) (hj : j < 16) :
    (shiftedTweak tweak).val.testBit j = false := by
  simp only [shiftedTweak, Nat.testBit_two_pow_mul]
  have h : ¬16 ≤ j := by omega
  simp only [h, decide_false, Bool.false_and]

theorem shiftedTweak_high (tweak : Byte) (j : Fin 8) :
    (shiftedTweak tweak).val.testBit (16 + j.val) = tweak.val.testBit j.val := by
  simp only [shiftedTweak, Nat.testBit_two_pow_mul, Nat.le_add_right,
    decide_true, Bool.true_and, Nat.add_sub_cancel_left]

theorem saltedPlaintext_low (category : Category) (variant : Grinding) (salt : Bits (width category))
    (tweak : Byte) (counter : Nat) (j : Fin 16) :
    plaintext category (tweakSalt variant salt (shiftedTweak tweak) false) counter
      ⟨j.val, by have := width_ge_26 category; omega⟩ = counter.testBit j.val := by
  rw [plaintext, DomainSeparation.tweak_low_bits (width_ge_26 category) variant salt
    (shiftedTweak tweak) false _ (show j.val < 24 by omega), shiftedTweak_low tweak _ j.isLt]
  simp only [littleEndian, Bool.false_xor]

theorem saltedPlaintext_tag (category : Category) (variant : Grinding) (salt : Bits (width category))
    (tweak : Byte) (counter : Nat) (hc : counter < 2 ^ 16) (j : Fin 8) :
    plaintext category (tweakSalt variant salt (shiftedTweak tweak) false) counter
      ⟨16 + j.val, by have := width_ge_26 category; omega⟩ = tweak.val.testBit j.val := by
  rw [plaintext, DomainSeparation.tweak_low_bits (width_ge_26 category) variant salt
    (shiftedTweak tweak) false _ (show 16 + j.val < 24 by omega), shiftedTweak_high]
  have hp : counter < 2 ^ (16 + j.val) := hc.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [littleEndian, Nat.testBit_lt_two_pow hp, Bool.xor_false]

/-- The low 16 counter bits and next 8 tweak bits are independently
recoverable while counters stay below 2^16. -/
theorem saltedPlaintext_injective (category : Category) (variant : Grinding)
    (salt : Bits (width category)) (t₁ t₂ : Byte) (a b : Nat)
    (ha : a < 2 ^ 16) (hb : b < 2 ^ 16)
    (h : plaintext category (tweakSalt variant salt (shiftedTweak t₁) false) a =
      plaintext category (tweakSalt variant salt (shiftedTweak t₂) false) b) :
    t₁ = t₂ ∧ a = b := by
  constructor
  · apply ByteSampling.byte_bits_injective
    intro j
    have he := congrFun h ⟨16 + j.val, by have := width_ge_26 category; omega⟩
    simpa only [saltedPlaintext_tag category variant salt t₁ a ha j,
      saltedPlaintext_tag category variant salt t₂ b hb j] using he
  · apply littleEndian_injective_below ha hb
    funext j
    have he := congrFun h ⟨j.val, by have := width_ge_26 category; omega⟩
    simpa only [littleEndian, saltedPlaintext_low category variant salt t₁ a j,
      saltedPlaintext_low category variant salt t₂ b j] using he

theorem saltedBlocks_injective (category : Category) (variant : Grinding)
    (seed salt : Bits (width category)) (t₁ t₂ : Byte) (a b : Nat)
    (ha : a < 2 ^ 16) (hb : b < 2 ^ 16)
    (h : block category seed (tweakSalt variant salt (shiftedTweak t₁) false) a =
      block category seed (tweakSalt variant salt (shiftedTweak t₂) false) b) :
    t₁ = t₂ ∧ a = b :=
  saltedPlaintext_injective category variant salt t₁ t₂ a b ha hb
    (CipherPrimitives.enc_injective category seed h)

theorem tweak_high_independent {lambda : Nat} (variant : Grinding) (salt : Bits lambda)
    (t₁ t₂ : Tweak) (bit : Bool) (j : Fin lambda) (hj : 24 ≤ j.val) :
    tweakSalt variant salt t₁ bit j = tweakSalt variant salt t₂ bit j := by
  have hn : ¬j.val < 24 := by omega
  cases variant <;> simp only [tweakSalt, hn, if_false]

/-- The joint bound above cannot be dropped: counter 2^16 with tweak 0
produces exactly the same input as counter 0 with tweak 1, under the same salt.
This is a statement about these explicit inputs, not a signature attack. -/
theorem saltedPlaintext_overlap (category : Category) (variant : Grinding) (salt : Bits (width category)) :
    plaintext category (tweakSalt variant salt (shiftedTweak 0) false) (2 ^ 16) =
      plaintext category (tweakSalt variant salt (shiftedTweak 1) false) 0 := by
  funext j
  by_cases hj : j.val < 24
  · rw [plaintext, plaintext, DomainSeparation.tweak_low_bits (width_ge_26 category) variant salt _ false j hj,
      DomainSeparation.tweak_low_bits (width_ge_26 category) variant salt _ false j hj]
    change ((0 : Nat).testBit j.val ^^ (2 ^ 16 : Nat).testBit j.val) =
      ((2 ^ 16 : Nat).testBit j.val ^^ (0 : Nat).testBit j.val)
    simp only [Nat.zero_testBit, Bool.false_xor, Bool.xor_false]
  · have hp : 2 ^ 16 < 2 ^ j.val := Nat.pow_lt_pow_right (by decide) (by omega)
    simp only [plaintext, littleEndian, Nat.testBit_lt_two_pow hp, Nat.zero_testBit, Bool.xor_false]
    exact tweak_high_independent variant salt _ _ false j (by omega)

theorem saltedBlocks_overlap (category : Category) (variant : Grinding) (seed salt : Bits (width category)) :
    block category seed (tweakSalt variant salt (shiftedTweak 0) false) (2 ^ 16) =
      block category seed (tweakSalt variant salt (shiftedTweak 1) false) 0 :=
  congrArg (Spec.CipherPrimitives.enc category seed) (saltedPlaintext_overlap category variant salt)

end SDitH.Proofs.PRGCounter
