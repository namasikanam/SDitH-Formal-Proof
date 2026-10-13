import SDitH.Spec.PRG
import SDitH.Proofs.CipherPrimitives
import SDitH.Proofs.ByteSampling

namespace SDitH.Proofs.PRG

open Spec.DomainSeparation Spec.FieldRepresentation Spec.PRG

theorem ciphertextBytes_positive (category : Category) : 0 < ciphertextBytes category := by
  cases category <;> decide

theorem ciphertextBytes_width (category : Category) :
    8 * ciphertextBytes category = Spec.CipherPrimitives.ciphertextWidth category := by
  cases category <;> decide

/-- The implemented quotient is the least number of blocks covering the
requested bits for the explicitly supplied positive denominator. -/
theorem blockCount_le_iff (size : BlockSize) (nbytes n : Nat) :
    blockCount size nbytes ≤ n ↔ 8 * nbytes ≤ n * size.bits := by
  rw [blockCount, Nat.div_le_iff_le_mul size.positive]
  have h := size.positive
  omega

theorem blockCount_covers (size : BlockSize) (nbytes : Nat) :
    8 * nbytes ≤ blockCount size nbytes * size.bits :=
  (blockCount_le_iff size nbytes _).mp le_rfl

theorem blockCount_zero_iff (size : BlockSize) (nbytes : Nat) :
    blockCount size nbytes = 0 ↔ nbytes = 0 := by
  rw [← Nat.le_zero, blockCount_le_iff]
  omega

theorem blockCount_positive (size : BlockSize) (nbytes : Nat) (hn : 0 < nbytes) :
    0 < blockCount size nbytes := by
  have h := blockCount_zero_iff size nbytes
  omega

theorem blockCount_enough_bytes (category : Category) (size : BlockSize)
    (hsize : size.bits ≤ Spec.CipherPrimitives.ciphertextWidth category) (nbytes : Nat) :
    nbytes ≤ blockCount size nbytes * ciphertextBytes category := by
  rw [← ciphertextBytes_width] at hsize
  have h := (blockCount_covers size nbytes).trans (Nat.mul_le_mul_left (blockCount size nbytes) hsize)
  nlinarith

theorem parseShape_i (count : Nat) : ParseShape .i count := rfl
theorem parseShape_v (count : Nat) : ParseShape .v count := rfl

theorem parseShape_iii_iff (count : Nat) : ParseShape .iii count ↔ count = 0 := by
  change count * 32 = count * 24 ↔ count = 0
  omega

theorem parseShape_nonIII (category : Category) (h : category ≠ .iii) (count : Nat) :
    ParseShape category count := by
  cases category with
  | i => exact parseShape_i count
  | iii => exact (h rfl).elim
  | v => exact parseShape_v count

theorem byteInBlock_bit (category : Category)
    (value : Bits (Spec.CipherPrimitives.ciphertextWidth category))
    (j : Fin (ciphertextBytes category)) (k : Fin 8) :
    (byteInBlock category value j).val.testBit k.val =
      value ⟨8 * j.val + k.val, by
        have hj := j.isLt
        have hk := k.isLt
        cases category <;> simp only [ciphertextBytes, Spec.CipherPrimitives.ciphertextWidth] at * <;> omega⟩ := by
  change (Spec.Keccak.word _).getLsbD k.val = _
  exact Keccak.word_bit _ k

theorem byteInBlock_injective (category : Category) : Function.Injective (byteInBlock category) := by
  intro a b hab
  funext i
  let j : Fin (ciphertextBytes category) := ⟨i.val / 8, by
    have h := i.isLt
    have hw := ciphertextBytes_width category
    omega⟩
  let k : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have hh := congrArg (fun byte : Byte => byte.val.testBit k.val) (congrFun hab j)
  simp only [byteInBlock_bit] at hh
  have he : (⟨8 * j.val + k.val, by
      have h := i.isLt
      dsimp [j, k]
      omega⟩ : Fin (Spec.CipherPrimitives.ciphertextWidth category)) = i := by
    apply Fin.ext
    dsimp [j, k]
    omega
  simpa only [he] using hh

theorem byteArray_coordinate (category : Category) (seed salt : Bits (width category))
    (count : Nat) (i : Fin (count * ciphertextBytes category)) :
    (byteArray category seed salt count)[i] = stream category seed salt i.val := by
  simp only [byteArray, blockArray, Fin.getElem_fin, Vector.getElem_ofFn, stream]

theorem stream_at_block (category : Category) (seed salt : Bits (width category))
    (n : Nat) (j : Fin (ciphertextBytes category)) :
    stream category seed salt (n * ciphertextBytes category + j.val) =
      byteInBlock category (block category seed salt n) j := by
  have hj := j.isLt
  have hd : (n * ciphertextBytes category + j.val) / ciphertextBytes category = n :=
    by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (ciphertextBytes_positive category), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (n * ciphertextBytes category + j.val) % ciphertextBytes category = j.val :=
    by rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [stream, hd, hm]

theorem byteLoop_eq_flatten (category : Category) (seed salt : Bits (width category)) (count : Nat) :
    byteLoop category seed salt count =
      (List.ofFn fun i : Fin count => List.ofFn (byteInBlock category (block category seed salt i.val))).flatten := by
  induction count with
  | zero => simp [byteLoop]
  | succ n ih =>
    rw [byteLoop, ih, List.ofFn_succ_last]
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl

/-- The indexed implementation agrees with the increasing append loop,
including the complete final block rather than only its requested prefix. -/
theorem byteArray_eq_loop (category : Category) (seed salt : Bits (width category)) (count : Nat) :
    List.ofFn (fun i : Fin (count * ciphertextBytes category) => (byteArray category seed salt count)[i]) =
      byteLoop category seed salt count := by
  simp only [byteArray_coordinate]
  rw [List.ofFn_mul, byteLoop_eq_flatten]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  exact stream_at_block category seed salt i.val j

theorem byteLoop_length (category : Category) (seed salt : Bits (width category)) (count : Nat) :
    (byteLoop category seed salt count).length = count * ciphertextBytes category := by
  rw [← byteArray_eq_loop, List.length_ofFn]

theorem parseAndTake_success (category : Category) (seed salt : Bits (width category)) (count nbytes : Nat)
    (hs : ParseShape category count) (he : nbytes ≤ declaredBytes category count) :
    parseAndTake category count nbytes (byteArray category seed salt count) =
      some (Vector.ofFn fun i : Fin nbytes => stream category seed salt i.val) := by
  rw [parseAndTake, dif_pos hs, dif_pos he]
  apply congrArg some
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  exact byteArray_coordinate category seed salt count ⟨i, by
    unfold ParseShape at hs
    omega⟩

theorem parseAndTake_has_output_iff (category : Category) (count nbytes : Nat)
    (bytes : Vector Byte (count * ciphertextBytes category)) :
    (∃ out, parseAndTake category count nbytes bytes = some out) ↔
      ParseShape category count ∧ nbytes ≤ declaredBytes category count := by
  unfold parseAndTake
  split_ifs <;> simp_all

theorem run_success (category : Category) (variant : Grinding) (size : BlockSize)
    (seed : Bits (width category)) (salt : Option (Bits (width category)))
    (tweak : Option Byte) (nbytes : Nat) (prepared : Bits (width category))
    (hp : prepareSalt category variant salt tweak = some prepared)
    (hs : ParseShape category (blockCount size nbytes))
    (he : nbytes ≤ declaredBytes category (blockCount size nbytes)) :
    run category variant size seed salt tweak nbytes =
      some (Vector.ofFn fun i : Fin nbytes => stream category seed prepared i.val) := by
  simp only [run, hp]
  exact parseAndTake_success category seed prepared _ _ hs he

/-- The complete characterization of a defined transcription result. None of
the preparation, shape or allocation obligations is hidden in an axiom. -/
theorem run_eq_some_iff (category : Category) (variant : Grinding) (size : BlockSize)
    (seed : Bits (width category)) (salt : Option (Bits (width category)))
    (tweak : Option Byte) (nbytes : Nat) (out : Vector Byte nbytes) :
    run category variant size seed salt tweak nbytes = some out ↔
      ∃ prepared, prepareSalt category variant salt tweak = some prepared ∧
        ParseShape category (blockCount size nbytes) ∧
        nbytes ≤ declaredBytes category (blockCount size nbytes) ∧
        out = Vector.ofFn (fun i : Fin nbytes => stream category seed prepared i.val) := by
  constructor
  · intro h
    obtain ⟨prepared, hp, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hs, he⟩ := (parseAndTake_has_output_iff category (blockCount size nbytes)
      nbytes (byteArray category seed prepared (blockCount size nbytes))).mp ⟨out, hr⟩
    refine ⟨prepared, hp, hs, he, ?_⟩
    exact Option.some.inj (hr.symm.trans (parseAndTake_success category seed prepared _ _ hs he))
  · rintro ⟨prepared, hp, hs, he, rfl⟩
    exact run_success category variant size seed salt tweak nbytes prepared hp hs he

theorem run_output_coordinate (category : Category) (variant : Grinding) (size : BlockSize)
    (seed : Bits (width category)) (salt : Option (Bits (width category)))
    (tweak : Option Byte) (nbytes : Nat) (out : Vector Byte nbytes)
    (prepared : Bits (width category))
    (hp : prepareSalt category variant salt tweak = some prepared)
    (hr : run category variant size seed salt tweak nbytes = some out) (i : Fin nbytes) :
    out[i] = stream category seed prepared i.val := by
  obtain ⟨prepared', hp', _, _, ho⟩ := (run_eq_some_iff category variant size seed salt tweak nbytes out).mp hr
  have he : prepared' = prepared := Option.some.inj (hp'.symm.trans hp)
  subst prepared'
  rw [ho]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

/-- Successful requests at different lengths or supplied block sizes read the
same prefix. This theorem does not claim all requested lengths are defined. -/
theorem run_prefix (category : Category) (variant : Grinding) (size₁ size₂ : BlockSize)
    (seed : Bits (width category)) (salt : Option (Bits (width category))) (tweak : Option Byte)
    (n₁ n₂ : Nat) (out₁ : Vector Byte n₁) (out₂ : Vector Byte n₂)
    (h₁ : run category variant size₁ seed salt tweak n₁ = some out₁)
    (h₂ : run category variant size₂ seed salt tweak n₂ = some out₂)
    (i : Nat) (hi₁ : i < n₁) (hi₂ : i < n₂) : out₁[i] = out₂[i] := by
  obtain ⟨prepared, hp, _, _, _⟩ := (run_eq_some_iff category variant size₁ seed salt tweak n₁ out₁).mp h₁
  exact (run_output_coordinate category variant size₁ seed salt tweak n₁ out₁ prepared hp h₁ ⟨i, hi₁⟩).trans
    (run_output_coordinate category variant size₂ seed salt tweak n₂ out₂ prepared hp h₂ ⟨i, hi₂⟩).symm

theorem run_missing_tweak (category : Category) (variant : Grinding) (size : BlockSize)
    (seed salt : Bits (width category)) (nbytes : Nat) :
    run category variant size seed (some salt) none nbytes = none := rfl

/-- Complete finite execution where the printed Parse dimensions agree and
the supplied denominator does not underallocate ciphertext bytes. -/
theorem run_nonIII (category : Category) (hc : category ≠ .iii) (variant : Grinding) (size : BlockSize)
    (hsize : size.bits ≤ Spec.CipherPrimitives.ciphertextWidth category)
    (seed : Bits (width category)) (salt : Option (Bits (width category)))
    (tweak : Option Byte) (nbytes : Nat) (prepared : Bits (width category))
    (hp : prepareSalt category variant salt tweak = some prepared) :
    run category variant size seed salt tweak nbytes =
      some (Vector.ofFn fun i : Fin nbytes => stream category seed prepared i.val) := by
  have hs := parseShape_nonIII category hc (blockCount size nbytes)
  apply run_success category variant size seed salt tweak nbytes prepared hp hs
  rw [← hs]
  exact blockCount_enough_bytes category size hsize nbytes

/-- No complete byte parse can give the source's declared output shape for a
positive Category-III request. This is a source-elaboration failure, not a
rejection branch of Algorithm 6 and not a corrected/truncated PRG. -/
theorem run_iii_unresolved (variant : Grinding) (size : BlockSize) (seed : Bits 192)
    (salt : Option (Bits 192)) (tweak : Option Byte) (nbytes : Nat) (hn : 0 < nbytes) :
    run .iii variant size seed salt tweak nbytes = none := by
  have hs : ¬ParseShape .iii (blockCount size nbytes) := by
    rw [parseShape_iii_iff]
    exact Nat.ne_of_gt (blockCount_positive size nbytes hn)
  simp only [run]
  cases prepareSalt .iii variant salt tweak <;> simp [parseAndTake, hs]

end SDitH.Proofs.PRG
