import SDitH.Proofs.PRG
import SDitH.Spec.FieldBytes

/-! Finite Algorithm-6 outputs and the readers used by §3.2.2. Every use of
the zero-extended finite reader below is bounded by the actual output length.
These are deterministic correspondence results, not sampling-law claims.
-/

namespace SDitH.Proofs.PRGSampling

open Spec.DomainSeparation Spec.FieldRepresentation Spec.PRG Spec.ByteSampling

theorem finiteReader_coordinate {nbytes : Nat} (out : Vector Byte nbytes)
    (i : Nat) (hi : i < nbytes) :
    (finiteReader (count := nbytes) (fun j => out[j])).stream i = out[i] := by
  simp only [finiteReader, dif_pos hi, Fin.getElem_fin]

theorem readBytes_prefix (category : Category) (seed prepared : Bits (width category))
    (nbytes : Nat) (out : Vector Byte nbytes)
    (ho : ∀ i : Fin nbytes, out[i] = stream category seed prepared i.val)
    (offset count : Nat) (within : offset + count ≤ nbytes) :
    readBytes (advance (finiteReader (count := nbytes) (fun j => out[j])) offset) count =
      readBytes (advance (reader category seed prepared) offset) count := by
  funext i
  have hi : offset + i.val < nbytes := by have := i.isLt; omega
  change (finiteReader (count := nbytes) (fun j => out[j])).stream (0 + offset + i.val) =
    stream category seed prepared (0 + offset + i.val)
  simp only [Nat.zero_add, finiteReader, dif_pos hi, Fin.getElem_fin]
  exact ho ⟨offset + i.val, hi⟩

theorem sampleBinary_of_readBytes (src₁ src₂ : Reader) (n count : Nat)
    (enough : n ≤ 8 * count) (h : readBytes src₁ count = readBytes src₂ count) :
    (sampleBinary src₁ n count enough).value = (sampleBinary src₂ n count enough).value := by
  funext j
  unfold sampleBinary
  rw [h]

theorem sampleExtension_of_readBytes {F : Type*} (src₁ src₂ : Reader) (b n count : Nat)
    (enough : n * b ≤ count) (decode : (Fin b → Byte) → F)
    (h : readBytes src₁ count = readBytes src₂ count) :
    (sampleExtension src₁ b n count enough decode).value =
      (sampleExtension src₂ b n count enough decode).value := by
  funext j
  unfold sampleExtension
  rw [h]

theorem sampleBinary_prefix (category : Category) (seed prepared : Bits (width category))
    (nbytes : Nat) (out : Vector Byte nbytes)
    (ho : ∀ i : Fin nbytes, out[i] = stream category seed prepared i.val)
    (offset n count : Nat) (within : offset + count ≤ nbytes) (enough : n ≤ 8 * count) :
    (sampleBinary (advance (finiteReader (count := nbytes) (fun j => out[j])) offset) n count enough).value =
      (sampleBinary (advance (reader category seed prepared) offset) n count enough).value :=
  sampleBinary_of_readBytes _ _ _ _ enough (readBytes_prefix category seed prepared nbytes out ho offset count within)

theorem sampleExtension_prefix {F : Type*} (category : Category) (seed prepared : Bits (width category))
    (nbytes : Nat) (out : Vector Byte nbytes)
    (ho : ∀ i : Fin nbytes, out[i] = stream category seed prepared i.val)
    (offset b n count : Nat) (within : offset + count ≤ nbytes) (enough : n * b ≤ count)
    (decode : (Fin b → Byte) → F) :
    (sampleExtension (advance (finiteReader (count := nbytes) (fun j => out[j])) offset) b n count enough decode).value =
      (sampleExtension (advance (reader category seed prepared) offset) b n count enough decode).value :=
  sampleExtension_of_readBytes _ _ _ _ _ enough decode
    (readBytes_prefix category seed prepared nbytes out ho offset count within)

theorem fieldSample_prefix (category : Category) (order : Spec.FieldBytes.ByteOrder category)
    (seed prepared : Bits (width category)) (nbytes : Nat) (out : Vector Byte nbytes)
    (ho : ∀ i : Fin nbytes, out[i] = stream category seed prepared i.val)
    (offset n count : Nat) (within : offset + count ≤ nbytes)
    (enough : n * Spec.FieldBytes.byteCount category ≤ count) :
    (Spec.FieldBytes.sample category order (advance (finiteReader (count := nbytes) (fun j => out[j])) offset) n count enough).value =
      (Spec.FieldBytes.sample category order (advance (reader category seed prepared) offset) n count enough).value :=
  sampleExtension_prefix category seed prepared nbytes out ho offset _ n count within enough _

theorem rowByte_lt {row rows bit cols count : Nat} (hr : row < rows) (hb : bit < cols)
    (enough : cols ≤ 8 * count) : row * count + bit / 8 < rows * count := by
  have hbit : bit / 8 < count := by omega
  have hrow := Nat.mul_le_mul_right count hr
  simp only [Nat.succ_mul] at hrow
  omega

theorem sampleRows_prefix (category : Category) (seed prepared : Bits (width category))
    (nbytes : Nat) (out : Vector Byte nbytes)
    (ho : ∀ i : Fin nbytes, out[i] = stream category seed prepared i.val)
    (offset rows cols count : Nat) (within : offset + rows * count ≤ nbytes)
    (enough : cols ≤ 8 * count) :
    (sampleRows (advance (finiteReader (count := nbytes) (fun j => out[j])) offset) cols count enough rows).value =
      (sampleRows (advance (reader category seed prepared) offset) cols count enough rows).value := by
  funext i j
  rw [ByteSampling.sampleRows_coordinate, ByteSampling.sampleRows_coordinate]
  have hb := rowByte_lt i.isLt j.isLt enough
  have hi : offset + i.val * count + j.val / 8 < nbytes := by omega
  change ((finiteReader (count := nbytes) (fun j => out[j])).stream (0 + offset + i.val * count + j.val / 8)).val.testBit _ = _
  simp only [Nat.zero_add, finiteReader, dif_pos hi, Fin.getElem_fin, advance, reader]
  have he := ho ⟨offset + i.val * count + j.val / 8, hi⟩
  exact congrArg (fun byte : Byte => byte.val.testBit (j.val % 8)) he

/-- The matrix loop agrees for a successful finite request covering all its
column calls. The source's row-wise prose is not substituted for the code. -/
theorem expandHColumns_from_run (category : Category) (variant : Grinding) (size : BlockSize)
    (seed : Bits (width category)) (nbytes : Nat) (out : Vector Byte nbytes)
    (hr : run category variant size seed none none nbytes = some out)
    (rows cols count : Nat) (within : cols * count ≤ nbytes) (enough : rows ≤ 8 * count) :
    (expandHColumns (finiteReader (count := nbytes) (fun j => out[j])).stream rows cols count enough).value =
      (expandHColumns (stream category seed (fun _ => false)) rows cols count enough).value := by
  have ho := PRG.run_output_coordinate category variant size seed none none nbytes out
    (fun _ => false) rfl hr
  have he := sampleRows_prefix category seed (fun _ => false) nbytes out ho 0 cols rows count
    (by simpa only [Nat.zero_add] using within) enough
  simpa only [expandHColumns, advance, finiteReader, reader, Nat.zero_add] using congrArg Matrix.transpose he

theorem sampleBinary_from_run (category : Category) (variant : Grinding) (size : BlockSize)
    (seed : Bits (width category)) (salt : Option (Bits (width category))) (tweak : Option Byte)
    (nbytes : Nat) (out : Vector Byte nbytes) (prepared : Bits (width category))
    (hp : prepareSalt category variant salt tweak = some prepared)
    (hr : run category variant size seed salt tweak nbytes = some out)
    (offset n count : Nat) (within : offset + count ≤ nbytes) (enough : n ≤ 8 * count) :
    (sampleBinary (advance (finiteReader (count := nbytes) (fun j => out[j])) offset) n count enough).value =
      (sampleBinary (advance (reader category seed prepared) offset) n count enough).value :=
  sampleBinary_prefix category seed prepared nbytes out
    (PRG.run_output_coordinate category variant size seed salt tweak nbytes out prepared hp hr)
    offset n count within enough

theorem fieldSample_from_run (category : Category) (order : Spec.FieldBytes.ByteOrder category)
    (variant : Grinding) (size : BlockSize) (seed : Bits (width category))
    (salt : Option (Bits (width category))) (tweak : Option Byte)
    (nbytes : Nat) (out : Vector Byte nbytes) (prepared : Bits (width category))
    (hp : prepareSalt category variant salt tweak = some prepared)
    (hr : run category variant size seed salt tweak nbytes = some out)
    (offset n count : Nat) (within : offset + count ≤ nbytes)
    (enough : n * Spec.FieldBytes.byteCount category ≤ count) :
    (Spec.FieldBytes.sample category order (advance (finiteReader (count := nbytes) (fun j => out[j])) offset) n count enough).value =
      (Spec.FieldBytes.sample category order (advance (reader category seed prepared) offset) n count enough).value :=
  fieldSample_prefix category order seed prepared nbytes out
    (PRG.run_output_coordinate category variant size seed salt tweak nbytes out prepared hp hr)
    offset n count within enough

end SDitH.Proofs.PRGSampling
